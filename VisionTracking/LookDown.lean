import VisionTracking.Master
import VisionTracking.AxisAngle
import VisionTracking.SteadyFormation

/-!
# Looking down from above: free tilt and forced loss

A camera on a pitch hinge with `η ≥ hingeLo` points at most `π/2 - hingeLo` away from
the thrust axis, whatever the yaw. So a target seen at angle `θ` from straight up forces
the tilt `angle b₃ up ≥ θ - (π/2 - hingeLo) - α`.

* `tilt_ge_of_visible_below`: a target at least `h` below the drone and within range `D`
  forces the tilt `≥ arcsin (h/D) + hingeLo - α`.
* `steady_look_down_iff`: following a straight level target at speed `v`, a depression `e`
  can be held forever iff `e ≤ chaseTilt v + α - hingeLo` (and the hinge's upper side).
* `forced_loss_time`: if the thrust axis stays in the vertical plane of the track, the
  required tilt is never balanced by drag, and the drone's relative speed stays below `U`,
  the target is lost within an explicit time.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {Q : QuadParams} {C : CameraParams} {δ : ℝ}

/-- The camera is at angle `π/2 - η` from the thrust axis. -/
theorem QuadTraj.angle_b₃_cam (d : QuadTraj Q C δ) (k : ℕ) :
    angle (d.b₃ k) (d.cam k) = π / 2 - d.η k := by
  have h1 := d.b₁_unit k
  have h3 := d.b₃_unit k
  have h13 := d.b₁₃_orth k
  have hc : ‖d.cam k‖ = 1 := norm_cos_smul_add_sin_smul h1 h3 h13 (d.η k)
  have hin : ⟪d.b₃ k, d.cam k⟫ = Real.sin (d.η k) := by
    have e3 : ⟪d.b₃ k, d.b₃ k⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h3]; norm_num
    have e31 : ⟪d.b₃ k, d.b₁ k⟫ = 0 := by rw [real_inner_comm]; exact h13
    simp only [QuadTraj.cam, frameCam, inner_add_right, real_inner_smul_right, e3, e31]
    ring
  have hlo := C.hingeLo_ge
  have hhi := C.hingeHi_le
  have hge := d.hinge_ge k
  have hle := d.hinge_le k
  rw [angle, hin, h3, hc, mul_one, div_one, ← Real.cos_pi_div_two_sub,
    Real.arccos_cos (by linarith) (by linarith)]

/-- **Yaw-free look-down bound.** Whatever the yaw, seeing a target at angle `θ` from
straight up costs tilt `θ - (π/2 - hingeLo) - α`. -/
theorem QuadTraj.tilt_ge_of_visible (d : QuadTraj Q C δ) (k : ℕ) {s : ℝ} {p : E3}
    (hvis : Visible C s (d.x k) (d.cam k) p) :
    angle (p - d.x k) up - (π / 2 - C.hingeLo + C.halfFov) ≤ angle (d.b₃ k) up := by
  have t1 := angle_le_angle_add_angle (p - d.x k) (d.cam k) up
  have t2 := angle_le_angle_add_angle (d.cam k) (d.b₃ k) up
  have h1 : angle (p - d.x k) (d.cam k) ≤ C.halfFov := by rw [angle_comm]; exact hvis.2
  have h2 : angle (d.cam k) (d.b₃ k) ≤ π / 2 - C.hingeLo := by
    rw [angle_comm, d.angle_b₃_cam]; linarith [d.hinge_ge k]
  linarith

/-- A vector at least `h` below the horizon and of length at most `D` is at angle at
least `π/2 + arcsin (h/D)` from straight up. -/
theorem angle_up_ge_of_below {L : E3} {h D : ℝ} (hh : 0 ≤ h) (hD : 0 < D) (hL : ‖L‖ ≤ D)
    (hz : ⟪L, up⟫ ≤ -h) : π / 2 + Real.arcsin (h / D) ≤ angle L up := by
  by_cases h0 : L = 0
  · have : h = 0 := by
      rw [h0, inner_zero_left] at hz; linarith
    subst this; rw [h0]; simp
  have hLpos : 0 < ‖L‖ := norm_pos_iff.2 h0
  rw [angle, norm_up, mul_one]
  have hx : ⟪L, up⟫ / ‖L‖ ≤ -(h / D) := by
    rw [div_le_iff₀ hLpos]
    have : h / D * ‖L‖ ≤ h := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hD]; exact mul_le_mul_of_nonneg_left hL hh
    linarith
  calc π / 2 + Real.arcsin (h / D) = Real.arccos (-(h / D)) := by
        rw [Real.arccos_neg, Real.arccos_eq_pi_div_two_sub_arcsin]; ring
    _ ≤ Real.arccos (⟪L, up⟫ / ‖L‖) := Real.arccos_le_arccos hx

/-- **Look-down tilt.** A target at least `h` below the drone, seen within detection
range `D`, forces the tilt `≥ arcsin (h/D) + hingeLo - α`. -/
theorem QuadTraj.tilt_ge_of_visible_below (d : QuadTraj Q C δ) (k : ℕ) {s h : ℝ} {p : E3}
    (hs : 0 < C.detectRange s) (hh : 0 ≤ h)
    (hvis : Visible C s (d.x k) (d.cam k) p) (hz : ⟪p - d.x k, up⟫ ≤ -h) :
    Real.arcsin (h / C.detectRange s) + C.hingeLo - C.halfFov ≤ angle (d.b₃ k) up := by
  have h1 := d.tilt_ge_of_visible k hvis
  have h2 := angle_up_ge_of_below hh hs hvis.1 hz
  linarith

/-- **Free tilt from drag.** Following a straight level target at speed `v` from above,
a line of sight at depression `e` (the target below and ahead) can be held forever iff
`e ≤ chaseTilt v + α - hingeLo`, together with the hinge's upper side. This is
`steady_formation_iff` at elevation `-e`. -/
theorem steady_look_down_iff {P : TargetParams} (hkn : Q.normalDrag = 0) (hδ : 0 < δ) (p₀ w : E3) (hw : ‖w‖ = 1)
    (hwu : ⟪w, up⟫ = 0) {v : ℝ} (hv : v ∈ Set.Icc P.vMin P.vMax) {e r : ℝ} (hr : 0 < r)
    (hrange : r ≤ C.detectRange P.size)
    (hsum : |chaseTilt Q v - e| ≤ π / 2)
    (hthrust : Q.mass * (Q.g * √(1 + (Q.drag * v ^ 2 / Q.g) ^ 2)) ≤ 4 * Q.fMotor)
    (htilt : chaseTilt Q v ≤ Q.tiltMax) (henv : v ≤ Q.speedEnv) :
    (∃ d : QuadTraj Q C δ, (∀ k, d.v k = v • w) ∧
        (∀ k, (levelTarget P hδ.le p₀ w hw hwu v hv).p k - d.x k =
          r • (Real.cos e • w - Real.sin e • up)) ∧
        KeepsInView C P.size d (levelTarget P hδ.le p₀ w hw hwu v hv)) ↔
      (e ≤ chaseTilt Q v + C.halfFov - C.hingeLo ∧
        chaseTilt Q v - C.hingeHi - C.halfFov ≤ e) := by
  have key := steady_formation_iff (Q := Q) (C := C) hkn hδ p₀ w hw hwu hv (el := -e) hr hrange
    (by rwa [← sub_eq_add_neg]) hthrust htilt henv
  have hlos : Real.cos (-e) • w + Real.sin (-e) • up = Real.cos e • w - Real.sin e • up := by
    rw [Real.cos_neg, Real.sin_neg, neg_smul, ← sub_eq_add_neg]
  rw [hlos] at key
  rw [key]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-! ## Forced loss for track-aligned drones -/

section Planar

variable {w : E3}

/-- Parseval for the frame `(w, up × w, up)` with `w` a horizontal unit vector. -/
theorem inner_eq_track_coords (hw : ‖w‖ = 1) (hwu : ⟪w, up⟫ = 0) (x y : E3) :
    ⟪x, y⟫ = ⟪x, w⟫ * ⟪y, w⟫ + ⟪x, cross up w⟫ * ⟪y, cross up w⟫ + ⟪x, up⟫ * ⟪y, up⟫ := by
  have h2 : w.ofLp 2 = 0 := by rw [← inner_up]; exact hwu
  have hn : w.ofLp 0 ^ 2 + w.ofLp 1 ^ 2 = 1 := by
    have := real_inner_self_eq_norm_sq w
    rw [hw, inner_eq_coords, h2] at this; nlinarith
  simp only [inner_eq_coords, cross, crossProduct, up, h2]
  simp
  linear_combination -(x.ofLp 0 * y.ofLp 0 + x.ofLp 1 * y.ofLp 1) * hn

/-- Tilt bookkeeping in the track plane: a unit `b` in the plane, tilted by at least `p₀`
and at most `π/2`, has `0 ≤ ⟪b, up⟫ ≤ cos p₀`, `sin p₀ ≤ |⟪b, w⟫|` and
`sin p₀ ⟪b, up⟫ ≤ cos p₀ |⟪b, w⟫|`. -/
theorem planar_tilt (hw : ‖w‖ = 1) (hwu : ⟪w, up⟫ = 0) {b : E3} (hb : ‖b‖ = 1)
    (hpl : ⟪b, cross up w⟫ = 0) {p₀ : ℝ} (hp0 : 0 ≤ p₀) (hlo : p₀ ≤ angle b up)
    (hhi : angle b up ≤ π / 2) :
    0 ≤ ⟪b, up⟫ ∧ ⟪b, up⟫ ≤ Real.cos p₀ ∧ Real.sin p₀ ≤ |⟪b, w⟫| ∧
      Real.sin p₀ * ⟪b, up⟫ ≤ Real.cos p₀ * |⟪b, w⟫| := by
  have hcos : ⟪b, up⟫ = Real.cos (angle b up) := by
    rw [cos_angle, hb, norm_up, mul_one, div_one]
  have hz0 : 0 ≤ ⟪b, up⟫ := by
    rw [hcos]; exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [angle_nonneg b up], hhi⟩
  have hzc : ⟪b, up⟫ ≤ Real.cos p₀ := by
    rw [hcos]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hp0 (angle_le_pi b up) hlo
  have hpar := inner_eq_track_coords hw hwu b b
  rw [real_inner_self_eq_norm_sq, hb, hpl] at hpar
  have hsp0 : 0 ≤ Real.sin p₀ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hp0 (by linarith [angle_le_pi b up])
  have hcp0 : 0 ≤ Real.cos p₀ := hz0.trans hzc
  have hsc := Real.sin_sq_add_cos_sq p₀
  have hbw2 : ⟪b, w⟫ ^ 2 = |⟪b, w⟫| ^ 2 := (sq_abs _).symm
  refine ⟨hz0, hzc, ?_, ?_⟩
  · rw [← sq_le_sq₀ hsp0 (abs_nonneg _)]
    nlinarith [mul_le_mul hzc hzc hz0 hcp0]
  · rw [← sq_le_sq₀ (mul_nonneg hsp0 hz0) (mul_nonneg hcp0 (abs_nonneg _))]
    have := mul_le_mul hzc hzc hz0 hcp0
    nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg (Real.sin p₀))]

/-- Two thrust axes in the track plane tilted to opposite sides by at least `p₀` are at
least `2 p₀` apart. -/
theorem angle_ge_of_opposite (hw : ‖w‖ = 1) (hwu : ⟪w, up⟫ = 0) {b b' : E3}
    (hb : ‖b‖ = 1) (hb' : ‖b'‖ = 1) (hpl : ⟪b, cross up w⟫ = 0)
    (hpl' : ⟪b', cross up w⟫ = 0) {p₀ : ℝ} (hp0 : 0 ≤ p₀) (hp1 : p₀ < π / 2)
    (hlo : p₀ ≤ angle b up) (hhi : angle b up ≤ π / 2)
    (hlo' : p₀ ≤ angle b' up) (hhi' : angle b' up ≤ π / 2)
    (hopp : ⟪b, w⟫ * ⟪b', w⟫ ≤ 0) : 2 * p₀ ≤ angle b b' := by
  obtain ⟨z0, zc, sw, -⟩ := planar_tilt hw hwu hb hpl hp0 hlo hhi
  obtain ⟨z0', zc', sw', -⟩ := planar_tilt hw hwu hb' hpl' hp0 hlo' hhi'
  have hpar := inner_eq_track_coords hw hwu b b'
  rw [hpl, zero_mul, add_zero] at hpar
  have hsp0 : 0 ≤ Real.sin p₀ := Real.sin_nonneg_of_nonneg_of_le_pi hp0 (by linarith)
  have hprod : Real.sin p₀ * Real.sin p₀ ≤ |⟪b, w⟫ * ⟪b', w⟫| := by
    rw [abs_mul]; exact mul_le_mul sw sw' hsp0 (abs_nonneg _)
  have hneg : ⟪b, w⟫ * ⟪b', w⟫ = -|⟪b, w⟫ * ⟪b', w⟫| := by
    rw [abs_of_nonpos hopp]; ring
  have hzz : ⟪b, up⟫ * ⟪b', up⟫ ≤ Real.cos p₀ * Real.cos p₀ :=
    mul_le_mul zc zc' z0' (z0.trans zc)
  have hin : ⟪b, b'⟫ ≤ Real.cos (2 * p₀) := by
    rw [Real.cos_two_mul, hpar]; nlinarith [Real.sin_sq_add_cos_sq p₀]
  rw [angle, hb, hb', mul_one, div_one]
  calc 2 * p₀ = Real.arccos (Real.cos (2 * p₀)) :=
        (Real.arccos_cos (by linarith) (by linarith)).symm
    _ ≤ Real.arccos ⟪b, b'⟫ := Real.arccos_le_arccos hin

end Planar

/-- One control step turns the thrust axis by at most `δ · rateMax`. -/
theorem QuadTraj.angle_b₃_step_le (d : QuadTraj Q C δ) (hδ : 0 ≤ δ) (k : ℕ)
    (hπ : δ * Q.rateMax ≤ π) : angle (d.b₃ (k + 1)) (d.b₃ k) ≤ δ * Q.rateMax := by
  have hW : worldRate (d.b₁ k) (d.b₂ k) (d.b₃ k) (d.Ω k) = ofF (d.b₁ k) (d.b₂ k) (d.Ω k) := by
    rw [d.b₃_cross k]; rfl
  have hn : ‖δ • worldRate (d.b₁ k) (d.b₂ k) (d.b₃ k) (d.Ω k)‖ ≤ δ * Q.rateMax := by
    rw [hW, norm_smul, Real.norm_of_nonneg hδ, norm_ofF (d.b₁_unit k) (d.b₂_unit k)
      (d.b₁₂_orth k)]
    exact mul_le_mul_of_nonneg_left (d.rate_le k) hδ
  have h0 : d.b₃ k ≠ 0 := by
    intro h; have := d.b₃_unit k; rw [h, norm_zero] at this; norm_num at this
  rw [(d.attitude k).2.2]
  exact (angle_rotate_le _ _ h0 (hn.trans hπ)).trans hn

/-- **Forced loss of a target below.** Suppose a drone keeps targets `p k` in view for
`k ≤ N` while
* each target is at least `h` below it, so the tilt must be at least
  `p₀ ≤ arcsin (h/D) + hingeLo - α` (`D` the detection range);
* its thrust axis stays in the vertical plane of a horizontal direction `w` (no orbiting or
  weaving), and one step cannot flip the tilt across vertical (`δ · rateMax < 2 p₀`);
* its velocity stays within `U` of the reference `vT • w`.

The required tilt then pushes it along `w` faster than drag can balance: with
`κ = sin p₀ (g - c V U) - c V² cos p₀` (`V = vT + U`) positive, the time in view is at most

  `N δ ≤ 2 U (cos p₀ + sin p₀) / κ`. -/
theorem QuadTraj.forced_loss_time (hkn : Q.normalDrag = 0) (d : QuadTraj Q C δ) (hδ : 0 < δ) {w : E3} (hw : ‖w‖ = 1)
    (hwu : ⟪w, up⟫ = 0) {p : ℕ → E3} {s h p₀ vT U : ℝ} {N : ℕ}
    (hs : 0 < C.detectRange s) (hh : 0 ≤ h) (hvT : 0 ≤ vT) (hU0 : 0 ≤ U)
    (hp0pos : 0 < p₀) (hp0 : p₀ ≤ Real.arcsin (h / C.detectRange s) + C.hingeLo - C.halfFov)
    (hrate : δ * Q.rateMax < 2 * p₀)
    (hvis : ∀ k ≤ N, Visible C s (d.x k) (d.cam k) (p k))
    (hbelow : ∀ k ≤ N, ⟪p k - d.x k, up⟫ ≤ -h)
    (hplanar : ∀ k ≤ N, ⟪d.b₃ k, cross up w⟫ = 0)
    (hU : ∀ k ≤ N, ‖d.v k - vT • w‖ ≤ U)
    (hκ : 0 < Real.sin p₀ * (Q.g - Q.drag * (vT + U) * U)
      - Q.drag * (vT + U) ^ 2 * Real.cos p₀) :
    N * δ ≤ 2 * U * (Real.cos p₀ + Real.sin p₀) /
      (Real.sin p₀ * (Q.g - Q.drag * (vT + U) * U) - Q.drag * (vT + U) ^ 2 * Real.cos p₀) := by
  set κ := Real.sin p₀ * (Q.g - Q.drag * (vT + U) * U) - Q.drag * (vT + U) ^ 2 * Real.cos p₀
    with hκdef
  set V := vT + U with hVdef
  have hup1 : ⟪up, up⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_up]; norm_num
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have huw : ⟪up, w⟫ = 0 := by rw [real_inner_comm]; exact hwu
  -- tilt bounds at every visible step
  have htilt : ∀ k ≤ N, p₀ ≤ angle (d.b₃ k) up := fun k hk =>
    hp0.trans (d.tilt_ge_of_visible_below k hs hh (hvis k hk) (hbelow k hk))
  have hhalf : ∀ k, angle (d.b₃ k) up ≤ π / 2 := fun k =>
    (d.tilt_le k).trans Q.tiltMax_lt.le
  have hp1 : p₀ < π / 2 := (htilt 0 (Nat.zero_le _)).trans_lt
    ((d.tilt_le 0).trans_lt Q.tiltMax_lt)
  have hb := fun k hk => planar_tilt hw hwu (d.b₃_unit k) (hplanar k hk) hp0pos.le
    (htilt k hk) (hhalf k)
  have hsp : 0 < Real.sin p₀ := Real.sin_pos_of_pos_of_lt_pi hp0pos (by linarith)
  have hcp : 0 < Real.cos p₀ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hp1⟩
  -- the tilt never flips side
  have hsame : ∀ k ≤ N, 0 < ⟪d.b₃ 0, w⟫ * ⟪d.b₃ k, w⟫ := by
    intro k
    induction k with
    | zero =>
      intro _
      have := (hb 0 (Nat.zero_le _)).2.2.1
      have h0 : 0 < |⟪d.b₃ 0, w⟫| := hsp.trans_le this
      nlinarith [abs_mul_abs_self ⟪d.b₃ 0, w⟫]
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 : 0 < ⟪d.b₃ k, w⟫ * ⟪d.b₃ (k + 1), w⟫ := by
        by_contra hneg
        have hang := angle_ge_of_opposite hw hwu (d.b₃_unit k) (d.b₃_unit (k + 1))
          (hplanar k (by omega)) (hplanar (k + 1) hk) hp0pos.le hp1 (htilt k (by omega))
          (hhalf k) (htilt (k + 1) hk) (hhalf (k + 1)) (not_lt.1 hneg)
        have hstep := d.angle_b₃_step_le hδ.le k (by linarith)
        rw [angle_comm] at hstep
        linarith
      by_contra hneg
      have := mul_pos h1 h2
      nlinarith [sq_nonneg ⟪d.b₃ k, w⟫]
  -- a fixed side `σ`
  obtain ⟨σ, hσ, hσabs⟩ : ∃ σ : ℝ, |σ| = 1 ∧ ∀ k ≤ N, |⟪d.b₃ k, w⟫| = σ * ⟪d.b₃ k, w⟫ := by
    rcases lt_or_gt_of_ne (show ⟪d.b₃ 0, w⟫ ≠ 0 by
      have := hsame 0 (Nat.zero_le _); intro h0; rw [h0, zero_mul] at this; exact lt_irrefl _ this)
      with hneg | hpos
    · refine ⟨-1, by norm_num, fun k hk => ?_⟩
      have := hsame k hk
      have : ⟪d.b₃ k, w⟫ < 0 := by nlinarith
      rw [abs_of_neg this]; ring
    · refine ⟨1, by norm_num, fun k hk => ?_⟩
      have := hsame k hk
      have : 0 < ⟪d.b₃ k, w⟫ := by nlinarith
      rw [abs_of_pos this]; ring
  -- velocity bounds
  have hcomp : ∀ k ≤ N, |⟪d.v k, w⟫ - vT| ≤ U ∧ |⟪d.v k, up⟫| ≤ U ∧ ‖d.v k‖ ≤ V := by
    intro k hk
    have h1 := hU k hk
    refine ⟨?_, ?_, ?_⟩
    · have := abs_real_inner_le_norm (d.v k - vT • w) w
      rw [hw, mul_one, inner_sub_left, real_inner_smul_left, hww, mul_one] at this
      linarith
    · have := abs_real_inner_le_norm (d.v k - vT • w) up
      rw [norm_up, mul_one, inner_sub_left, real_inner_smul_left, hwu, mul_zero,
        sub_zero] at this
      linarith
    · have := norm_le_insert' (d.v k) (vT • w)
      rw [norm_smul, hw, Real.norm_of_nonneg hvT, mul_one] at this
      linarith
  -- one step
  have hstep : ∀ k < N, δ * κ ≤ Real.cos p₀ * (σ * (⟪d.v (k + 1), w⟫ - ⟪d.v k, w⟫))
      - Real.sin p₀ * (⟪d.v (k + 1), up⟫ - ⟪d.v k, up⟫) := by
    intro k hk
    set A := totalThrust (d.f k) / Q.mass
    set nv := ‖d.v k‖
    set B := ⟪d.b₃ k, w⟫
    set Z := ⟪d.b₃ k, up⟫
    set u := ⟪d.v k, w⟫
    set z := ⟪d.v k, up⟫
    have hA : 0 ≤ A := d.thrust_nonneg k
    have hu' : ⟪d.v (k + 1), w⟫ = u + δ * (A * B - Q.drag * nv * u) := by
      rw [d.translational k, hkn, zero_mul, zero_mul, sub_zero]
      simp only [inner_add_left, inner_sub_left, real_inner_smul_left, huw]
      ring
    have hz' : ⟪d.v (k + 1), up⟫ = z + δ * (A * Z - Q.g - Q.drag * nv * z) := by
      rw [d.translational k, hkn, zero_mul, zero_mul, sub_zero]
      simp only [inner_add_left, inner_sub_left, real_inner_smul_left, hup1]
      ring
    obtain ⟨-, -, -, hsz⟩ := hb k hk.le
    rw [hσabs k hk.le] at hsz
    obtain ⟨hu1, hz1, hn1⟩ := hcomp k hk.le
    have hc := Q.drag_pos.le
    have hnv0 : 0 ≤ nv := norm_nonneg _
    have hσu : σ * u ≤ nv := by
      have h1 := abs_real_inner_le_norm (d.v k) w
      rw [hw, mul_one] at h1
      have : |σ * u| ≤ nv := by rw [abs_mul, hσ, one_mul]; exact h1
      exact (le_abs_self _).trans this
    have t1 : 0 ≤ A * (Real.cos p₀ * (σ * B) - Real.sin p₀ * Z) :=
      mul_nonneg hA (by linarith)
    have t2 : Q.drag * Real.cos p₀ * (nv * (σ * u)) ≤ Q.drag * Real.cos p₀ * V ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc hcp.le)
      have : nv * (σ * u) ≤ nv * nv := mul_le_mul_of_nonneg_left hσu hnv0
      nlinarith [mul_le_mul hn1 hn1 hnv0 (hnv0.trans hn1)]
    have t3 : -(V * U) ≤ nv * z := by
      have : |nv * z| ≤ V * U := by
        rw [abs_mul, abs_of_nonneg hnv0]; exact mul_le_mul hn1 hz1 (abs_nonneg _) (by linarith)
      linarith [neg_abs_le (nv * z)]
    have t3' := mul_le_mul_of_nonneg_left t3 (mul_nonneg hsp.le hc)
    have e : Real.cos p₀ * (σ * ((u + δ * (A * B - Q.drag * nv * u)) - u))
        - Real.sin p₀ * ((z + δ * (A * Z - Q.g - Q.drag * nv * z)) - z)
        = δ * (A * (Real.cos p₀ * (σ * B) - Real.sin p₀ * Z)
          - Q.drag * Real.cos p₀ * (nv * (σ * u)) + Real.sin p₀ * Q.g
          + Real.sin p₀ * Q.drag * (nv * z)) := by ring
    rw [hu', hz', e]
    apply mul_le_mul_of_nonneg_left _ hδ.le
    have hk : κ = Real.sin p₀ * Q.g - Real.sin p₀ * Q.drag * (V * U)
        - Q.drag * Real.cos p₀ * V ^ 2 := by rw [hκdef]; ring
    rw [hk]
    linarith
  -- telescoping
  have htel : ∀ n ≤ N, (n : ℝ) * (δ * κ) ≤ Real.cos p₀ * (σ * (⟪d.v n, w⟫ - ⟪d.v 0, w⟫))
      - Real.sin p₀ * (⟪d.v n, up⟫ - ⟪d.v 0, up⟫) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := hstep n (by omega)
      push_cast
      linarith
  have hfin := htel N le_rfl
  obtain ⟨hu0, hz0, -⟩ := hcomp 0 (Nat.zero_le _)
  obtain ⟨huN, hzN, -⟩ := hcomp N le_rfl
  have hσd : σ * (⟪d.v N, w⟫ - ⟪d.v 0, w⟫) ≤ 2 * U := by
    have : |σ * (⟪d.v N, w⟫ - ⟪d.v 0, w⟫)| ≤ 2 * U := by
      rw [abs_mul, hσ, one_mul]
      have := abs_sub (⟪d.v N, w⟫ - vT) (⟪d.v 0, w⟫ - vT)
      rw [sub_sub_sub_cancel_right] at this
      linarith
    exact (le_abs_self _).trans this
  have hzd : -(2 * U) ≤ ⟪d.v N, up⟫ - ⟪d.v 0, up⟫ := by
    have := abs_sub (⟪d.v N, up⟫) (⟪d.v 0, up⟫)
    linarith [neg_abs_le (⟪d.v N, up⟫ - ⟪d.v 0, up⟫)]
  rw [le_div_iff₀ hκ]
  have a1 := mul_le_mul_of_nonneg_left hσd hcp.le
  have a2 := mul_le_mul_of_nonneg_left hzd hsp.le
  linarith

end VisionTracking
import VisionTracking.SteadyChase
import VisionTracking.Motors
import VisionTracking.Rotation

/-!
# Steady formation: an exact characterization on the full quadrotor

Against a target flying straight and level at speed `v`, consider holding a fixed
offset: the target seen at elevation `el` (in the plane of travel) and range `r`.
`steady_formation_iff` proves that a valid rigid-body quadrotor trajectory (four
motors in range, right-handed orthonormal body frame, body rates within limits,
hinge in range) doing this and keeping the target in view **exists iff**
`lo - α ≤ θ(v) + el ≤ hi + α`, where `θ(v) = arctan (c_D v² / g)`. This assumes
the quad can produce the steady thrust `√(g² + (c_D v²)²)` with its four motors,
within its tilt envelope and drag-model envelope.

* `→` is `steady_chase_window` and holds for any trajectory with that velocity.
* `←` builds the trajectory explicitly: constant velocity, thrust axis on the steady
  axis, `b₁` chosen in the rotor plane towards the line of sight, `b₂ = b₃ × b₁`,
  zero body rates, four equal motor thrusts, and the hinge clamped to the
  elevation.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {P : TargetParams} {Q : QuadParams} {C : CameraParams} {δ : ℝ}

/-- The level target flying straight at speed `v` along the horizontal unit vector
`w`. -/
noncomputable def levelTarget (P : TargetParams) {δ : ℝ} (hδ : 0 ≤ δ) (p₀ w : E3)
    (hw : ‖w‖ = 1) (hwu : ⟪w, up⟫ = 0) (v : ℝ) (hv : v ∈ Set.Icc P.vMin P.vMax) :
    TargetTraj P δ where
  p k := p₀ + ((k : ℝ) * δ * v) • w
  v _ := v • w
  steps k := by push_cast; module
  speed_ge _ := by
    rw [norm_smul, hw, Real.norm_of_nonneg (P.vMin_pos.le.trans hv.1), mul_one]; exact hv.1
  speed_le _ := by
    rw [norm_smul, hw, Real.norm_of_nonneg (P.vMin_pos.le.trans hv.1), mul_one]; exact hv.2
  tangential _ := by
    simp only [sub_self, inner_zero_left, abs_zero]
    have := P.aTan_nonneg
    have := P.vMin_pos.le.trans hv.1
    positivity
  normal _ := by
    simp only [sub_self, inner_zero_left, zero_div, zero_smul, norm_zero]
    have := P.turnRadius_pos
    positivity
  jerk_le _ := by
    simp only [sub_self, norm_zero]
    have := P.jerk_nonneg
    positivity
  vert_le _ := by
    simp only [sub_self, inner_zero_left, abs_zero]
    have := P.aVert_nonneg
    positivity
  snap_le _ := by
    have h0 : ∀ x : E3, x - 3 • x + 3 • x - x = 0 := fun x => by module
    rw [h0, norm_zero]
    have := P.snap_nonneg
    positivity
  climb_le _ := by
    rw [real_inner_smul_left, hwu, mul_zero, abs_zero]
    exact mul_nonneg (norm_nonneg _)
      (Real.sin_nonneg_of_nonneg_of_le_pi P.climbMax_nonneg
        (by linarith [P.climbMax_lt, Real.pi_pos]))

/-- The steady thrust identity: `g √(1 + x²) · steadyAxis θ(v) w = g e₃ + c_D ‖v w‖ (v w)`. -/
theorem steady_thrust {w : E3} (hw : ‖w‖ = 1) {v : ℝ} (hv : 0 < v) :
    (Q.g * √(1 + (Q.drag * v ^ 2 / Q.g) ^ 2)) • steadyAxis (chaseTilt Q v) w
      = Q.g • up + (Q.drag * ‖v • w‖) • (v • w) := by
  set x := Q.drag * v ^ 2 / Q.g with hx
  have hsq : 0 < √(1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hg := Q.g_pos.ne'
  rw [steadyAxis, chaseTilt, ← hx, Real.cos_arctan, Real.sin_arctan, smul_add, smul_smul,
    smul_smul, norm_smul, hw, Real.norm_of_nonneg hv.le, mul_one, smul_smul]
  congr 1
  · congr 1; field_simp
  · congr 1; rw [hx]; field_simp

/-- `a × (b × a) = b` for orthonormal `a, b`. -/
theorem cross_cross_self {a b : E3} (ha : ‖a‖ = 1) (hab : ⟪a, b⟫ = 0) :
    cross a (cross b a) = b := by
  have ha2 : (a.ofLp 0) ^ 2 + (a.ofLp 1) ^ 2 + (a.ofLp 2) ^ 2 = 1 := by
    have := norm_sq_coords a; rw [ha] at this; linarith
  have hab' : a.ofLp 0 * b.ofLp 0 + a.ofLp 1 * b.ofLp 1 + a.ofLp 2 * b.ofLp 2 = 0 := by
    rw [← inner_eq_coords]; exact hab
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two]
    linear_combination (b.ofLp 0) * ha2 - (a.ofLp 0) * hab'
  · simp only [Fin.mk_one, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two]
    linear_combination (b.ofLp 1) * ha2 - (a.ofLp 1) * hab'
  · simp only [Fin.reduceFinMk, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two]
    linear_combination (b.ofLp 2) * ha2 - (a.ofLp 2) * hab'

/-- Given a unit `b₃` and any unit `z ⟂ b₃`, there is a unit `b₁ ⟂ b₃` aligned with the
rotor-plane part of the unit vector `u`. -/
theorem exists_aligned {b₃ u z : E3} (h₃ : ‖b₃‖ = 1) (hu : ‖u‖ = 1) (hz : ‖z‖ = 1)
    (hzb : ⟪z, b₃⟫ = 0) :
    ∃ b₁ : E3, ‖b₁‖ = 1 ∧ ⟪b₁, b₃⟫ = 0 ∧ ⟪b₁, u⟫ = √(1 - ⟪b₃, u⟫ ^ 2) := by
  set s := ⟪b₃, u⟫ with hs
  have hb₃b₃ : ⟪b₃, b₃⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h₃]; norm_num
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  set rr := u - s • b₃ with hr
  have hrb : ⟪rr, b₃⟫ = 0 := by
    rw [hr, inner_sub_left, real_inner_smul_left, hb₃b₃, hs, real_inner_comm]; ring
  have hrr : ‖rr‖ ^ 2 = 1 - s ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hr]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hb₃b₃, huu]
    rw [real_inner_comm b₃ u, ← hs]; ring
  by_cases hr0 : rr = 0
  · refine ⟨z, hz, hzb, ?_⟩
    have hs1 : 1 - s ^ 2 = 0 := by rw [← hrr, hr0, norm_zero]; norm_num
    have hu' : u = s • b₃ := by rw [← sub_eq_zero, ← hr, hr0]
    rw [hs1, Real.sqrt_zero, hu', real_inner_smul_right, hzb, mul_zero]
  · have hrpos : 0 < ‖rr‖ := norm_pos_iff.2 hr0
    refine ⟨‖rr‖⁻¹ • rr, norm_smul_inv_norm hr0, by rw [real_inner_smul_left, hrb, mul_zero], ?_⟩
    have hur : ⟪rr, u⟫ = ‖rr‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      conv_rhs => rw [hr]
      rw [inner_sub_right, real_inner_smul_right, hrb, mul_zero, sub_zero]
    rw [real_inner_smul_left, hur, ← hrr, Real.sqrt_sq hrpos.le]
    field_simp

/-- **Steady formation, exact characterization.** -/
theorem steady_formation_iff (hδ : 0 < δ) (p₀ w : E3) (hw : ‖w‖ = 1) (hwu : ⟪w, up⟫ = 0)
    {v : ℝ} (hv : v ∈ Set.Icc P.vMin P.vMax) {el r : ℝ} (hr : 0 < r)
    (hrange : r ≤ C.detectRange P.size)
    (hsum : |chaseTilt Q v + el| ≤ π / 2)
    (hthrust : Q.mass * (Q.g * √(1 + (Q.drag * v ^ 2 / Q.g) ^ 2)) ≤ 4 * Q.fMotor)
    (htilt : chaseTilt Q v ≤ Q.tiltMax) (henv : v ≤ Q.speedEnv) :
    (∃ d : QuadTraj Q C δ, (∀ k, d.v k = v • w) ∧
        (∀ k, (levelTarget P hδ.le p₀ w hw hwu v hv).p k - d.x k =
          r • (Real.cos el • w + Real.sin el • up)) ∧
        KeepsInView C P.size d (levelTarget P hδ.le p₀ w hw hwu v hv)) ↔
      (C.hingeLo - C.halfFov ≤ chaseTilt Q v + el ∧
        chaseTilt Q v + el ≤ C.hingeHi + C.halfFov) := by
  have hv0 : 0 < v := P.vMin_pos.trans_le hv.1
  have hvw : ‖v • w‖ = v := by rw [norm_smul, hw, Real.norm_of_nonneg hv0.le, mul_one]
  have hvw0 : v • w ≠ 0 := by
    intro h; have := congrArg norm h; rw [hvw, norm_zero] at this; linarith
  have hwnorm : ‖v • w‖⁻¹ • (v • w) = w := by
    rw [hvw, smul_smul, inv_mul_cancel₀ hv0.ne', one_smul]
  constructor
  · rintro ⟨d, hdv, hlos, hkeep⟩
    have h := steady_chase_window d hδ.ne' 0 (by rw [hdv, hdv]) (by
        rw [hdv, real_inner_smul_left, hwu, mul_zero]) (by rw [hdv]; exact hvw0)
      (hkeep 0) hr (el := el) (by rw [hlos 0, hdv 0, hwnorm]) (by rw [hdv 0, hvw]; exact hsum)
    rwa [hdv 0, hvw] at h
  · rintro ⟨hw1, hw2⟩
    -- Geometry of the steady attitude.
    set θ := chaseTilt Q v with hθ
    set b₃ := steadyAxis θ w with hb₃
    set u := Real.cos el • w + Real.sin el • up with hu
    have hb₃n : ‖b₃‖ = 1 := norm_steadyAxis hw hwu
    have hun : ‖u‖ = 1 := norm_cos_smul_add_sin_smul hw norm_up hwu el
    have hupup : ⟪up, up⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_up]; norm_num
    have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
    have huw : ⟪up, w⟫ = 0 := by rw [real_inner_comm]; exact hwu
    have helev : Real.arcsin ⟪b₃, u⟫ = θ + el := by
      rw [hb₃, inner_steadyAxis, hu, inner_add_right, inner_add_right, real_inner_smul_right,
        real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, hupup, hww, huw,
        hwu]
      have : Real.cos θ * (Real.cos el * 0 + Real.sin el * 1) +
          Real.sin θ * (Real.cos el * 1 + Real.sin el * 0) = Real.sin (θ + el) := by
        rw [Real.sin_add]; ring
      rw [this, Real.arcsin_sin (abs_le.1 hsum).1 (abs_le.1 hsum).2]
    -- A unit vector orthogonal to `b₃`, then the aligned forward axis.
    set z := Real.cos θ • w - Real.sin θ • up with hz
    have hzn : ‖z‖ = 1 := by
      have := norm_cos_smul_add_sin_smul (η := -θ) hw norm_up hwu
      rwa [Real.cos_neg, Real.sin_neg, neg_smul, ← sub_eq_add_neg] at this
    have hzb : ⟪z, b₃⟫ = 0 := by
      simp only [hz, hb₃, steadyAxis, inner_sub_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hupup, hww, huw, hwu]
      ring
    obtain ⟨b₁, hb₁n, hb₁₃, hal⟩ := exists_aligned hb₃n hun hzn hzb
    set b₂ := cross b₃ b₁ with hb₂
    have hb₃₁ : ⟪b₃, b₁⟫ = 0 := by rw [real_inner_comm]; exact hb₁₃
    have hb₂n : ‖b₂‖ = 1 := norm_cross_of_orthonormal hb₃n hb₁n hb₃₁
    have hb₁₂ : ⟪b₁, b₂⟫ = 0 := inner_cross_right _ _
    have hcross : b₃ = cross b₁ b₂ := (cross_cross_self hb₁n hb₁₃).symm
    -- The hinge, clamped to the elevation.
    set η := max C.hingeLo (min C.hingeHi (θ + el)) with hηdef
    have hηI : η ∈ Set.Icc C.hingeLo C.hingeHi :=
      ⟨le_max_left _ _, max_le C.hingeLo_le (min_le_left _ _)⟩
    have hηpi : η ∈ Set.Icc (-(π / 2)) (π / 2) :=
      ⟨by linarith [hηI.1, C.hingeLo_ge], by linarith [hηI.2, C.hingeHi_le]⟩
    have hcam : angle (frameCam b₁ b₃ η) u ≤ C.halfFov := by
      unfold frameCam
      rw [angle_eq_abs_sub_of_aligned hb₁n hb₃n hb₁₃ hun hal hηpi, helev, abs_le]
      constructor
      · have : min C.hingeHi (θ + el) ≤ η := le_max_right _ _
        rcases min_choice C.hingeHi (θ + el) with h | h <;> rw [h] at this <;>
          linarith [C.halfFov_pos]
      · rcases le_total C.hingeLo (min C.hingeHi (θ + el)) with h | h
        · rw [hηdef, max_eq_right h]; linarith [min_le_right C.hingeHi (θ + el), C.halfFov_pos]
        · rw [hηdef, max_eq_left h]; linarith
    -- Thrust.
    set M := Q.g * √(1 + (Q.drag * v ^ 2 / Q.g) ^ 2) with hM
    have hMpos : 0 < M := mul_pos Q.g_pos (Real.sqrt_pos.2 (by positivity))
    have hthr := steady_thrust (Q := Q) hw hv0
    set T := levelTarget P hδ.le p₀ w hw hwu v hv with hT
    have htilt' : angle b₃ up = θ := by
      have hθ0 := chaseTilt_nonneg Q v
      have hθ1 := chaseTilt_lt Q v
      unfold angle
      rw [hb₃n, norm_up, mul_one, div_one, hb₃, inner_steadyAxis, hupup, hwu, mul_one,
        mul_zero, add_zero, Real.arccos_cos hθ0 (by linarith [Real.pi_pos])]
    refine ⟨{
      x := fun k => T.p k - r • u
      v := fun _ => v • w
      b₁ := fun _ => b₁
      b₂ := fun _ => b₂
      b₃ := fun _ => b₃
      Ω := fun _ => 0
      f := fun _ _ => Q.mass * M / 4
      η := fun _ => η
      steps := fun k => by
        show T.p (k + 1) - r • u = T.p k - r • u + δ • (v • w)
        rw [T.steps k]; simp only [hT, levelTarget]; module
      translational := fun k => by
        have hF : totalThrust (fun _ : Fin 4 => Q.mass * M / 4) / Q.mass = M := by
          have := Q.mass_pos.ne'; unfold totalThrust; field_simp; ring
        rw [hF, hthr]; simp
      rotational := fun k => by
        have h0 : Q.torque (fun _ : Fin 4 => Q.mass * M / 4) = 0 := by
          ext i; fin_cases i <;> simp [QuadParams.torque]
        rw [h0, cross_zero_left]
        ext i; fin_cases i <;> simp [QuadParams.inertiaInv]
      attitude := fun k => by
        have h0 : worldRate b₁ b₂ b₃ 0 = 0 := by simp [worldRate]
        simp only [h0, smul_zero, rotate_zero, and_self]
      b₁_unit := fun _ => hb₁n
      b₂_unit := fun _ => hb₂n
      b₁₂_orth := fun _ => hb₁₂
      b₃_cross := fun _ => hcross
      motor_nonneg := fun _ _ => by have := Q.mass_pos; positivity
      motor_le := fun _ _ => by linarith
      tilt_le := fun _ => by rw [htilt']; exact htilt
      rate_le := fun _ => by rw [norm_zero]; exact Q.rateMax_pos.le
      speed_le := fun _ => by rw [hvw]; exact henv
      hinge_ge := fun _ => hηI.1
      hinge_le := fun _ => hηI.2
      hinge_rate := fun _ => by
        simp only [sub_self, abs_zero]
        exact mul_nonneg hδ.le C.hingeRate_nonneg }, fun _ => rfl, fun k => by simp, ?_⟩
    intro k
    refine ⟨?_, ?_⟩
    · show ‖T.p k - (T.p k - r • u)‖ ≤ C.detectRange P.size
      rw [sub_sub_cancel, norm_smul, hun, Real.norm_of_nonneg hr.le, mul_one]; exact hrange
    · show angle (frameCam b₁ b₃ η) (T.p k - (T.p k - r • u)) ≤ C.halfFov
      rw [sub_sub_cancel, angle_smul_right_of_pos _ _ hr]; exact hcam

end VisionTracking

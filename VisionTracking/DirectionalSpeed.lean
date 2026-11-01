import VisionTracking.Frame
import VisionTracking.SpeedBound

/-!
# Directional speed limits of the rigid-body quadrotor

Along any unit direction `u`, the quad's velocity component is driven by
`F ⟪b₃, u⟫ - g ⟪e₃, u⟫ - c_D ‖v‖ ⟪v, u⟫` with collective thrust `F ∈ [0, 4 f_motor / m]`
and `b₃` inside the tilt envelope. That caps the sustainable speed along `u` at
`dirSpeed u = √(max 0 (push u) / c_D)`, where `push u` is the best net force along `u`.

* Straight down: thrust cannot help, so `push = g` and `dirSpeed = √(g / c_D)`: the
  quad cannot follow a target that sinks faster than its own terminal fall speed.
* Horizontal: `push = F_max sin θ_max`.
* Straight up: `push = F_max - g`.

`not_maintainable_of_dirSpeed_lt`: a target able to fly along `u` faster than
`dirSpeed u` escapes every full-information strategy. This is the physical content
behind "a slower drone loses": the limit comes from motors, tilt envelope and drag,
and it depends on the direction.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {P : TargetParams} {Q : QuadParams} {C : CameraParams} {δ : ℝ}

/-- Maximum collective thrust per unit mass. -/
noncomputable def QuadParams.maxAcc (Q : QuadParams) : ℝ := 4 * Q.fMotor / Q.mass

/-- How far a thrust axis within the tilt envelope can point along `u`:
`cos (max 0 (angle u e₃ - tiltMax))`. -/
noncomputable def QuadParams.reach (Q : QuadParams) (u : E3) : ℝ :=
  Real.cos (max 0 (angle u up - Q.tiltMax))

/-- Net push available along `u` against gravity. -/
noncomputable def QuadParams.push (Q : QuadParams) (u : E3) : ℝ :=
  Q.maxAcc * max 0 (Q.reach u) - Q.g * ⟪up, u⟫

/-- The drag-limited sustainable speed along `u`. -/
noncomputable def QuadParams.dirSpeed (Q : QuadParams) (u : E3) : ℝ :=
  √(max 0 (Q.push u) / Q.drag)

/-- A thrust axis inside the tilt envelope points along `u` by at most `reach u`. -/
theorem inner_le_reach {b u : E3} (hb : ‖b‖ = 1) (hu : ‖u‖ = 1)
    (ht : angle b up ≤ Q.tiltMax) : ⟪b, u⟫ ≤ Q.reach u := by
  have hcos : ⟪b, u⟫ = Real.cos (angle b u) := by
    rw [cos_angle, hb, hu, mul_one, div_one]
  have htri := angle_le_angle_add_angle u b up
  rw [angle_comm u b] at htri
  rw [hcos, QuadParams.reach]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (le_max_left _ _) (angle_le_pi _ _)
  exact max_le (angle_nonneg _ _) (by linarith)

theorem QuadTraj.thrust_le (d : QuadTraj Q C δ) (k : ℕ) :
    totalThrust (d.f k) / Q.mass ≤ Q.maxAcc := by
  unfold totalThrust QuadParams.maxAcc
  apply div_le_div_of_nonneg_right _ Q.mass_pos.le
  linarith [d.motor_le k 0, d.motor_le k 1, d.motor_le k 2, d.motor_le k 3]

/-- One-step bound on the velocity component along `u`. -/
theorem dir_step_le (hkn : Q.normalDrag = 0) (d : QuadTraj Q C δ) (hδ : 0 < δ) {u : E3} (hu : ‖u‖ = 1) (k : ℕ) :
    ⟪d.v (k + 1), u⟫ ≤
      ⟪d.v k, u⟫ + δ * (Q.push u - Q.drag * ‖d.v k‖ * ⟪d.v k, u⟫) := by
  have hF0 := d.thrust_nonneg k
  have hF1 := d.thrust_le k
  have hreach := inner_le_reach (Q := Q) (d.b₃_unit k) hu (d.tilt_le k)
  have hthr : totalThrust (d.f k) / Q.mass * ⟪d.b₃ k, u⟫ ≤ Q.maxAcc * max 0 (Q.reach u) := by
    calc totalThrust (d.f k) / Q.mass * ⟪d.b₃ k, u⟫
        ≤ totalThrust (d.f k) / Q.mass * max 0 (Q.reach u) :=
          mul_le_mul_of_nonneg_left (hreach.trans (le_max_right _ _)) hF0
      _ ≤ Q.maxAcc * max 0 (Q.reach u) :=
          mul_le_mul_of_nonneg_right hF1 (le_max_left _ _)
  rw [d.translational k, hkn, zero_mul, zero_mul, sub_zero, inner_add_left, real_inner_smul_left, inner_sub_left,
    inner_sub_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left]
  unfold QuadParams.push
  have : ⟪up, u⟫ = ⟪up, u⟫ := rfl
  nlinarith [mul_le_mul_of_nonneg_left hthr hδ.le]

/-- The excess of the velocity component along `u` over any `V` with
`push u ≤ c_D V²` contracts by the factor `1 - 2 δ c_D V` each step. -/
theorem dir_excess_step (hkn : Q.normalDrag = 0) (d : QuadTraj Q C δ) (hδ : 0 < δ)
    (hfine : δ * Q.drag * Q.speedEnv ≤ 1 / 2) {u : E3} (hu : ‖u‖ = 1) {V : ℝ}
    (hV0 : 0 < V) (hVenv : V ≤ Q.speedEnv) (hV : Q.push u ≤ Q.drag * V ^ 2) (k : ℕ) :
    ⟪d.v (k + 1), u⟫ - V ≤ (1 - 2 * δ * Q.drag * V) * max 0 (⟪d.v k, u⟫ - V) := by
  have hstep := dir_step_le hkn d hδ hu k
  set s := ⟪d.v k, u⟫
  set n := ‖d.v k‖
  have hc := Q.drag_pos
  have hn : n ≤ Q.speedEnv := d.speed_le k
  have hsn : |s| ≤ n := by
    have := abs_real_inner_le_norm (d.v k) u
    rwa [hu, mul_one] at this
  have hdcV : δ * Q.drag * V ≤ 1 / 2 :=
    le_trans (mul_le_mul_of_nonneg_left hVenv (by positivity)) hfine
  have hdcn : δ * Q.drag * n ≤ 1 / 2 :=
    le_trans (mul_le_mul_of_nonneg_left hn (by positivity)) hfine
  have hfac : 0 ≤ 1 - 2 * δ * Q.drag * V := by linarith
  have hstep' : ⟪d.v (k + 1), u⟫ ≤ s + δ * (Q.drag * V ^ 2 - Q.drag * n * s) := by
    nlinarith [mul_le_mul_of_nonneg_left hV hδ.le]
  rcases le_or_gt s V with hsV | hsV
  · -- At or below `V`: the next component stays below `V`.
    have hrhs : 0 ≤ (1 - 2 * δ * Q.drag * V) * max 0 (s - V) :=
      mul_nonneg hfac (le_max_left _ _)
    rcases lt_or_ge s 0 with hs0 | hs0
    · -- Negative component: drag cannot push it past `δ c V² ≤ V / 2`.
      have h1 : s + δ * (Q.drag * V ^ 2 - Q.drag * n * s) ≤ V := by
        have hn0 : 0 ≤ n := le_trans (abs_nonneg s) hsn
        have : s * (1 - δ * Q.drag * n) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hs0.le (by linarith)
        nlinarith [mul_le_mul_of_nonneg_right hdcV hV0.le]
      linarith
    · have hns : s ≤ n := le_trans (le_abs_self s) hsn
      have h1 : s + δ * (Q.drag * V ^ 2 - Q.drag * n * s) ≤ V := by
        have hcs : Q.drag * s * s ≤ Q.drag * n * s :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hns hc.le) hs0
        have key : δ * Q.drag * (V - s) * (V + s) ≤ V - s := by
          have : δ * Q.drag * (V + s) ≤ 1 := by nlinarith
          nlinarith [sub_nonneg.2 hsV]
        nlinarith [mul_le_mul_of_nonneg_left hcs hδ.le]
      linarith
  · -- Above `V`: quadratic drag beats the push and the excess contracts.
    have hns : s ≤ n := le_trans (le_abs_self s) hsn
    have hcs : Q.drag * s * s ≤ Q.drag * n * s :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hns hc.le) (by linarith)
    rw [max_eq_right (by linarith)]
    have h1 := mul_le_mul_of_nonneg_left hcs hδ.le
    have h2 : 0 ≤ δ * Q.drag * (s - V) ^ 2 := by positivity
    have : δ * (Q.drag * V ^ 2 - Q.drag * n * s) ≤ -(2 * δ * Q.drag * V) * (s - V) := by
      nlinarith [h1, h2]
    nlinarith

/-- Consequently the quad advances along `u` at most `k δ V` plus a bounded
transient from its initial excess speed. -/
theorem dir_displacement_le (hkn : Q.normalDrag = 0) (d : QuadTraj Q C δ) (hδ : 0 < δ)
    (hfine : δ * Q.drag * Q.speedEnv ≤ 1 / 2) {u : E3} (hu : ‖u‖ = 1) {V : ℝ}
    (hV0 : 0 < V) (hVenv : V ≤ Q.speedEnv) (hV : Q.push u ≤ Q.drag * V ^ 2) (k : ℕ) :
    ⟪d.x k - d.x 0, u⟫ ≤ k * δ * V + max 0 (⟪d.v 0, u⟫ - V) / (2 * Q.drag * V) := by
  have hc := Q.drag_pos
  have hcV : 0 < 2 * Q.drag * V := by positivity
  set e : ℕ → ℝ := fun j => max 0 (⟪d.v j, u⟫ - V) with he
  have hcontract : ∀ j, e (j + 1) ≤ (1 - 2 * δ * Q.drag * V) * e j := by
    intro j
    have h1 := dir_excess_step hkn d hδ hfine hu hV0 hVenv hV j
    have hdcV : δ * Q.drag * V ≤ 1 / 2 :=
      le_trans (mul_le_mul_of_nonneg_left hVenv (by positivity)) hfine
    exact max_le (mul_nonneg (by linarith) (le_max_left _ _)) h1
  -- Invariant: displacement ≤ k δ V + (e 0 - e k) / (2 c V).
  have inv : ∀ j : ℕ, ⟪d.x j - d.x 0, u⟫ ≤ j * δ * V + (e 0 - e j) / (2 * Q.drag * V) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hstep : ⟪d.x (j + 1) - d.x j, u⟫ ≤ δ * V + δ * e j := by
        rw [d.steps j, add_sub_cancel_left, real_inner_smul_left]
        have : ⟪d.v j, u⟫ ≤ V + e j := by
          have := le_max_right 0 (⟪d.v j, u⟫ - V); simp only [he]; linarith
        nlinarith
      have hsplit : d.x (j + 1) - d.x 0 = (d.x (j + 1) - d.x j) + (d.x j - d.x 0) := by abel
      rw [hsplit, inner_add_left]
      have hcj := hcontract j
      have hkey : δ * e j ≤ (e j - e (j + 1)) / (2 * Q.drag * V) := by
        rw [le_div_iff₀ hcV]; nlinarith
      have : (e 0 - e j) / (2 * Q.drag * V) + (e j - e (j + 1)) / (2 * Q.drag * V)
          = (e 0 - e (j + 1)) / (2 * Q.drag * V) := by
        field_simp; ring
      push_cast
      nlinarith
  have hek : 0 ≤ e k := le_max_left _ _
  calc ⟪d.x k - d.x 0, u⟫ ≤ k * δ * V + (e 0 - e k) / (2 * Q.drag * V) := inv k
    _ ≤ k * δ * V + e 0 / (2 * Q.drag * V) := by
        gcongr; linarith

/-- Escape against any trajectory whose advance along `u` is at most `k δ V + K`. -/
theorem straightTarget_escapes_of_displacement (P : TargetParams) {δ : ℝ} (hδ : 0 < δ)
    (p₀ u : E3) (hu : ‖u‖ = 1) (hclimb : |⟪u, up⟫| ≤ Real.sin P.climbMax)
    {x : ℕ → E3} {V K : ℝ} (hx : ∀ k : ℕ, ⟪x k - x 0, u⟫ ≤ k * δ * V + K)
    (hV : V < P.vMax) (R : ℝ) :
    ∃ k, R < ‖(straightTarget P hδ.le p₀ u hu hclimb).p k - x k‖ := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((R + K - ⟪p₀ - x 0, u⟫) / (δ * (P.vMax - V)))
  have hgap : 0 < δ * (P.vMax - V) := mul_pos hδ (by linarith)
  have hk' : R + K - ⟪p₀ - x 0, u⟫ < k * (δ * (P.vMax - V)) := (div_lt_iff₀ hgap).1 hk
  have hdisp := hx k
  refine ⟨k, ?_⟩
  have hfar : R < ⟪(straightTarget P hδ.le p₀ u hu hclimb).p k - x k, u⟫ := by
    have hexp : (straightTarget P hδ.le p₀ u hu hclimb).p k - x k
        = (p₀ - x 0) + ((k : ℝ) * δ * P.vMax) • u - (x k - x 0) := by
      simp only [straightTarget]; abel
    rw [hexp, inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hu]
    nlinarith
  have hle : ⟪(straightTarget P hδ.le p₀ u hu hclimb).p k - x k, u⟫
      ≤ ‖(straightTarget P hδ.le p₀ u hu hclimb).p k - x k‖ := by
    simpa [hu] using real_inner_le_norm _ u
  exact hfar.trans_le hle

/-- **Directional escape.** If the target may fly along `u` (within its climb limit)
faster than the quad can sustain along `u`, no full-information strategy keeps it in
view, whatever the motors, attitude and camera do. -/
theorem not_maintainable_of_dirSpeed_lt (hkn : Q.normalDrag = 0) (hδ : 0 < δ)
    (hfine : δ * Q.drag * Q.speedEnv ≤ 1 / 2) (p₀ : E3) {u : E3} (hu : ‖u‖ = 1)
    (hclimb : |⟪u, up⟫| ≤ Real.sin P.climbMax) (hslow : Q.dirSpeed u < P.vMax) :
    ¬ MaintainableFullInfo P Q C δ p₀ (P.vMax • u) 0 := by
  rintro ⟨σ, hσ⟩
  set T := straightTarget P hδ.le p₀ u hu hclimb
  have hT := straightTarget_startsAt P hδ.le p₀ u hu hclimb
  have hkeep := hσ T hT
  set d := σ.play T hT
  have hc := Q.drag_pos
  have hvM : 0 < P.vMax := P.vMin_pos.trans_le P.vMin_le_vMax
  -- Pick a speed `V` strictly between the quad's limit and the target's speed.
  obtain ⟨V, K, hV, hx⟩ : ∃ V K : ℝ, V < P.vMax ∧ ∀ k : ℕ, ⟪d.x k - d.x 0, u⟫ ≤ k * δ * V + K := by
    rcases le_or_gt P.vMax Q.speedEnv with henv | henv
    · set V := (Q.dirSpeed u + P.vMax) / 2 with hVdef
      have hds0 : 0 ≤ Q.dirSpeed u := Real.sqrt_nonneg _
      have hdsV : Q.dirSpeed u ≤ V := by rw [hVdef]; linarith
      have hV0 : 0 < V := by positivity
      have hVlt : V < P.vMax := by rw [hVdef]; linarith
      have hpush : Q.push u ≤ Q.drag * V ^ 2 := by
        have h1 : Q.dirSpeed u ^ 2 = max 0 (Q.push u) / Q.drag :=
          Real.sq_sqrt (div_nonneg (le_max_left _ _) hc.le)
        have h2 : Q.dirSpeed u ^ 2 ≤ V ^ 2 := by
          exact pow_le_pow_left₀ hds0 hdsV 2
        have h3 : max 0 (Q.push u) ≤ Q.drag * V ^ 2 := by
          rw [h1, div_le_iff₀ hc] at h2; linarith
        exact (le_max_right _ _).trans h3
      exact ⟨V, _, hVlt, dir_displacement_le hkn d hδ hfine hu hV0 (by linarith) hpush⟩
    · refine ⟨Q.speedEnv, 0, henv, ?_⟩
      have hv : ∀ k, ⟪d.v k, u⟫ ≤ Q.speedEnv := fun k => by
        have := real_inner_le_norm (d.v k) u
        rw [hu, mul_one] at this
        exact this.trans (d.speed_le k)
      intro k
      simpa using inner_displacement_le hδ.le d.steps hv k
  obtain ⟨k, hk⟩ := straightTarget_escapes_of_displacement P hδ p₀ u hu hclimb hx hV
    (C.detectRange P.size)
  exact absurd (hkeep k).1 (not_le.2 hk)

end VisionTracking

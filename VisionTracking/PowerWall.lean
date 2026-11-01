import VisionTracking.Necessity3

/-!
# The power wall (rotor-disc normal force)

With the rotor-disc normal force `-k_n ‖v‖ ⟪v, b₃⟫ b₃`, the power the motors can put into
the flight path is limited at speed. With `y = ⟪v, b₃⟫` and collective `F ≤ F_max`:

  `⟪v, F b₃ - k_n ‖v‖ y b₃⟫ = F y - k_n ‖v‖ y² ≤ min (F_max ‖v‖) (F_max² / (4 k_n ‖v‖))`.

The mechanical energy `½‖v‖² + g z` therefore changes by at most
`δ (availPower ‖v‖ - c ‖v‖³)` per step (plus `δ² B²/2`). If a line `α - β s` lies above
`availPower s - c s³` on the speed envelope, a drone that stays within range of a level
target can average at most `(α + δ B²/2)/β` along it. A faster level target escapes
**every** trajectory: `no_traj_keeps_of_power`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {P : TargetParams} {Q : QuadParams} {C : CameraParams} {δ : ℝ}

/-- Power available along the flight path, per unit mass, at speed `s`. -/
noncomputable def QuadParams.availPower (Q : QuadParams) (s : ℝ) : ℝ :=
  min (Q.maxAcc * s) (Q.maxAcc ^ 2 / (4 * Q.normalDrag * s))

/-- A bound on the acceleration over the speed envelope. -/
noncomputable def QuadParams.accBound (Q : QuadParams) : ℝ :=
  Q.maxAcc + Q.normalDrag * Q.speedEnv ^ 2 + Q.g + Q.drag * Q.speedEnv ^ 2

theorem power_le_availPower (hkn : 0 < Q.normalDrag) {F s y : ℝ} (hF0 : 0 ≤ F)
    (hF1 : F ≤ Q.maxAcc) (hs : 0 ≤ s) (hy : |y| ≤ s) :
    F * y - Q.normalDrag * s * y ^ 2 ≤ Q.availPower s := by
  have hq : 0 ≤ Q.normalDrag * s * y ^ 2 := by positivity
  apply le_min
  · rcases le_or_gt y 0 with h0 | h0
    · have : F * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hF0 h0
      have : 0 ≤ Q.maxAcc * s := mul_nonneg (hF0.trans hF1) hs
      linarith
    · have h1 : y ≤ s := (le_abs_self y).trans hy
      have := mul_le_mul hF1 h1 h0.le (hF0.trans hF1)
      have := mul_le_mul_of_nonneg_left h0.le hF0
      linarith
  · rcases eq_or_lt_of_le hs with h0 | h0
    · subst h0
      have : y = 0 := abs_nonpos_iff.1 hy
      simp [this]
    · have hd : 0 < 4 * Q.normalDrag * s := by positivity
      rw [le_div_iff₀ hd]
      have hFF : F ^ 2 ≤ Q.maxAcc ^ 2 := pow_le_pow_left₀ hF0 hF1 2
      nlinarith [sq_nonneg (2 * Q.normalDrag * s * y - F)]

/-- The acceleration of step `k`. -/
noncomputable def QuadTraj.acc (d : QuadTraj Q C δ) (k : ℕ) : E3 :=
  (totalThrust (d.f k) / Q.mass - Q.normalDrag * ‖d.v k‖ * ⟪d.v k, d.b₃ k⟫) • d.b₃ k
    - Q.g • up - (Q.drag * ‖d.v k‖) • d.v k

theorem QuadTraj.norm_acc_le (d : QuadTraj Q C δ) (k : ℕ) : ‖d.acc k‖ ≤ Q.accBound := by
  have hF0 := d.thrust_nonneg k
  have hF1 := d.thrust_le k
  have hS := d.speed_le k
  have hn := norm_nonneg (d.v k)
  have hS0 : 0 ≤ Q.speedEnv := hn.trans hS
  have hkn := Q.normalDrag_nonneg
  have hc := Q.drag_pos.le
  generalize hF : totalThrust (d.f k) / Q.mass = F at hF0 hF1
  have hy : |⟪d.v k, d.b₃ k⟫| ≤ ‖d.v k‖ := by
    have := abs_real_inner_le_norm (d.v k) (d.b₃ k); rwa [d.b₃_unit k, mul_one] at this
  generalize hY : ⟪d.v k, d.b₃ k⟫ = y at hy
  generalize hV : ‖d.v k‖ = s at hn hS hy
  have hsy : s * |y| ≤ Q.speedEnv ^ 2 := by
    rw [sq]; exact mul_le_mul hS (hy.trans hS) (abs_nonneg _) hS0
  have hss : s * s ≤ Q.speedEnv ^ 2 := by rw [sq]; exact mul_le_mul hS hS hn hS0
  have t1 : ‖(F - Q.normalDrag * s * y) • d.b₃ k‖ ≤ Q.maxAcc + Q.normalDrag * Q.speedEnv ^ 2 := by
    rw [norm_smul, d.b₃_unit k, mul_one, Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hF0, mul_assoc, abs_mul, abs_of_nonneg hkn, abs_mul, abs_of_nonneg hn]
    have := mul_le_mul_of_nonneg_left hsy hkn
    linarith
  have t2 : ‖Q.g • up‖ = Q.g := by rw [norm_smul, norm_up', mul_one, Real.norm_of_nonneg Q.g_pos.le]
  have t3 : ‖(Q.drag * s) • d.v k‖ ≤ Q.drag * Q.speedEnv ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (mul_nonneg hc hn), hV, mul_assoc]
    exact mul_le_mul_of_nonneg_left hss hc
  have e : d.acc k = (F - Q.normalDrag * s * y) • d.b₃ k - Q.g • up - (Q.drag * s) • d.v k := by
    rw [QuadTraj.acc, hF, hY, hV]
  rw [e]
  have u1 := norm_sub_le ((F - Q.normalDrag * s * y) • d.b₃ k - Q.g • up) ((Q.drag * s) • d.v k)
  have u2 := norm_sub_le ((F - Q.normalDrag * s * y) • d.b₃ k) (Q.g • up)
  unfold QuadParams.accBound
  linarith

/-- Mechanical energy per unit mass. -/
noncomputable def QuadTraj.energy (d : QuadTraj Q C δ) (k : ℕ) : ℝ :=
  ‖d.v k‖ ^ 2 / 2 + Q.g * ⟪d.x k, up⟫

/-- **Energy step.** -/
theorem QuadTraj.energy_step (d : QuadTraj Q C δ) (hδ : 0 < δ) (hkn : 0 < Q.normalDrag)
    (k : ℕ) :
    d.energy (k + 1) - d.energy k
      ≤ δ * (Q.availPower ‖d.v k‖ - Q.drag * ‖d.v k‖ ^ 3) + δ ^ 2 * Q.accBound ^ 2 / 2 := by
  have hv : d.v (k + 1) = d.v k + δ • d.acc k := by rw [d.translational k]; rfl
  have hx : d.x (k + 1) = d.x k + δ • d.v k := d.steps k
  set s := ‖d.v k‖
  set y := ⟪d.v k, d.b₃ k⟫
  set F := totalThrust (d.f k) / Q.mass
  have hpow : ⟪d.v k, d.acc k⟫ = F * y - Q.normalDrag * s * y ^ 2 - Q.g * ⟪d.v k, up⟫
      - Q.drag * s ^ 3 := by
    simp only [QuadTraj.acc, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hP := power_le_availPower (Q := Q) hkn (d.thrust_nonneg k) (d.thrust_le k)
    (norm_nonneg (d.v k)) (by
      have := abs_real_inner_le_norm (d.v k) (d.b₃ k); rwa [d.b₃_unit k, mul_one] at this)
  have hA := d.norm_acc_le k
  have hA2 : ‖d.acc k‖ ^ 2 ≤ Q.accBound ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hE : d.energy (k + 1) - d.energy k
      = δ * ⟪d.v k, d.acc k⟫ + δ ^ 2 * ‖d.acc k‖ ^ 2 / 2 + Q.g * δ * ⟪d.v k, up⟫ := by
    simp only [QuadTraj.energy]
    rw [hv, hx, norm_add_sq_real, norm_smul, real_inner_smul_right, inner_add_left,
      real_inner_smul_left, Real.norm_of_nonneg hδ.le]
    ring
  rw [hE, hpow]
  have := mul_le_mul_of_nonneg_left hP hδ.le
  nlinarith [mul_le_mul_of_nonneg_left hA2 (by positivity : (0 : ℝ) ≤ δ ^ 2 / 2)]

/-- **Energy-displacement budget.** -/
theorem QuadTraj.energy_disp_le (d : QuadTraj Q C δ) (hδ : 0 < δ) (hkn : 0 < Q.normalDrag)
    {α β : ℝ} (hβ : 0 ≤ β)
    (hline : ∀ s, 0 ≤ s → s ≤ Q.speedEnv → Q.availPower s - Q.drag * s ^ 3 ≤ α - β * s)
    {u : E3} (hu : ‖u‖ = 1) (N : ℕ) :
    d.energy N - d.energy 0 + β * ⟪d.x N - d.x 0, u⟫
      ≤ N * δ * (α + δ * Q.accBound ^ 2 / 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hst := d.energy_step hδ hkn N
    have hl := hline ‖d.v N‖ (norm_nonneg _) (d.speed_le N)
    have hvu : ⟪d.v N, u⟫ ≤ ‖d.v N‖ := by
      have := real_inner_le_norm (d.v N) u; rwa [hu, mul_one] at this
    have hx : d.x (N + 1) - d.x 0 = (d.x N - d.x 0) + δ • d.v N := by rw [d.steps N]; abel
    rw [hx, inner_add_left, real_inner_smul_left]
    push_cast
    have h1 := mul_le_mul_of_nonneg_left hl hδ.le
    have h2 := mul_le_mul_of_nonneg_left hvu (mul_nonneg hβ hδ.le)
    nlinarith

/-- **Power wall, trajectory form.** A level target faster than the power wall escapes
every drone trajectory. -/
theorem no_traj_keeps_of_power (hδ : 0 < δ) (hkn : 0 < Q.normalDrag) {α β : ℝ} (hβ : 0 < β)
    (hline : ∀ s, 0 ≤ s → s ≤ Q.speedEnv → Q.availPower s - Q.drag * s ^ 3 ≤ α - β * s)
    (hfast : α + δ * Q.accBound ^ 2 / 2 < β * P.vMax)
    (p₀ : E3) {u : E3} (hu : ‖u‖ = 1) (hclimb : |⟪u, up⟫| ≤ Real.sin P.climbMax)
    (hhor : ⟪u, up⟫ = 0) (d : QuadTraj Q C δ) :
    ¬ KeepsInView C P.size d (straightTarget P hδ.le p₀ u hu hclimb) := by
  intro hkeep
  set D := C.detectRange P.size
  set T := straightTarget P hδ.le p₀ u hu hclimb
  have hTz : ∀ k, ⟪T.p k, up⟫ = ⟪p₀, up⟫ := by
    intro k; simp [T, straightTarget, inner_add_left, real_inner_smul_left, hhor]
  have hz : ∀ k, -(2 * D) ≤ ⟪d.x k - d.x 0, up⟫ := by
    intro k
    have r1 := (hkeep k).1
    have r0 := (hkeep 0).1
    have a1 : |⟪T.p k - d.x k, up⟫| ≤ D := by
      have := abs_real_inner_le_norm (T.p k - d.x k) up
      rw [norm_up', mul_one] at this; exact this.trans r1
    have a0 : |⟪T.p 0 - d.x 0, up⟫| ≤ D := by
      have := abs_real_inner_le_norm (T.p 0 - d.x 0) up
      rw [norm_up', mul_one] at this; exact this.trans r0
    rw [inner_sub_left] at a1 a0 ⊢
    rw [hTz] at a1 a0
    linarith [(abs_le.1 a1).1, (abs_le.1 a1).2, (abs_le.1 a0).1, (abs_le.1 a0).2]
  set α' := α + δ * Q.accBound ^ 2 / 2 with hα'
  have hdisp : ∀ k : ℕ, ⟪d.x k - d.x 0, u⟫
      ≤ k * δ * (α' / β) + (Q.speedEnv ^ 2 / 2 + 2 * Q.g * D) / β := by
    intro k
    have hb := d.energy_disp_le hδ hkn hβ.le hline hu k
    rw [← hα'] at hb
    have hv0 : ‖d.v 0‖ ^ 2 ≤ Q.speedEnv ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (d.speed_le 0) 2
    have hE : -(Q.speedEnv ^ 2 / 2) + Q.g * ⟪d.x k - d.x 0, up⟫ ≤ d.energy k - d.energy 0 := by
      simp only [QuadTraj.energy, inner_sub_left]
      nlinarith [sq_nonneg ‖d.v k‖]
    have hgz := mul_le_mul_of_nonneg_left (hz k) Q.g_pos.le
    rw [show (k : ℝ) * δ * (α' / β) + (Q.speedEnv ^ 2 / 2 + 2 * Q.g * D) / β
        = (k * δ * α' + (Q.speedEnv ^ 2 / 2 + 2 * Q.g * D)) / β by field_simp,
      le_div_iff₀ hβ]
    nlinarith
  have hV : α' / β < P.vMax := by rw [div_lt_iff₀ hβ]; linarith
  obtain ⟨k, hk⟩ := straightTarget_escapes_of_displacement P hδ p₀ u hu hclimb hdisp hV D
  exact absurd (hkeep k).1 (not_le.2 hk)

/-- **The necessary inequality with the rotor-disc normal force**: every line above the
available power caps the target's top speed. -/
def NecPower (P : TargetParams) (Q : QuadParams) (δ : ℝ) : Prop :=
  ∀ α β : ℝ, 0 < β →
    (∀ s, 0 ≤ s → s ≤ Q.speedEnv → Q.availPower s - Q.drag * s ^ 3 ≤ α - β * s) →
    β * P.vMax ≤ α + δ * Q.accBound ^ 2 / 2

/-- **Necessary side with the rotor-disc normal force.** -/
theorem master_necessary_power (hδ : 0 < δ) (hkn : 0 < Q.normalDrag)
    (h : ∀ p₀ v₀ a₀ : E3, MaintainableSteady P Q C δ p₀ v₀ a₀) : NecPower P Q δ := by
  intro α β hβ hline
  by_contra hlt
  have hu : ‖ex‖ = 1 := by simp [ex]
  have hhor : ⟪ex, up⟫ = 0 := by simp [ex, up, inner_eq_coords]
  have hclimb : |⟪ex, up⟫| ≤ Real.sin P.climbMax := by
    rw [hhor, abs_zero]; exact sin_climb_nonneg P
  obtain ⟨σ, hσ⟩ := h 0 (P.vMax • ex) 0
  have hS := straightTarget_startsSteady (P := P) hδ 0 hu hclimb
  exact no_traj_keeps_of_power hδ hkn hβ hline (not_le.1 hlt) 0 hu hclimb hhor _ (hσ _ hS)

/-- **P3 bracket with the rotor-disc normal force.** -/
theorem p3_bracket_power (F : FIR) (hlag : ∀ i < 4, F.h i = 0) {d : ℝ}
    (hδ : 0 < δ) (hkn : 0 < Q.normalDrag) :
    (MasterIneq3 P Q C δ F d → ∀ p₀ v₀ a₀ : E3, MaintainableSteady P Q C δ p₀ v₀ a₀) ∧
    ((∀ p₀ v₀ a₀ : E3, MaintainableSteady P Q C δ p₀ v₀ a₀) → NecPower P Q δ) :=
  ⟨fun h p₀ v₀ a₀ => master_sufficient3 F hlag h p₀ v₀ a₀,
    master_necessary_power hδ hkn⟩

end VisionTracking

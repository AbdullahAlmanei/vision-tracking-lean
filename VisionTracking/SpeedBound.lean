import VisionTracking.Model

/-!
# Speed is a hard limit

If the target can fly faster than the drone, tracking cannot be maintained: the
target flies in a straight line at full speed, and its distance along that line
grows by at least `δ (v_T − v_D)` per step whatever the drone does. This holds
against *every* drone trajectory, not just causal strategies, so it also covers
drones that know the target's future.
-/

open InnerProductGeometry
open scoped RealInnerProductSpace

namespace VisionTracking

/-- A trajectory with speed at most `vD` advances at most `k δ vD` along any unit
direction in `k` steps. -/
theorem inner_displacement_le {δ vD : ℝ} (hδ : 0 ≤ δ) {x v : ℕ → E3}
    (hs : StepsWith δ x v) (hv : ∀ k, ‖v k‖ ≤ vD) {u : E3} (hu : ‖u‖ = 1) :
    ∀ k : ℕ, ⟪x k - x 0, u⟫ ≤ k * δ * vD := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : ⟪x (k + 1) - x k, u⟫ ≤ δ * vD := by
      rw [hs k, add_sub_cancel_left, real_inner_smul_left]
      have h1 : ⟪v k + v (k + 1), u⟫ ≤ ‖v k + v (k + 1)‖ := by
        simpa [hu] using real_inner_le_norm (v k + v (k + 1)) u
      have h2 : ‖v k + v (k + 1)‖ ≤ 2 * vD := by
        linarith [norm_add_le (v k) (v (k + 1)), hv k, hv (k + 1)]
      nlinarith
    have hsplit : x (k + 1) - x 0 = (x (k + 1) - x k) + (x k - x 0) := by abel
    rw [hsplit, inner_add_left]
    push_cast
    linarith

/-- The straight-line, full-speed target trajectory from `p₀` along the unit
vector `u`. -/
noncomputable def straightTarget (P : TargetParams) {δ : ℝ} (hδ : 0 ≤ δ)
    (p₀ u : E3) (hu : ‖u‖ = 1) : TargetTraj P δ where
  p k := p₀ + ((k : ℝ) * δ * P.vMax) • u
  v _ := P.vMax • u
  steps k := by
    push_cast
    rw [← two_smul ℝ (P.vMax • u), smul_smul, smul_smul, add_assoc, ← add_smul]
    congr 2
    ring
  speed_ge _ := by
    rw [norm_smul, hu, Real.norm_of_nonneg (P.vMin_pos.le.trans P.vMin_le_vMax)]
    simpa using P.vMin_le_vMax
  speed_le _ := by
    rw [norm_smul, hu, Real.norm_of_nonneg (P.vMin_pos.le.trans P.vMin_le_vMax)]
    simp
  tangential _ := by
    simp only [sub_self, inner_zero_left, abs_zero]
    have := P.aTan_nonneg
    have := P.vMin_pos.le.trans P.vMin_le_vMax
    positivity
  normal _ := by
    simp only [sub_self, inner_zero_left, zero_div, zero_smul, norm_zero]
    have := P.turnRadius_pos
    positivity

/-- **Speed impossibility.** If the target's top speed exceeds the drone's, then
against the straight full-speed target every drone trajectory eventually leaves
detection range, whatever its camera does. -/
theorem straightTarget_escapes (P : TargetParams) (D : DroneParams)
    (C : CameraParams) {δ : ℝ} (hδ : 0 < δ) (hspeed : D.vMax < P.vMax)
    (p₀ u : E3) (hu : ‖u‖ = 1) (d : DroneTraj D C δ) :
    ¬ KeepsInView C P.size d (straightTarget P hδ.le p₀ u hu) := by
  intro hkeep
  set R := C.detectRange P.size
  obtain ⟨k, hk⟩ := exists_nat_gt ((R - ⟪p₀ - d.x 0, u⟫) / (δ * (P.vMax - D.vMax)))
  have hgap : 0 < δ * (P.vMax - D.vMax) := mul_pos hδ (by linarith)
  have hk' : R - ⟪p₀ - d.x 0, u⟫ < k * (δ * (P.vMax - D.vMax)) :=
    (div_lt_iff₀ hgap).1 hk
  have hdisp := inner_displacement_le hδ.le d.steps d.speed_le hu k
  have hfar : R < ⟪(straightTarget P hδ.le p₀ u hu).p k - d.x k, u⟫ := by
    have hexp : (straightTarget P hδ.le p₀ u hu).p k - d.x k
        = (p₀ - d.x 0) + ((k : ℝ) * δ * P.vMax) • u - (d.x k - d.x 0) := by
      simp only [straightTarget]; abel
    rw [hexp, inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hu]
    nlinarith
  have hle : ⟪(straightTarget P hδ.le p₀ u hu).p k - d.x k, u⟫
      ≤ ‖(straightTarget P hδ.le p₀ u hu).p k - d.x k‖ := by
    simpa [hu] using real_inner_le_norm _ u
  exact absurd (hkeep k).1 (not_le.2 (hfar.trans_le hle))

/-- **Corollary.** If `D.vMax < P.vMax`, tracking is not maintainable from any
start position (the target starts at full speed in any direction). -/
theorem not_maintainable_of_slower (P : TargetParams) (D : DroneParams)
    (C : CameraParams) {δ : ℝ} (hδ : 0 < δ) (hspeed : D.vMax < P.vMax)
    (p₀ u : E3) (hu : ‖u‖ = 1) :
    ¬ Maintainable P D C δ p₀ (P.vMax • u) := by
  rintro ⟨σ, hσ⟩
  exact straightTarget_escapes P D C hδ hspeed p₀ u hu (σ.play _)
    (hσ (straightTarget P hδ.le p₀ u hu) (by simp [straightTarget]) rfl)

end VisionTracking

import VisionTracking.Model

/-!
# Escape along a direction

The kinematic core of every "the target simply flies away" argument. If some
sequence of positions advances along a unit direction `u` at no more than `V` per
unit time, a straight-line target at speed `vMax > V` along `u` eventually leaves any
fixed range. The physical work, showing that a quadrotor's velocity component along
`u` really is bounded (from its thrust, tilt envelope and drag), is done separately
for each direction (`DirectionalSpeed.lean`).
-/

open InnerProductGeometry
open scoped RealInnerProductSpace

namespace VisionTracking

/-- A trajectory whose velocity component along the unit vector `u` is at most `V`
advances at most `k δ V` along `u` in `k` steps. -/
theorem inner_displacement_le {δ V : ℝ} (hδ : 0 ≤ δ) {x v : ℕ → E3}
    (hs : StepsWith δ x v) {u : E3} (hv : ∀ k, ⟪v k, u⟫ ≤ V) :
    ∀ k : ℕ, ⟪x k - x 0, u⟫ ≤ k * δ * V := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : ⟪x (k + 1) - x k, u⟫ ≤ δ * V := by
      rw [hs k, add_sub_cancel_left, real_inner_smul_left]
      exact mul_le_mul_of_nonneg_left (hv k) hδ
    have hsplit : x (k + 1) - x 0 = (x (k + 1) - x k) + (x k - x 0) := by abel
    rw [hsplit, inner_add_left]
    push_cast
    linarith

/-- The straight-line, full-speed target trajectory from `p₀` along the unit vector
`u`, which must respect the climb limit. -/
noncomputable def straightTarget (P : TargetParams) {δ : ℝ} (hδ : 0 ≤ δ)
    (p₀ u : E3) (hu : ‖u‖ = 1) (hclimb : |⟪u, up⟫| ≤ Real.sin P.climbMax) :
    TargetTraj P δ where
  p k := p₀ + ((k : ℝ) * δ * P.vMax) • u
  v _ := P.vMax • u
  steps k := by
    push_cast
    module
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
    have hv := P.vMin_pos.le.trans P.vMin_le_vMax
    rw [real_inner_smul_left, abs_mul, abs_of_nonneg hv, norm_smul, hu,
      Real.norm_of_nonneg hv, mul_one]
    exact mul_le_mul_of_nonneg_left hclimb hv

theorem straightTarget_startsAt (P : TargetParams) {δ : ℝ} (hδ : 0 ≤ δ) (p₀ u : E3)
    (hu : ‖u‖ = 1) (hclimb : |⟪u, up⟫| ≤ Real.sin P.climbMax) :
    (straightTarget P hδ p₀ u hu hclimb).StartsAt p₀ (P.vMax • u) 0 := by
  refine ⟨by simp [straightTarget], rfl, by simp [straightTarget]⟩

/-- **Escape.** If a position sequence's velocity component along `u` stays at most
`V < vMax`, the straight full-speed target along `u` is eventually beyond any range
`R` from it. -/
theorem straightTarget_escapes (P : TargetParams) {δ : ℝ} (hδ : 0 < δ) (p₀ u : E3)
    (hu : ‖u‖ = 1) (hclimb : |⟪u, up⟫| ≤ Real.sin P.climbMax) {x v : ℕ → E3}
    (hs : StepsWith δ x v) {V : ℝ} (hv : ∀ k, ⟪v k, u⟫ ≤ V) (hV : V < P.vMax) (R : ℝ) :
    ∃ k, R < ‖(straightTarget P hδ.le p₀ u hu hclimb).p k - x k‖ := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((R - ⟪p₀ - x 0, u⟫) / (δ * (P.vMax - V)))
  have hgap : 0 < δ * (P.vMax - V) := mul_pos hδ (by linarith)
  have hk' : R - ⟪p₀ - x 0, u⟫ < k * (δ * (P.vMax - V)) := (div_lt_iff₀ hgap).1 hk
  have hdisp := inner_displacement_le hδ.le hs hv k
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

end VisionTracking

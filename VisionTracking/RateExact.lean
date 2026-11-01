import VisionTracking.BodyRate
import VisionTracking.SharpNorm

/-!
# The exact change of body rate

A rotation fixes its own axis. So when the frame moves by `rotate ω_k`, the body
coordinates of `ω_k` are the same in the old and the new frame. The change of body rate is
therefore exactly the change of the world rotation vector, read in the new frame:

  `rate (k+1) - rate k = δ⁻¹ toF (b (k+1)) (ω_{k+1} - ω_k)`.

In particular `‖Δrate‖ = ‖Δω‖/δ`, with no rate-product terms.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

/-- A rotation fixes its own axis. -/
theorem rotate_self (ω : E3) : rotate ω ω = ω := by
  by_cases h0 : ω = 0
  · rw [h0, rotate_zero]
  have hn : ‖ω‖ ≠ 0 := norm_ne_zero_iff.2 h0
  have hcr : cross (‖ω‖⁻¹ • ω) ω = 0 := by
    rw [cross_smul_left, cross_self', smul_zero]
  have hin : ⟪‖ω‖⁻¹ • ω, ω⟫ = ‖ω‖ := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]; field_simp
  rw [rotate, hcr, smul_zero, add_zero, hin, smul_smul]
  have : (1 - Real.cos ‖ω‖) * ‖ω‖ * ‖ω‖⁻¹ = 1 - Real.cos ‖ω‖ := by field_simp
  rw [this]; module

/-- Inner products with the axis are preserved. -/
theorem inner_rotate_axis (ω x : E3) : ⟪rotate ω x, ω⟫ = ⟪x, ω⟫ := by
  have := inner_rotate ω x ω
  rwa [rotate_self] at this

namespace KinPlan

variable {Q : QuadParams} {C : CameraParams} {δ : ℝ} (p : KinPlan Q C δ)

/-- Body coordinates of the step's rotation vector are the same in the new frame. -/
theorem toF_next_rotVec (k : ℕ) :
    toF (p.b₁ (k + 1)) (p.b₂ (k + 1)) (p.rotVec k) = toF (p.b₁ k) (p.b₂ k) (p.rotVec k) := by
  obtain ⟨-, h1, h2, h3⟩ := p.rotVec_spec k
  have e3 : cross (p.b₁ (k + 1)) (p.b₂ (k + 1)) = rotate (p.rotVec k) (p.b₃ k) := by
    rw [h3]; rfl
  ext j; fin_cases j
  · simp [toF, ← h1, inner_rotate_axis]
  · simp [toF, ← h2, inner_rotate_axis]
  · simp only [toF]; rw [e3]; simp [inner_rotate_axis, KinPlan.b₃]

/-- **Exact rate change.** -/
theorem rate_sub_eq (k : ℕ) :
    p.rate (k + 1) - p.rate k
      = δ⁻¹ • toF (p.b₁ (k + 1)) (p.b₂ (k + 1)) (p.rotVec (k + 1) - p.rotVec k) := by
  rw [rate, rate, ← p.toF_next_rotVec k, toF_sub, smul_sub]

theorem norm_rate_sub_eq (hδ : 0 < δ) (k : ℕ) :
    ‖p.rate (k + 1) - p.rate k‖ = ‖p.rotVec (k + 1) - p.rotVec k‖ / δ := by
  rw [p.rate_sub_eq, norm_smul, norm_inv, Real.norm_of_nonneg hδ.le,
    norm_toF (p.b₁_unit _) (p.b₂_unit _) (p.b₁₂_orth _), inv_mul_eq_div]

end KinPlan

end VisionTracking

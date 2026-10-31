import VisionTracking.SharpNorm
import VisionTracking.SteadyFormation

/-!
# Minimal rotations and parallel transport

For unit vectors `a, b` with `⟪a, b⟫ ≥ 0`, `minRot a b = psiVec (a × b)` is the rotation
vector of the smallest rotation taking `a` to `b`: its axis is `a × b`, its angle
`angle a b`, and it has no component along `a`. A body frame carried by these minimal
rotations is *parallel transported*: it never yaws about its thrust axis.
-/

set_option linter.unusedSimpArgs false

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

noncomputable def minRot (a b : E3) : E3 := psiVec (cross a b)

theorem cross_cross_unit {a b : E3} (ha : ‖a‖ = 1) : cross (cross a b) a = b - ⟪a, b⟫ • a := by
  have hA := coords_unit ha
  ext i; fin_cases i
  · simp only [Fin.zero_eta, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two,
      inner_eq_coords]
    linear_combination (b.ofLp 0) * hA
  · simp only [Fin.mk_one, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two,
      inner_eq_coords]
    linear_combination (b.ofLp 1) * hA
  · simp only [Fin.reduceFinMk, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two,
      inner_eq_coords]
    linear_combination (b.ofLp 2) * hA

theorem norm_psiVec_eq (σ : E3) : ‖psiVec σ‖ = Real.arcsin ‖σ‖ := by
  have h0 : 0 ≤ Real.arcsin ‖σ‖ / ‖σ‖ :=
    div_nonneg (Real.arcsin_nonneg.2 (norm_nonneg _)) (norm_nonneg _)
  rw [psiVec, norm_smul, Real.norm_of_nonneg h0, arcsin_div_mul]

theorem rotate_minRot {a b : E3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : 0 ≤ ⟪a, b⟫) :
    rotate (minRot a b) a = b := by
  have hsq : ‖cross a b‖ ^ 2 = 1 - ⟪a, b⟫ ^ 2 := by rw [norm_cross_sq, ha, hb]; ring
  by_cases h0 : cross a b = 0
  · have h1 : ⟪a, b⟫ = 1 := by
      rw [h0, norm_zero] at hsq
      have : ⟪a, b⟫ ^ 2 = 1 := by linarith
      have := abs_real_inner_le_norm a b; rw [ha, hb, mul_one] at this
      nlinarith [abs_nonneg ⟪a, b⟫]
    have hab' : a = b := by
      have : ‖a - b‖ ^ 2 = 0 := by rw [norm_sub_sq_real, ha, hb, h1]; ring
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    rw [minRot, h0, show psiVec 0 = 0 by simp [psiVec], rotate_zero, hab']
  · set σ := cross a b with hσ
    have hs : 0 < ‖σ‖ := norm_pos_iff.2 h0
    have hs1 : ‖σ‖ ≤ 1 := by
      have : ‖σ‖ ^ 2 ≤ 1 := by rw [hsq]; nlinarith [sq_nonneg ⟪a, b⟫]
      nlinarith [norm_nonneg σ]
    have hθ : ‖minRot a b‖ = Real.arcsin ‖σ‖ := norm_psiVec_eq σ
    have hθpos : 0 < Real.arcsin ‖σ‖ := Real.arcsin_pos.2 hs
    have hk : ‖minRot a b‖⁻¹ • minRot a b = ‖σ‖⁻¹ • σ := by
      rw [hθ, minRot, psiVec, smul_smul, div_eq_mul_inv, ← mul_assoc,
        inv_mul_cancel₀ hθpos.ne', one_mul]
    have hcos : Real.cos ‖minRot a b‖ = ⟪a, b⟫ := by
      rw [hθ, Real.cos_arcsin, hsq, show 1 - (1 - ⟪a, b⟫ ^ 2) = ⟪a, b⟫ ^ 2 by ring,
        Real.sqrt_sq hab]
    have hsin : Real.sin ‖minRot a b‖ = ‖σ‖ := by
      rw [hθ, Real.sin_arcsin (by linarith) hs1]
    rw [rotate_eq_rodr, hcos, hsin, hk, rodr, cross_smul_left, smul_smul, mul_inv_cancel₀ hs.ne',
      one_smul, hσ, cross_cross_unit ha, real_inner_smul_left, real_inner_comm a (cross a b),
      inner_cross_left,
      mul_zero, mul_zero, zero_smul, add_zero]
    abel

theorem inner_minRot_left (a b : E3) : ⟪minRot a b, a⟫ = 0 := by
  rw [minRot, psiVec, real_inner_smul_left, real_inner_comm, inner_cross_left, mul_zero]

theorem inner_rotate_ge (ω y : E3) : Real.cos ‖ω‖ * ‖y‖ ^ 2 ≤ ⟪rotate ω y, y⟫ := by
  by_cases h0 : ω = 0
  · rw [h0, rotate_zero, norm_zero, Real.cos_zero, one_mul, real_inner_self_eq_norm_sq]
  rw [rotate_eq_rodr, rodr, inner_add_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hz : ⟪cross (‖ω‖⁻¹ • ω) y, y⟫ = 0 := by
    rw [real_inner_comm]; exact inner_cross_right _ _
  rw [hz, mul_zero, add_zero]
  have h1 : 0 ≤ 1 - Real.cos ‖ω‖ := by linarith [Real.cos_le_one ‖ω‖]
  have h2 : 0 ≤ (1 - Real.cos ‖ω‖) * ⟪‖ω‖⁻¹ • ω, y⟫ * ⟪‖ω‖⁻¹ • ω, y⟫ := by
    rw [mul_assoc]; exact mul_nonneg h1 (mul_self_nonneg _)
  linarith

theorem norm_rotate_sub_le (ω y : E3) : ‖rotate ω y - y‖ ≤ ‖ω‖ * ‖y‖ := by
  have hsq : ‖rotate ω y - y‖ ^ 2 ≤ (‖ω‖ * ‖y‖) ^ 2 := by
    rw [norm_sub_sq_real, norm_rotate]
    have h1 := inner_rotate_ge ω y
    have h2 := Real.one_sub_sq_div_two_le_cos (x := ‖ω‖)
    nlinarith [sq_nonneg ‖y‖, sq_nonneg ‖ω‖]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq

end VisionTracking

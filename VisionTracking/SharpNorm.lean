import VisionTracking.Regularity
import VisionTracking.RateBound

/-!
# Sharp normalisation bounds

* `norm_nrm_sub_le_sharp`: `‖â - b̂‖ ≤ ‖a - b‖ / m` when both norms are at least `m`.
* `norm_cross_nrm_second_le`: `‖b̂ × (ĉ - 2 b̂ + â)‖ ≤ ‖c - 2b + a‖ / m
  + (‖c - b‖² + ‖b - a‖²) / m²`. The cross product removes the component of the
  second difference along `b̂`, which is the centripetal part. What is left is the
  part that needs angular acceleration, i.e. torque.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

theorem cross_add_right' (a x y : E3) : cross a (x + y) = cross a x + cross a y := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring

theorem cross_smul_right' (a x : E3) (r : ℝ) : cross a (r • x) = r • cross a x := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring

theorem cross_self' (a : E3) : cross a a = 0 := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring

theorem norm_nrm_sub_le_sharp {a b : E3} {m : ℝ} (hm : 0 < m) (ha : m ≤ ‖a‖) (hb : m ≤ ‖b‖) :
    ‖nrm a - nrm b‖ ≤ ‖a - b‖ / m := by
  have hA : 0 < ‖a‖ := hm.trans_le ha
  have hB : 0 < ‖b‖ := hm.trans_le hb
  have hn : ∀ x : E3, 0 < ‖x‖ → ‖nrm x‖ = 1 := fun x hx => by
    unfold nrm; rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx.ne']
  have hin : ⟪nrm a, nrm b⟫ = ⟪a, b⟫ / (‖a‖ * ‖b‖) := by
    unfold nrm; rw [real_inner_smul_left, real_inner_smul_right]; field_simp
  have h1 : ‖nrm a - nrm b‖ ^ 2 = 2 - 2 * (⟪a, b⟫ / (‖a‖ * ‖b‖)) := by
    rw [norm_sub_sq_real, hn a hA, hn b hB, hin]; ring
  have h2 : ‖a - b‖ ^ 2 = ‖a‖ ^ 2 - 2 * ⟪a, b⟫ + ‖b‖ ^ 2 := norm_sub_sq_real a b
  have key : ‖nrm a - nrm b‖ ^ 2 * (‖a‖ * ‖b‖) ≤ ‖a - b‖ ^ 2 := by
    rw [h1, h2]
    have : (2 - 2 * (⟪a, b⟫ / (‖a‖ * ‖b‖))) * (‖a‖ * ‖b‖) = 2 * (‖a‖ * ‖b‖) - 2 * ⟪a, b⟫ := by
      field_simp
    rw [this]; nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have hmm : m * m ≤ ‖a‖ * ‖b‖ := mul_le_mul ha hb hm.le hA.le
  rw [le_div_iff₀ hm, ← sq_le_sq₀ (by positivity) (norm_nonneg _), mul_pow]
  nlinarith [sq_nonneg ‖nrm a - nrm b‖]

theorem norm_cross_nrm_second_le {a b c : E3} {m : ℝ} (hm : 0 < m) (ha : m ≤ ‖a‖)
    (hb : m ≤ ‖b‖) (hc : m ≤ ‖c‖) :
    ‖cross (nrm b) (nrm c - 2 • nrm b + nrm a)‖ ≤
      ‖c - 2 • b + a‖ / m + (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / m ^ 2 := by
  have hA : 0 < ‖a‖ := hm.trans_le ha
  have hB : 0 < ‖b‖ := hm.trans_le hb
  have hC : 0 < ‖c‖ := hm.trans_le hc
  set Y := ‖b‖⁻¹ • (c - 2 • b + a) + (‖c‖⁻¹ - ‖b‖⁻¹) • (c - b) - (‖a‖⁻¹ - ‖b‖⁻¹) • (b - a)
    with hY
  have hX : nrm c - 2 • nrm b + nrm a = Y + (‖c‖⁻¹ - 2 * ‖b‖⁻¹ + ‖a‖⁻¹) • b := by
    rw [hY]; unfold nrm; module
  have hcr : cross (nrm b) (nrm c - 2 • nrm b + nrm a) = cross (nrm b) Y := by
    rw [hX, cross_add_right', cross_smul_right']
    have : cross (nrm b) b = 0 := by unfold nrm; rw [cross_smul_left, cross_self', smul_zero]
    rw [this, smul_zero, add_zero]
  rw [hcr]
  have hnb : ‖nrm b‖ = 1 := by unfold nrm; rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hB.ne']
  refine (norm_cross_le _ _).trans ?_
  rw [hnb, one_mul, hY]
  have hα : |‖c‖ - ‖b‖| ≤ ‖c - b‖ := abs_norm_sub_norm_le c b
  have hβ : |‖a‖ - ‖b‖| ≤ ‖b - a‖ := by rw [norm_sub_rev]; exact abs_norm_sub_norm_le a b
  have t1 : ‖‖b‖⁻¹ • (c - 2 • b + a)‖ ≤ ‖c - 2 • b + a‖ / m := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hm hb
  have t2 : ‖(‖c‖⁻¹ - ‖b‖⁻¹) • (c - b)‖ ≤ ‖c - b‖ ^ 2 / m ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs]; exact inv_sub_mul_le hm hc hb hα
  have t3 : ‖(‖a‖⁻¹ - ‖b‖⁻¹) • (b - a)‖ ≤ ‖b - a‖ ^ 2 / m ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs]; exact inv_sub_mul_le hm ha hb hβ
  have htri := (norm_sub_le _ _).trans (add_le_add (norm_add_le
    (‖b‖⁻¹ • (c - 2 • b + a)) ((‖c‖⁻¹ - ‖b‖⁻¹) • (c - b))) (le_refl ‖(‖a‖⁻¹ - ‖b‖⁻¹) • (b - a)‖))
  have : (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / m ^ 2 = ‖c - b‖ ^ 2 / m ^ 2 + ‖b - a‖ ^ 2 / m ^ 2 := by
    ring
  linarith

end VisionTracking

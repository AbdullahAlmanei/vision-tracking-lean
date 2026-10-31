import VisionTracking.AxisAngle

/-!
# Lipschitz bounds for the rotation vector

For a rotation of angle at most `π/2`, the axis-angle vector is
`psiVec σ = (arcsin ‖σ‖ / ‖σ‖) σ` with `σ = ½ Σ eᵢ × cᵢ`. On `‖σ‖ ≤ ρ < 1`:

* `norm_psiVec_le`: `‖psiVec σ‖ ≤ ‖σ‖ / √(1 - ρ²)`;
* `norm_psiVec_sub_le`: `‖psiVec σ - psiVec σ'‖ ≤ 3 ‖σ - σ'‖ / √(1 - ρ²)`;
* `norm_sigmaVec_sub_le`: `‖σ(r,s) - σ(r',s')‖ ≤ ‖r - r'‖ + ‖s - s'‖` for unit vectors.

Together these bound how fast body rates can change in terms of the second
differences of the frame vectors, which is what the torque budget needs.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

theorem arcsin_sub_le {x y ρ : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ ρ) (hρ : ρ < 1) :
    Real.arcsin y - Real.arcsin x ≤ (y - x) / √(1 - ρ ^ 2) := by
  have hs1 : 0 < √(1 - ρ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  rcases hxy.lt_or_eq with hlt | heq
  · obtain ⟨c, hc, hd⟩ := exists_hasDerivAt_eq_slope Real.arcsin
      (fun t => 1 / √(1 - t ^ 2)) hlt Real.continuous_arcsin.continuousOn
      (fun t ht => Real.hasDerivAt_arcsin (by linarith [ht.1] : (-1 : ℝ) < t).ne'
        (by linarith [ht.2] : t < 1).ne)
    have hyx : 0 < y - x := by linarith
    have hc2 : c ^ 2 ≤ ρ ^ 2 := by nlinarith [hc.1, hc.2]
    have hsc : √(1 - ρ ^ 2) ≤ √(1 - c ^ 2) := Real.sqrt_le_sqrt (by linarith)
    have hd' : 1 / √(1 - c ^ 2) = (Real.arcsin y - Real.arcsin x) / (y - x) := hd
    have heq' : Real.arcsin y - Real.arcsin x = 1 / √(1 - c ^ 2) * (y - x) := by
      rw [hd']; field_simp
    rw [heq']
    calc 1 / √(1 - c ^ 2) * (y - x) ≤ 1 / √(1 - ρ ^ 2) * (y - x) :=
          mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hs1 hsc) hyx.le
      _ = (y - x) / √(1 - ρ ^ 2) := by ring
  · rw [heq]; simp

theorem arcsin_div_mul (a : ℝ) : Real.arcsin a / a * a = Real.arcsin a := by
  rcases eq_or_ne a 0 with h | h
  · simp [h]
  · exact div_mul_cancel₀ _ h

theorem abs_arcsin_sub_le {x y ρ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxρ : x ≤ ρ) (hyρ : y ≤ ρ)
    (hρ : ρ < 1) : |Real.arcsin x - Real.arcsin y| ≤ |x - y| / √(1 - ρ ^ 2) := by
  rcases le_total x y with h | h
  · rw [abs_sub_comm (Real.arcsin x), abs_sub_comm x y,
      abs_of_nonneg (by linarith [Real.arcsin_le_arcsin h]),
      abs_of_nonneg (by linarith : 0 ≤ y - x)]
    exact arcsin_sub_le hx h hyρ hρ
  · rw [abs_of_nonneg (by linarith [Real.arcsin_le_arcsin h]),
      abs_of_nonneg (by linarith : 0 ≤ x - y)]
    exact arcsin_sub_le hy h hxρ hρ

theorem arcsin_div_le {a ρ : ℝ} (ha : 0 ≤ a) (haρ : a ≤ ρ) (hρ : ρ < 1) :
    0 ≤ Real.arcsin a / a ∧ Real.arcsin a / a ≤ 1 / √(1 - ρ ^ 2) := by
  have hs1 : 0 < √(1 - ρ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  refine ⟨div_nonneg (Real.arcsin_nonneg.2 ha) ha, ?_⟩
  rcases ha.lt_or_eq with hpos | h0
  · have := arcsin_sub_le le_rfl ha haρ hρ
    rw [Real.arcsin_zero, sub_zero, sub_zero] at this
    rw [div_le_iff₀ hpos]; rw [div_eq_mul_one_div] at this; linarith
  · rw [← h0]; simp

theorem norm_psiVec_le {σ : E3} {ρ : ℝ} (h : ‖σ‖ ≤ ρ) (hρ : ρ < 1) :
    ‖psiVec σ‖ ≤ ‖σ‖ / √(1 - ρ ^ 2) := by
  obtain ⟨h0, h1⟩ := arcsin_div_le (norm_nonneg σ) h hρ
  rw [psiVec, norm_smul, Real.norm_of_nonneg h0, div_eq_mul_one_div ‖σ‖, mul_comm ‖σ‖]
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg σ)

theorem norm_psiVec_sub_le {σ σ' : E3} {ρ : ℝ} (h : ‖σ‖ ≤ ρ) (h' : ‖σ'‖ ≤ ρ) (hρ : ρ < 1) :
    ‖psiVec σ - psiVec σ'‖ ≤ 3 * ‖σ - σ'‖ / √(1 - ρ ^ 2) := by
  set a := ‖σ‖ with ha
  set a' := ‖σ'‖ with ha'
  have hs1 : 0 < √(1 - ρ ^ 2) := Real.sqrt_pos.2 (by nlinarith [norm_nonneg σ])
  obtain ⟨g0, g1⟩ := arcsin_div_le (norm_nonneg σ) h hρ
  have hsplit : psiVec σ - psiVec σ' = (Real.arcsin a / a) • (σ - σ')
      + (Real.arcsin a / a - Real.arcsin a' / a') • σ' := by
    rw [psiVec, psiVec]; module
  have hd : |a - a'| ≤ ‖σ - σ'‖ := abs_norm_sub_norm_le σ σ'
  have hasin := abs_arcsin_sub_le (norm_nonneg σ) (norm_nonneg σ') h h' hρ
  have key : ‖(Real.arcsin a / a - Real.arcsin a' / a') • σ'‖
      ≤ 2 * ‖σ - σ'‖ / √(1 - ρ ^ 2) := by
    have hk : (Real.arcsin a / a - Real.arcsin a' / a') * a'
        = (Real.arcsin a - Real.arcsin a') - Real.arcsin a / a * (a - a') := by
      rw [sub_mul, arcsin_div_mul a', mul_sub, arcsin_div_mul a]; ring
    calc ‖(Real.arcsin a / a - Real.arcsin a' / a') • σ'‖
        = |(Real.arcsin a / a - Real.arcsin a' / a') * a'| := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg σ')]
      _ = |(Real.arcsin a - Real.arcsin a') - Real.arcsin a / a * (a - a')| := by rw [hk]
      _ ≤ 2 * ‖σ - σ'‖ / √(1 - ρ ^ 2) := ?_
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg g0]
    have e1 : |a - a'| / √(1 - ρ ^ 2) ≤ ‖σ - σ'‖ / √(1 - ρ ^ 2) :=
      div_le_div_of_nonneg_right hd hs1.le
    have e2 : Real.arcsin a / a * |a - a'| ≤ ‖σ - σ'‖ / √(1 - ρ ^ 2) := by
      calc Real.arcsin a / a * |a - a'| ≤ 1 / √(1 - ρ ^ 2) * ‖σ - σ'‖ :=
            mul_le_mul g1 hd (abs_nonneg _) (by positivity)
        _ = ‖σ - σ'‖ / √(1 - ρ ^ 2) := by ring
    have : 2 * ‖σ - σ'‖ / √(1 - ρ ^ 2) = ‖σ - σ'‖ / √(1 - ρ ^ 2) + ‖σ - σ'‖ / √(1 - ρ ^ 2) := by
      ring
    linarith
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have e3 : ‖(Real.arcsin a / a) • (σ - σ')‖ ≤ ‖σ - σ'‖ / √(1 - ρ ^ 2) := by
    rw [norm_smul, Real.norm_of_nonneg g0]
    calc Real.arcsin a / a * ‖σ - σ'‖ ≤ 1 / √(1 - ρ ^ 2) * ‖σ - σ'‖ :=
          mul_le_mul_of_nonneg_right g1 (norm_nonneg _)
      _ = ‖σ - σ'‖ / √(1 - ρ ^ 2) := by ring
  have : 3 * ‖σ - σ'‖ / √(1 - ρ ^ 2)
      = ‖σ - σ'‖ / √(1 - ρ ^ 2) + 2 * ‖σ - σ'‖ / √(1 - ρ ^ 2) := by ring
  linarith

theorem norm_cross_le (x y : E3) : ‖cross x y‖ ≤ ‖x‖ * ‖y‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), norm_cross_sq, mul_pow]
  nlinarith [sq_nonneg ⟪x, y⟫]

theorem sigmaVec_sub (r s r' s' : E3) :
    sigmaVec r s - sigmaVec r' s' = (1 / 2 : ℝ) • (cross ex (r - r') + cross ey (s - s')
      + cross up (cross (r - r') s + cross r' (s - s'))) := by
  obtain ⟨g0, g1, g2⟩ := sigmaVec_ofLp r s
  obtain ⟨k0, k1, k2⟩ := sigmaVec_ofLp r' s'
  ext j; fin_cases j <;>
    simp [g0, g1, g2, k0, k1, k2, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two, ex, ey,
      up] <;> ring

theorem norm_sigmaVec_sub_le {r s r' s' : E3} (hs : ‖s‖ = 1) (hr' : ‖r'‖ = 1) :
    ‖sigmaVec r s - sigmaVec r' s'‖ ≤ ‖r - r'‖ + ‖s - s'‖ := by
  have hex : ‖ex‖ = 1 := by simp [ex]
  have hey : ‖ey‖ = 1 := by simp [ey]
  rw [sigmaVec_sub, norm_smul]
  have b1 := norm_cross_le ex (r - r')
  have b2 := norm_cross_le ey (s - s')
  have b3 := norm_cross_le up (cross (r - r') s + cross r' (s - s'))
  have b4 := norm_cross_le (r - r') s
  have b5 := norm_cross_le r' (s - s')
  have b6 := norm_add_le (cross (r - r') s) (cross r' (s - s'))
  have b7 := norm_add_le (cross ex (r - r') + cross ey (s - s'))
    (cross up (cross (r - r') s + cross r' (s - s')))
  have b8 := norm_add_le (cross ex (r - r')) (cross ey (s - s'))
  have hup : ‖up‖ = 1 := by simp [up]
  rw [hex] at b1; rw [hey] at b2; rw [hup] at b3; rw [hs] at b4; rw [hr'] at b5
  norm_num
  linarith

end VisionTracking

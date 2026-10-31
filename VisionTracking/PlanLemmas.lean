import VisionTracking.TargetBounds
import VisionTracking.RateBound

/-!
# Generic lemmas for assembling the overhead plan
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

/-- The drag map `x ↦ ‖x‖ x` is Lipschitz with constant `‖a‖ + ‖b‖`. -/
theorem norm_dragMap_sub_le (a b : E3) : ‖‖a‖ • a - ‖b‖ • b‖ ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := by
  have hsplit : ‖a‖ • a - ‖b‖ • b = ‖a‖ • (a - b) + (‖a‖ - ‖b‖) • b := by module
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (norm_nonneg a), Real.norm_eq_abs]
  have := abs_norm_sub_norm_le a b
  nlinarith [norm_nonneg b, norm_nonneg (a - b), abs_nonneg (‖a‖ - ‖b‖)]

/-- Second difference of the norm. -/
theorem abs_norm_second_le {a b c : E3} (hb : b ≠ 0) :
    |‖c‖ - 2 * ‖b‖ + ‖a‖| ≤ ‖c - 2 • b + a‖ + (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / (2 * ‖b‖) := by
  have hB : 0 < ‖b‖ := norm_pos_iff.2 hb
  have h1 := norm_add_le_quad (u := c - b) hb
  have h2 := norm_add_le_quad (u := a - b) hb
  rw [add_sub_cancel] at h1 h2
  rw [norm_sub_rev a b] at h2
  have h3 : (⟪b, c - b⟫ + ⟪b, a - b⟫) / ‖b‖ ≤ ‖c - 2 • b + a‖ := by
    rw [← inner_add_right, div_le_iff₀ hB]
    have : c - b + (a - b) = c - 2 • b + a := by module
    rw [this]
    have := real_inner_le_norm b (c - 2 • b + a); linarith
  have e1 : ⟪b, c - b⟫ / ‖b‖ + ⟪b, a - b⟫ / ‖b‖ = (⟪b, c - b⟫ + ⟪b, a - b⟫) / ‖b‖ := by ring
  have e2 : ‖c - b‖ ^ 2 / (2 * ‖b‖) + ‖b - a‖ ^ 2 / (2 * ‖b‖)
      = (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / (2 * ‖b‖) := by ring
  have hlo : -‖c - 2 • b + a‖ ≤ ‖c‖ - 2 * ‖b‖ + ‖a‖ := by
    have k1 : ‖c + a‖ ≤ ‖c‖ + ‖a‖ := norm_add_le c a
    have k2 : ‖(2 : ℝ) • b‖ ≤ ‖c + a‖ + ‖c - 2 • b + a‖ := by
      have : (2 : ℝ) • b = (c + a) - (c - 2 • b + a) := by module
      rw [this]; exact norm_sub_le _ _
    rw [norm_smul, Real.norm_ofNat] at k2
    linarith
  have hpos : 0 ≤ (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / (2 * ‖b‖) := by positivity
  rw [abs_le]; constructor <;> linarith

/-- Second difference of the drag map. -/
theorem norm_dragMap_second_le {a b c : E3} (hb : b ≠ 0) :
    ‖‖c‖ • c - 2 • (‖b‖ • b) + ‖a‖ • a‖ ≤
      2 * ‖b‖ * ‖c - 2 • b + a‖ + 2 * (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) := by
  have hB : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hsplit : ‖c‖ • c - 2 • (‖b‖ • b) + ‖a‖ • a = ‖b‖ • (c - 2 • b + a)
      + (‖c‖ - 2 * ‖b‖ + ‖a‖) • b + (‖c‖ - ‖b‖) • (c - b) - (‖a‖ - ‖b‖) • (b - a) := by
    module
  have hS := abs_norm_second_le (a := a) (c := c) hb
  have hα : |‖c‖ - ‖b‖| ≤ ‖c - b‖ := abs_norm_sub_norm_le c b
  have hβ : |‖a‖ - ‖b‖| ≤ ‖b - a‖ := by rw [norm_sub_rev]; exact abs_norm_sub_norm_le a b
  rw [hsplit]
  have t1 : ‖‖b‖ • (c - 2 • b + a)‖ = ‖b‖ * ‖c - 2 • b + a‖ := by
    rw [norm_smul, Real.norm_of_nonneg hB.le]
  have t2 : ‖(‖c‖ - 2 * ‖b‖ + ‖a‖) • b‖ ≤ ‖b‖ * ‖c - 2 • b + a‖
      + (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_right hS hB.le
    have e : (‖c - 2 • b + a‖ + (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / (2 * ‖b‖)) * ‖b‖
        = ‖b‖ * ‖c - 2 • b + a‖ + (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / 2 := by field_simp
    linarith
  have t3 : ‖(‖c‖ - ‖b‖) • (c - b)‖ ≤ ‖c - b‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, sq]; exact mul_le_mul_of_nonneg_right hα (norm_nonneg _)
  have t4 : ‖(‖a‖ - ‖b‖) • (b - a)‖ ≤ ‖b - a‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, sq]; exact mul_le_mul_of_nonneg_right hβ (norm_nonneg _)
  have htri : ‖‖b‖ • (c - 2 • b + a) + (‖c‖ - 2 * ‖b‖ + ‖a‖) • b + (‖c‖ - ‖b‖) • (c - b)
      - (‖a‖ - ‖b‖) • (b - a)‖ ≤ ‖‖b‖ • (c - 2 • b + a)‖ + ‖(‖c‖ - 2 * ‖b‖ + ‖a‖) • b‖
        + ‖(‖c‖ - ‖b‖) • (c - b)‖ + ‖(‖a‖ - ‖b‖) • (b - a)‖ :=
    (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  have hnn : 0 ≤ (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / 2 := by positivity
  linarith

/-- A perturbation of size `‖e‖ < ‖x‖` turns `x` by at most `arcsin (‖e‖/‖x‖)`. -/
theorem angle_add_le_arcsin {x e : E3} (h : ‖e‖ < ‖x‖) :
    angle x (x + e) ≤ Real.arcsin (‖e‖ / ‖x‖) := by
  have hx : 0 < ‖x‖ := (norm_nonneg e).trans_lt h
  set y := x + e with hy
  have hyx : y - x = e := by rw [hy]; abel
  have hypos : 0 < ‖y‖ := by
    have := norm_sub_norm_le x (-e)
    rw [sub_neg_eq_add, norm_neg] at this; linarith
  have hin : 0 < ⟪x, y⟫ := by
    rw [hy, inner_add_right, real_inner_self_eq_norm_sq]
    have := neg_abs_le ⟪x, e⟫
    have := abs_real_inner_le_norm x e
    nlinarith
  set θ := angle x y with hθ
  have hcos : Real.cos θ = ⟪x, y⟫ / (‖x‖ * ‖y‖) := cos_angle x y
  have hθ0 : 0 ≤ θ := angle_nonneg x y
  have hθ1 : θ ≤ π / 2 := by
    by_contra hc
    have hneg : Real.cos θ < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt (lt_of_not_ge hc) (by linarith [angle_le_pi x y,
        Real.pi_pos])
    rw [hcos] at hneg
    have : 0 < ⟪x, y⟫ / (‖x‖ * ‖y‖) := div_pos hin (mul_pos hx hypos)
    linarith
  -- Lagrange: ‖x‖²‖y‖² - ⟪x,y⟫² ≤ ‖x - y‖²‖y‖².
  have hlag : ‖x‖ ^ 2 * ‖y‖ ^ 2 - ⟪x, y⟫ ^ 2 ≤ ‖e‖ ^ 2 * ‖y‖ ^ 2 := by
    have hxy : x = (x - y) + y := by abel
    have e1 : ‖x‖ ^ 2 = ‖x - y‖ ^ 2 + 2 * ⟪x - y, y⟫ + ‖y‖ ^ 2 := by
      conv_lhs => rw [hxy]
      rw [norm_add_sq_real]
    have e2 : ⟪x, y⟫ = ⟪x - y, y⟫ + ‖y‖ ^ 2 := by
      conv_lhs => rw [hxy]
      rw [inner_add_left, real_inner_self_eq_norm_sq]
    have e3 : ‖x - y‖ = ‖e‖ := by rw [norm_sub_rev, hyx]
    rw [e1, e2, e3]
    nlinarith [sq_nonneg ⟪x - y, y⟫]
  have hsin : Real.sin θ ≤ ‖e‖ / ‖x‖ := by
    rw [Real.sin_eq_sqrt_one_sub_cos_sq hθ0 (by linarith [Real.pi_pos]), hcos]
    rw [Real.sqrt_le_left (by positivity)]
    rw [div_pow, mul_pow, one_sub_div (by positivity), div_le_iff₀ (by positivity), div_pow]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖y‖]
  calc θ = Real.arcsin (Real.sin θ) := (Real.arcsin_sin (by linarith) hθ1).symm
    _ ≤ Real.arcsin (‖e‖ / ‖x‖) := Real.arcsin_le_arcsin hsin

/-- Tilt of a thrust vector with positive vertical component. -/
theorem angle_up_eq_arctan {T : E3} (hz : 0 < ⟪T, up⟫) :
    angle T up = Real.arctan (‖horiz T‖ / ⟪T, up⟫) := by
  have hT : 0 < ‖T‖ := by
    have := real_inner_le_norm T up; rw [norm_up', mul_one] at this; linarith
  set θ := angle T up
  have hcos : Real.cos θ = ⟪T, up⟫ / ‖T‖ := by rw [cos_angle, norm_up', mul_one]
  have hθ0 : 0 ≤ θ := angle_nonneg T up
  have hcpos : 0 < Real.cos θ := by rw [hcos]; positivity
  have hθ1 : θ < π / 2 := by
    by_contra hc
    have := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_gt hc)
      (by linarith [angle_le_pi T up, Real.pi_pos])
    linarith
  have hsin : Real.sin θ = ‖horiz T‖ / ‖T‖ := by
    rw [Real.sin_eq_sqrt_one_sub_cos_sq hθ0 (by linarith [Real.pi_pos]), hcos]
    have hh := norm_horiz_sq T
    rw [show 1 - (⟪T, up⟫ / ‖T‖) ^ 2 = (‖horiz T‖ / ‖T‖) ^ 2 by rw [div_pow, div_pow, hh]; field_simp]
    exact Real.sqrt_sq (by positivity)
  rw [← Real.arctan_tan (by linarith) hθ1, Real.tan_eq_sin_div_cos, hsin, hcos]
  field_simp

/-- Chord versus angle for unit vectors. -/
theorem angle_le_chord {x y : E3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    angle x y ≤ π / 2 * ‖x - y‖ := by
  set θ := angle x y
  have hθ0 : 0 ≤ θ := angle_nonneg x y
  have hθπ : θ ≤ π := angle_le_pi x y
  have hcos : Real.cos θ = ⟪x, y⟫ := by rw [cos_angle, hx, hy, mul_one, div_one]
  have hd : ‖x - y‖ ^ 2 = 2 - 2 * Real.cos θ := by
    rw [norm_sub_sq_real, hx, hy, hcos]; ring
  have hhalf : 1 - Real.cos θ = 2 * Real.sin (θ / 2) ^ 2 := by
    have := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at this
    have := Real.sin_sq_add_cos_sq (θ / 2)
    linarith
  have hsin : 2 / π * (θ / 2) ≤ Real.sin (θ / 2) := Real.mul_le_sin (by linarith) (by linarith)
  have hpi := Real.pi_pos
  have hs0 : 0 ≤ 2 / π * (θ / 2) := by positivity
  have hchord : 2 * (2 / π * (θ / 2)) ≤ ‖x - y‖ := by
    rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), hd]
    have := pow_le_pow_left₀ hs0 hsin 2
    nlinarith
  have : θ = π / 2 * (2 * (2 / π * (θ / 2))) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hchord (by positivity)

/-- Discrete product rule for the cross product. -/
theorem cross_second (a a' a'' b b' b'' : E3) :
    cross a'' b'' - 2 • cross a' b' + cross a b =
      cross (a'' - 2 • a' + a) b'' + 2 • cross (a' - a) (b'' - b') + cross a (b'' - 2 • b' + b) := by
  ext j; fin_cases j <;> simp [cross, crossProduct, two_smul] <;> ring

theorem cross_sub_cross (a a' b b' : E3) :
    cross a' b' - cross a b = cross (a' - a) b' + cross a (b' - b) := by
  ext j; fin_cases j <;> simp [cross, crossProduct] <;> ring

end VisionTracking

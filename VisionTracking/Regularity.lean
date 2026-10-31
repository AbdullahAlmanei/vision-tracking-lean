import VisionTracking.Frame

/-!
# Regularity of normalisation

`nrm x = x / ‖x‖`. On vectors of length at least `m`:

* `norm_nrm_sub_le`: `‖nrm a - nrm b‖ ≤ 2 ‖a - b‖ / m`;
* `norm_nrm_second_le`: `‖nrm c - 2 nrm b + nrm a‖ ≤ 2 ‖c - 2b + a‖ / m
  + 3 (‖c - b‖² + ‖b - a‖²) / m²`.

These control how fast the thrust direction turns (first differences: body rate)
and how fast that turning changes (second differences: angular acceleration, hence
torque).
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

/-- Normalisation. -/
noncomputable def nrm (x : E3) : E3 := ‖x‖⁻¹ • x

theorem norm_nrm_sub_le {a b : E3} {m : ℝ} (hm : 0 < m) (ha : m ≤ ‖a‖) :
    ‖nrm a - nrm b‖ ≤ 2 * ‖a - b‖ / m := by
  have hA : 0 < ‖a‖ := hm.trans_le ha
  have hab := norm_nonneg (a - b)
  have hdiv : 2 * ‖a - b‖ / ‖a‖ ≤ 2 * ‖a - b‖ / m :=
    div_le_div_of_nonneg_left (by positivity) hm ha
  refine le_trans ?_ hdiv
  by_cases hb0 : b = 0
  · have : ‖nrm a‖ = 1 := by
      unfold nrm; rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hA.ne']
    have hn0 : nrm 0 = 0 := by simp [nrm]
    rw [hb0, hn0, sub_zero, this, sub_zero, le_div_iff₀ hA]
    linarith
  · have hB : 0 < ‖b‖ := norm_pos_iff.2 hb0
    have hsplit : nrm a - nrm b = ‖a‖⁻¹ • (a - b) + (‖a‖⁻¹ - ‖b‖⁻¹) • b := by
      unfold nrm; module
    have h2 : ‖(‖a‖⁻¹ - ‖b‖⁻¹) • b‖ ≤ ‖a - b‖ / ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have : (‖a‖⁻¹ - ‖b‖⁻¹) * ‖b‖ = (‖b‖ - ‖a‖) / ‖a‖ := by field_simp
      rw [← abs_of_pos hB, ← abs_mul, abs_of_pos hB, this, abs_div, abs_of_pos hA]
      exact div_le_div_of_nonneg_right
        (by rw [abs_sub_comm]; exact abs_norm_sub_norm_le a b) hA.le
    rw [hsplit]
    calc ‖‖a‖⁻¹ • (a - b) + (‖a‖⁻¹ - ‖b‖⁻¹) • b‖
        ≤ ‖‖a‖⁻¹ • (a - b)‖ + ‖(‖a‖⁻¹ - ‖b‖⁻¹) • b‖ := norm_add_le _ _
      _ ≤ ‖a - b‖ / ‖a‖ + ‖a - b‖ / ‖a‖ := by
          gcongr
          rw [norm_smul, norm_inv, norm_norm, inv_mul_eq_div]
      _ = 2 * ‖a - b‖ / ‖a‖ := by ring

/-- Quadratic upper bound for the norm: `‖b + u‖ ≤ ‖b‖ + ⟪b,u⟫/‖b‖ + ‖u‖²/(2‖b‖)`. -/
theorem norm_add_le_quad {b u : E3} (hb : b ≠ 0) :
    ‖b + u‖ ≤ ‖b‖ + ⟪b, u⟫ / ‖b‖ + ‖u‖ ^ 2 / (2 * ‖b‖) := by
  have hB : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hbu : -(‖b‖ * ‖u‖) ≤ ⟪b, u⟫ := by
    have := abs_real_inner_le_norm b u; rw [abs_le] at this; linarith
  have hsq : ‖b + u‖ ^ 2 = ‖b‖ ^ 2 + 2 * ⟪b, u⟫ + ‖u‖ ^ 2 := by rw [norm_add_sq_real]
  generalize ‖b + u‖ = N at hsq ⊢
  generalize ⟪b, u⟫ = I at hbu hsq ⊢
  generalize ‖u‖ = U at hbu hsq ⊢
  generalize ‖b‖ = B at hB hbu hsq ⊢
  have hX : B + I / B + U ^ 2 / (2 * B) = (2 * B ^ 2 + 2 * I + U ^ 2) / (2 * B) := by
    field_simp
  have hXpos : 0 < B + I / B + U ^ 2 / (2 * B) := by
    rw [hX]; apply div_pos _ (by positivity); nlinarith [sq_nonneg (B - U)]
  have hdiff : (B + I / B + U ^ 2 / (2 * B)) ^ 2 - N ^ 2 = (I / B + U ^ 2 / (2 * B)) ^ 2 := by
    rw [hsq]; field_simp; ring
  rcases le_or_gt N 0 with hN | hN
  · linarith
  · rw [← sq_le_sq₀ hN.le hXpos.le]; nlinarith [sq_nonneg (I / B + U ^ 2 / (2 * B))]

/-- The scalar core of the second-difference bound. -/
theorem second_scalar {A B Cn m U W Dn : ℝ} (hm : 0 < m) (hA : m ≤ A) (hB : m ≤ B)
    (hC : m ≤ Cn) (hU : |Cn - B| ≤ U) (hW : |A - B| ≤ W)
    (hS : |Cn - B + (A - B)| ≤ Dn + (U ^ 2 + W ^ 2) / (2 * m)) :
    |(Cn⁻¹ - 2 * B⁻¹ + A⁻¹) * B| ≤ Dn / m + (U ^ 2 + W ^ 2) / (2 * m ^ 2) + U ^ 2 / m ^ 2
      + W ^ 2 / m ^ 2 := by
  have hA0 : 0 < A := hm.trans_le hA
  have hB0 : 0 < B := hm.trans_le hB
  have hC0 : 0 < Cn := hm.trans_le hC
  have hexpr : (Cn⁻¹ - 2 * B⁻¹ + A⁻¹) * B = -(Cn - B + (A - B)) / B
      + (Cn - B) ^ 2 / (B * Cn) + (A - B) ^ 2 / (B * A) := by
    field_simp; ring
  rw [hexpr]
  have e1 : |-(Cn - B + (A - B)) / B| ≤ Dn / m + (U ^ 2 + W ^ 2) / (2 * m ^ 2) := by
    rw [abs_div, abs_neg, abs_of_pos hB0]
    calc |Cn - B + (A - B)| / B ≤ |Cn - B + (A - B)| / m :=
          div_le_div_of_nonneg_left (abs_nonneg _) hm hB
      _ ≤ (Dn + (U ^ 2 + W ^ 2) / (2 * m)) / m := div_le_div_of_nonneg_right hS hm.le
      _ = Dn / m + (U ^ 2 + W ^ 2) / (2 * m ^ 2) := by field_simp
  have sqb : ∀ {x y z : ℝ}, |x| ≤ y → m ≤ z → x ^ 2 / (B * z) ≤ y ^ 2 / m ^ 2 := by
    intro x y z hxy hz
    have hz0 : 0 < z := hm.trans_le hz
    have h1 : x ^ 2 ≤ y ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hxy 2
    rw [div_le_div_iff₀ (mul_pos hB0 hz0) (by positivity)]
    have h2 : m ^ 2 ≤ B * z := by nlinarith
    nlinarith [sq_nonneg x, sq_nonneg y]
  have e2 : |(Cn - B) ^ 2 / (B * Cn)| ≤ U ^ 2 / m ^ 2 := by
    rw [abs_of_nonneg (by positivity)]; exact sqb hU hC
  have e3 : |(A - B) ^ 2 / (B * A)| ≤ W ^ 2 / m ^ 2 := by
    rw [abs_of_nonneg (by positivity)]; exact sqb hW hA
  calc |-(Cn - B + (A - B)) / B + (Cn - B) ^ 2 / (B * Cn) + (A - B) ^ 2 / (B * A)|
      ≤ |-(Cn - B + (A - B)) / B| + |(Cn - B) ^ 2 / (B * Cn)| + |(A - B) ^ 2 / (B * A)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

/-- `|z⁻¹ - B⁻¹| · ‖u‖ ≤ ‖u‖² / m²` when `|z - B| ≤ ‖u‖` and `z, B ≥ m`. -/
theorem inv_sub_mul_le {z B m U : ℝ} (hm : 0 < m) (hz : m ≤ z) (hB : m ≤ B)
    (hU : |z - B| ≤ U) : |z⁻¹ - B⁻¹| * U ≤ U ^ 2 / m ^ 2 := by
  have hz0 : 0 < z := hm.trans_le hz
  have hB0 : 0 < B := hm.trans_le hB
  have hU0 : 0 ≤ U := (abs_nonneg _).trans hU
  rw [show z⁻¹ - B⁻¹ = (B - z) / (B * z) by field_simp, abs_div, abs_of_pos (mul_pos hB0 hz0),
    abs_sub_comm, div_mul_eq_mul_div, div_le_div_iff₀ (mul_pos hB0 hz0) (by positivity)]
  have h2 : m ^ 2 ≤ B * z := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hU hU0, abs_nonneg (z - B)]

theorem norm_nrm_second_le {a b c : E3} {m : ℝ} (hm : 0 < m) (ha : m ≤ ‖a‖)
    (hb : m ≤ ‖b‖) (hc : m ≤ ‖c‖) :
    ‖nrm c - 2 • nrm b + nrm a‖ ≤
      2 * ‖c - 2 • b + a‖ / m + 3 * (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / m ^ 2 := by
  have hB : 0 < ‖b‖ := hm.trans_le hb
  have hb0 : b ≠ 0 := norm_pos_iff.1 hB
  have hsplit : nrm c - 2 • nrm b + nrm a = ‖b‖⁻¹ • (c - 2 • b + a)
      + (‖c‖⁻¹ - ‖b‖⁻¹) • (c - b) - (‖a‖⁻¹ - ‖b‖⁻¹) • (b - a)
      + (‖c‖⁻¹ - 2 * ‖b‖⁻¹ + ‖a‖⁻¹) • b := by
    unfold nrm; module
  have hα : |‖c‖ - ‖b‖| ≤ ‖c - b‖ := abs_norm_sub_norm_le c b
  have hβ : |‖a‖ - ‖b‖| ≤ ‖b - a‖ := by rw [norm_sub_rev]; exact abs_norm_sub_norm_le a b
  -- The second difference of the norms.
  have hup : ‖c‖ - ‖b‖ + (‖a‖ - ‖b‖) ≤
      ‖c - 2 • b + a‖ + (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / (2 * m) := by
    have h1 := norm_add_le_quad (u := c - b) hb0
    have h2 := norm_add_le_quad (u := a - b) hb0
    rw [add_sub_cancel] at h1 h2
    rw [norm_sub_rev a b] at h2
    have h3 : (⟪b, c - b⟫ + ⟪b, a - b⟫) / ‖b‖ ≤ ‖c - 2 • b + a‖ := by
      rw [← inner_add_right, div_le_iff₀ hB]
      have : c - b + (a - b) = c - 2 • b + a := by module
      rw [this]
      have := real_inner_le_norm b (c - 2 • b + a); linarith
    have h4 : (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / (2 * ‖b‖) ≤
        (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / (2 * m) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have e1 : ⟪b, c - b⟫ / ‖b‖ + ⟪b, a - b⟫ / ‖b‖ = (⟪b, c - b⟫ + ⟪b, a - b⟫) / ‖b‖ := by ring
    have e2 : ‖c - b‖ ^ 2 / (2 * ‖b‖) + ‖b - a‖ ^ 2 / (2 * ‖b‖)
        = (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / (2 * ‖b‖) := by ring
    linarith
  have hlo : -‖c - 2 • b + a‖ ≤ ‖c‖ - ‖b‖ + (‖a‖ - ‖b‖) := by
    have h1 : ‖c + a‖ ≤ ‖c‖ + ‖a‖ := norm_add_le c a
    have h2 : ‖(2 : ℝ) • b‖ ≤ ‖c + a‖ + ‖c - 2 • b + a‖ := by
      have : (2 : ℝ) • b = (c + a) - (c - 2 • b + a) := by module
      rw [this]; exact norm_sub_le _ _
    rw [norm_smul, Real.norm_ofNat] at h2
    linarith
  have hS : |‖c‖ - ‖b‖ + (‖a‖ - ‖b‖)| ≤
      ‖c - 2 • b + a‖ + (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / (2 * m) := by
    rw [abs_le]; constructor
    · have : 0 ≤ (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / (2 * m) := by positivity
      linarith
    · exact hup
  have t1 : ‖‖b‖⁻¹ • (c - 2 • b + a)‖ ≤ ‖c - 2 • b + a‖ / m := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hm hb
  have t2 : ‖(‖c‖⁻¹ - ‖b‖⁻¹) • (c - b)‖ ≤ ‖c - b‖ ^ 2 / m ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs]; exact inv_sub_mul_le hm hc hb hα
  have t3 : ‖(‖a‖⁻¹ - ‖b‖⁻¹) • (b - a)‖ ≤ ‖b - a‖ ^ 2 / m ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs]; exact inv_sub_mul_le hm ha hb hβ
  have t4 : ‖(‖c‖⁻¹ - 2 * ‖b‖⁻¹ + ‖a‖⁻¹) • b‖ ≤ ‖c - 2 • b + a‖ / m
      + (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / (2 * m ^ 2) + ‖c - b‖ ^ 2 / m ^ 2
      + ‖b - a‖ ^ 2 / m ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, ← abs_of_pos hB, ← abs_mul, abs_of_pos hB]
    exact second_scalar hm ha hb hc hα hβ hS
  rw [hsplit]
  have htri : ‖‖b‖⁻¹ • (c - 2 • b + a) + (‖c‖⁻¹ - ‖b‖⁻¹) • (c - b)
      - (‖a‖⁻¹ - ‖b‖⁻¹) • (b - a) + (‖c‖⁻¹ - 2 * ‖b‖⁻¹ + ‖a‖⁻¹) • b‖
      ≤ ‖‖b‖⁻¹ • (c - 2 • b + a)‖ + ‖(‖c‖⁻¹ - ‖b‖⁻¹) • (c - b)‖
        + ‖(‖a‖⁻¹ - ‖b‖⁻¹) • (b - a)‖ + ‖(‖c‖⁻¹ - 2 * ‖b‖⁻¹ + ‖a‖⁻¹) • b‖ :=
    (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  have hfin : 2 * ‖c - 2 • b + a‖ / m + 3 * (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / m ^ 2
      - (‖c - 2 • b + a‖ / m + ‖c - b‖ ^ 2 / m ^ 2 + ‖b - a‖ ^ 2 / m ^ 2
        + (‖c - 2 • b + a‖ / m + (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / (2 * m ^ 2)
          + ‖c - b‖ ^ 2 / m ^ 2 + ‖b - a‖ ^ 2 / m ^ 2))
      = (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / (2 * m ^ 2) := by field_simp; ring
  have hnn : 0 ≤ (‖c - b‖ ^ 2 + ‖b - a‖ ^ 2) / (2 * m ^ 2) := by positivity
  linarith

/-! ## The downhill body axis -/

/-- The unnormalised rotor-plane part of straight down: `-e₃ + ⟪b, e₃⟫ b`. -/
noncomputable def downhillRaw (b : E3) : E3 := -up + ⟪b, up⟫ • b

/-- The unit body axis in the rotor plane pointing straight down. -/
noncomputable def downhill (b : E3) : E3 := nrm (downhillRaw b)

theorem norm_up' : ‖up‖ = 1 := by simp [up]

theorem inner_downhillRaw_self {b : E3} (hb : ‖b‖ = 1) : ⟪downhillRaw b, b⟫ = 0 := by
  have hbb : ⟪b, b⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hb]; norm_num
  rw [downhillRaw, inner_add_left, inner_neg_left, real_inner_smul_left, hbb, real_inner_comm]
  ring

theorem norm_downhillRaw_sq {b : E3} (hb : ‖b‖ = 1) : ‖downhillRaw b‖ ^ 2 = 1 - ⟪b, up⟫ ^ 2 := by
  have hbb : ⟪b, b⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hb]; norm_num
  have huu : ⟪up, up⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_up']; norm_num
  rw [← real_inner_self_eq_norm_sq, downhillRaw]
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
    real_inner_smul_left, real_inner_smul_right, hbb, huu]
  rw [real_inner_comm up b]; ring

theorem downhill_unit {b : E3} (hraw : downhillRaw b ≠ 0) : ‖downhill b‖ = 1 := by
  unfold downhill nrm; exact norm_smul_inv_norm hraw

theorem downhill_orth {b : E3} (hb : ‖b‖ = 1) : ⟪downhill b, b⟫ = 0 := by
  rw [downhill, nrm, real_inner_smul_left, inner_downhillRaw_self hb, mul_zero]

/-- `downhill b` is aligned with the rotor-plane part of `-e₃`. -/
theorem downhill_aligned {b : E3} (hb : ‖b‖ = 1) (hraw : downhillRaw b ≠ 0) :
    ⟪downhill b, -up⟫ = √(1 - ⟪b, -up⟫ ^ 2) := by
  have hpos : 0 < ‖downhillRaw b‖ := norm_pos_iff.2 hraw
  have hsq := norm_downhillRaw_sq hb
  have hin : ⟪downhillRaw b, -up⟫ = ‖downhillRaw b‖ ^ 2 := by
    rw [hsq, downhillRaw, inner_add_left, inner_neg_left, inner_neg_right, inner_neg_right,
      real_inner_self_eq_norm_sq, norm_up', real_inner_smul_left]
    ring
  rw [downhill, nrm, real_inner_smul_left, hin, inner_neg_right, neg_sq, ← hsq,
    Real.sqrt_sq hpos.le]
  field_simp

theorem downhillRaw_sub {b b' : E3} :
    downhillRaw b' - downhillRaw b = ⟪b' - b, up⟫ • b' + ⟪b, up⟫ • (b' - b) := by
  rw [downhillRaw, downhillRaw, inner_sub_left]; module

theorem norm_downhillRaw_sub_le {b b' : E3} (hb : ‖b‖ = 1) (hb' : ‖b'‖ = 1) :
    ‖downhillRaw b' - downhillRaw b‖ ≤ 2 * ‖b' - b‖ := by
  rw [downhillRaw_sub]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hb']
  have h1 := abs_real_inner_le_norm (b' - b) up
  have h2 := abs_real_inner_le_norm b up
  rw [norm_up'] at h1 h2; rw [hb] at h2
  nlinarith [norm_nonneg (b' - b), abs_nonneg ⟪b, up⟫]

theorem downhillRaw_second {a b c : E3} :
    downhillRaw c - 2 • downhillRaw b + downhillRaw a =
      ⟪c - 2 • b + a, up⟫ • c + ⟪b, up⟫ • (c - 2 • b + a) + ⟪b - a, up⟫ • ((c - b) + (b - a)) := by
  simp only [downhillRaw, inner_add_left, inner_sub_left, two_smul]
  module

theorem norm_downhillRaw_second_le {a b c : E3} (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    ‖downhillRaw c - 2 • downhillRaw b + downhillRaw a‖ ≤
      2 * ‖c - 2 • b + a‖ + ‖b - a‖ * (‖c - b‖ + ‖b - a‖) := by
  rw [downhillRaw_second]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_)
  · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hc]
    have h1 := abs_real_inner_le_norm (c - 2 • b + a) up
    have h2 := abs_real_inner_le_norm b up
    rw [norm_up'] at h1 h2; rw [hb] at h2
    nlinarith [norm_nonneg (c - 2 • b + a), abs_nonneg ⟪b, up⟫]
  · rw [norm_smul, Real.norm_eq_abs]
    have h1 := abs_real_inner_le_norm (b - a) up
    rw [norm_up', mul_one] at h1
    exact mul_le_mul h1 (norm_add_le _ _) (norm_nonneg _) (norm_nonneg _)

end VisionTracking

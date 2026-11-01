import VisionTracking.BodyRate
import VisionTracking.SharpNorm

/-!
# The lateral-locked frame

Given the thrust direction `n` and a horizontal lateral reference `ℓ` (both unit), the
frame is

* `b₂ = nrm (-ℓ + ⟪ℓ,n⟫ n)`, the reference projected into the rotor plane;
* `b₁ = b₂ × n`, pointing backwards relative to the travel direction;
* `b₃ = b₁ × b₂ = n`.

It is defined whenever `|⟪ℓ,n⟫| < 1`, at every pitch. This file proves the frame facts
and the step-local bounds on the body-rate vector `a` and its change, in terms of the
steps of `n` and `ℓ`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

noncomputable def latRaw (ℓ n : E3) : E3 := -ℓ + ⟪ℓ, n⟫ • n
noncomputable def lat2 (ℓ n : E3) : E3 := nrm (latRaw ℓ n)
noncomputable def lat1 (ℓ n : E3) : E3 := cross (lat2 ℓ n) n

section Basic

variable {ℓ n : E3} (hn : ‖n‖ = 1) (hℓ : ‖ℓ‖ = 1)
include hn

theorem inner_latRaw_n : ⟪latRaw ℓ n, n⟫ = 0 := by
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  rw [latRaw, inner_add_left, inner_neg_left, real_inner_smul_left, hnn]; ring

include hℓ in
theorem norm_latRaw_sq : ‖latRaw ℓ n‖ ^ 2 = 1 - ⟪ℓ, n⟫ ^ 2 := by
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hll : ⟪ℓ, ℓ⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hℓ]; norm_num
  rw [← real_inner_self_eq_norm_sq, latRaw]
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
    real_inner_smul_left, real_inner_smul_right, hnn, hll]
  rw [real_inner_comm n ℓ]; ring

include hℓ in
theorem norm_latRaw : ‖latRaw ℓ n‖ = √(1 - ⟪ℓ, n⟫ ^ 2) := by
  rw [← norm_latRaw_sq hn hℓ, Real.sqrt_sq (norm_nonneg _)]

include hℓ in
theorem latRaw_ne (hf : |⟪ℓ, n⟫| < 1) : latRaw ℓ n ≠ 0 := by
  intro h
  have := norm_latRaw_sq hn hℓ
  rw [h, norm_zero] at this
  have : ⟪ℓ, n⟫ ^ 2 < 1 := by
    have := abs_lt.1 hf; nlinarith
  linarith

include hℓ in
theorem lat2_unit (hf : |⟪ℓ, n⟫| < 1) : ‖lat2 ℓ n‖ = 1 := by
  unfold lat2 nrm; exact norm_smul_inv_norm (latRaw_ne hn hℓ hf)

theorem inner_lat2_n : ⟪lat2 ℓ n, n⟫ = 0 := by
  rw [lat2, nrm, real_inner_smul_left, inner_latRaw_n hn, mul_zero]

include hℓ in
theorem lat1_unit (hf : |⟪ℓ, n⟫| < 1) : ‖lat1 ℓ n‖ = 1 :=
  norm_cross_of_orthonormal (lat2_unit hn hℓ hf) hn (inner_lat2_n hn)

omit hn in
theorem inner_lat1_lat2 : ⟪lat1 ℓ n, lat2 ℓ n⟫ = 0 := by
  rw [lat1, real_inner_comm]; exact inner_cross_left _ _

omit hn in
theorem inner_lat1_n : ⟪lat1 ℓ n, n⟫ = 0 := by
  rw [lat1, real_inner_comm]; exact inner_cross_right _ _

include hℓ in
theorem cross_lat1_lat2 (hf : |⟪ℓ, n⟫| < 1) : cross (lat1 ℓ n) (lat2 ℓ n) = n := by
  have h22 : ⟪lat2 ℓ n, lat2 ℓ n⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, lat2_unit hn hℓ hf]; norm_num
  rw [lat1, cross_cross_eq, h22, real_inner_comm, inner_lat2_n hn, one_smul, zero_smul, sub_zero]

omit hn in
/-- The lateral axis is the projected reference up to the factor `1/‖m‖`. -/
theorem lat2_eq : lat2 ℓ n = ‖latRaw ℓ n‖⁻¹ • latRaw ℓ n := rfl

omit hn in
theorem inner_latRaw_lat1 : ⟪latRaw ℓ n, lat1 ℓ n⟫ = 0 := by
  rw [lat1, lat2, nrm, cross_smul_left, inner_smul_right, inner_cross_left, mul_zero]

include hℓ in
theorem inv_norm_latRaw_le {sb : ℝ} (hf : |⟪ℓ, n⟫| ≤ sb) (hsb : sb < 1) :
    ‖latRaw ℓ n‖⁻¹ ≤ 1 / √(1 - sb ^ 2) := by
  have hs : 0 < √(1 - sb ^ 2) := Real.sqrt_pos.2 (by nlinarith [abs_nonneg ⟪ℓ, n⟫])
  rw [norm_latRaw hn hℓ, ← one_div]
  apply one_div_le_one_div_of_le hs
  apply Real.sqrt_le_sqrt
  nlinarith [sq_abs ⟪ℓ, n⟫, abs_nonneg ⟪ℓ, n⟫]

end Basic

/-- Bessel for an orthonormal pair. -/
theorem bessel_pair {b₁ b₂ : E3} (h₁ : ‖b₁‖ = 1) (h₂ : ‖b₂‖ = 1) (h₁₂ : ⟪b₁, b₂⟫ = 0) (x : E3) :
    ⟪b₁, x⟫ ^ 2 + ⟪b₂, x⟫ ^ 2 + ⟪cross b₁ b₂, x⟫ ^ 2 = ‖x‖ ^ 2 := by
  have h := norm_toF h₁ h₂ h₁₂ x
  obtain ⟨t0, t1, t2⟩ := toF_ofLp b₁ b₂ x
  rw [← h, ← real_inner_self_eq_norm_sq (toF b₁ b₂ x), inner_eq_coords (toF b₁ b₂ x), t0, t1, t2]
  ring

/-! ## One step: the body-rate vector -/

section Step

variable {ℓ₀ ℓ₁ n₀ n₁ : E3} {sb : ℝ}
  (hn₀ : ‖n₀‖ = 1) (hn₁ : ‖n₁‖ = 1) (hℓ₀ : ‖ℓ₀‖ = 1) (hℓ₁ : ‖ℓ₁‖ = 1)
  (hf₀ : |⟪ℓ₀, n₀⟫| ≤ sb) (hf₁ : |⟪ℓ₁, n₁⟫| ≤ sb) (hsb : sb < 1)
include hn₀ hn₁ hℓ₀ hℓ₁ hf₀ hf₁ hsb

/-- **Roll and pitch components**: `a₀² + a₁² ≤ ‖Δn‖²`. -/
theorem lat_aVec_rp :
    (aVec (lat1 ℓ₀ n₀) (lat2 ℓ₀ n₀) (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁)).ofLp 0 ^ 2
      + (aVec (lat1 ℓ₀ n₀) (lat2 ℓ₀ n₀) (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁)).ofLp 1 ^ 2
      ≤ ‖n₁ - n₀‖ ^ 2 := by
  have f0 : |⟪ℓ₀, n₀⟫| < 1 := hf₀.trans_lt hsb
  have f1 : |⟪ℓ₁, n₁⟫| < 1 := hf₁.trans_lt hsb
  obtain ⟨e0, e1, -⟩ := aVec_ofLp_diff (c₁ := lat1 ℓ₁ n₁) (c₂ := lat2 ℓ₁ n₁)
    (lat1_unit hn₀ hℓ₀ f0) (lat2_unit hn₀ hℓ₀ f0) (inner_lat1_lat2) (inner_lat1_lat2)
  rw [cross_lat1_lat2 hn₀ hℓ₀ f0, cross_lat1_lat2 hn₁ hℓ₁ f1] at e0 e1
  rw [e0, e1]
  set x := n₁ - n₀
  have B0 := bessel_pair (lat1_unit hn₀ hℓ₀ f0) (lat2_unit hn₀ hℓ₀ f0) inner_lat1_lat2 x
  have B1 := bessel_pair (lat1_unit hn₁ hℓ₁ f1) (lat2_unit hn₁ hℓ₁ f1) inner_lat1_lat2 x
  rw [real_inner_comm x (lat1 ℓ₀ n₀), real_inner_comm x (lat2 ℓ₀ n₀),
    real_inner_comm x (cross (lat1 ℓ₀ n₀) (lat2 ℓ₀ n₀))] at B0
  rw [real_inner_comm x (lat1 ℓ₁ n₁), real_inner_comm x (lat2 ℓ₁ n₁),
    real_inner_comm x (cross (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁))] at B1
  nlinarith [sq_nonneg ⟪x, cross (lat1 ℓ₀ n₀) (lat2 ℓ₀ n₀)⟫,
    sq_nonneg ⟪x, cross (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁)⟫,
    sq_nonneg (⟪x, lat2 ℓ₁ n₁⟫ - ⟪x, lat2 ℓ₀ n₀⟫), sq_nonneg (⟪x, lat1 ℓ₀ n₀⟫ - ⟪x, lat1 ℓ₁ n₁⟫)]

/-- **Yaw component**: `|a₂| ≤ (‖Δℓ‖ + sb ‖Δn‖)/√(1 - sb²)`. -/
theorem lat_aVec_yaw :
    |(aVec (lat1 ℓ₀ n₀) (lat2 ℓ₀ n₀) (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁)).ofLp 2|
      ≤ (‖ℓ₁ - ℓ₀‖ + sb * ‖n₁ - n₀‖) / √(1 - sb ^ 2) := by
  have f0 : |⟪ℓ₀, n₀⟫| < 1 := hf₀.trans_lt hsb
  have f1 : |⟪ℓ₁, n₁⟫| < 1 := hf₁.trans_lt hsb
  have hsb0 : 0 ≤ sb := (abs_nonneg _).trans hf₀
  obtain ⟨-, -, e2⟩ := aVec_ofLp_diff (c₁ := lat1 ℓ₁ n₁) (c₂ := lat2 ℓ₁ n₁)
    (lat1_unit hn₀ hℓ₀ f0) (lat2_unit hn₀ hℓ₀ f0) (inner_lat1_lat2) (inner_lat1_lat2)
  rw [e2]
  have D : ∀ u : E3, ⟪latRaw ℓ₁ n₁ - latRaw ℓ₀ n₀, u⟫
      = -⟪ℓ₁ - ℓ₀, u⟫ + ⟪ℓ₁, n₁⟫ * ⟪n₁, u⟫ - ⟪ℓ₀, n₀⟫ * ⟪n₀, u⟫ := by
    intro u
    simp only [latRaw, inner_sub_left, inner_add_left, inner_neg_left, real_inner_smul_left]
    ring
  set b₁ := lat1 ℓ₀ n₀; set c₁ := lat1 ℓ₁ n₁
  have hr₀ : 0 ≤ ‖latRaw ℓ₀ n₀‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  have hr₁ : 0 ≤ ‖latRaw ℓ₁ n₁‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  have hr₀le : ‖latRaw ℓ₀ n₀‖⁻¹ ≤ 1 / √(1 - sb ^ 2) := inv_norm_latRaw_le hn₀ hℓ₀ hf₀ hsb
  have hr₁le : ‖latRaw ℓ₁ n₁‖⁻¹ ≤ 1 / √(1 - sb ^ 2) := inv_norm_latRaw_le hn₁ hℓ₁ hf₁ hsb
  have P1 : ⟪lat2 ℓ₁ n₁ - lat2 ℓ₀ n₀, b₁⟫
      = ‖latRaw ℓ₁ n₁‖⁻¹ * (-⟪ℓ₁ - ℓ₀, b₁⟫ + ⟪ℓ₁, n₁⟫ * ⟪n₁ - n₀, b₁⟫) := by
    have o1 : ⟪lat2 ℓ₀ n₀, b₁⟫ = 0 := by rw [real_inner_comm]; exact inner_lat1_lat2
    have o2 : ⟪latRaw ℓ₀ n₀, b₁⟫ = 0 := inner_latRaw_lat1
    have o3 : ⟪n₀, b₁⟫ = 0 := by rw [real_inner_comm]; exact inner_lat1_n
    rw [inner_sub_left, o1, sub_zero, lat2_eq, real_inner_smul_left]
    have : ⟪latRaw ℓ₁ n₁, b₁⟫ = ⟪latRaw ℓ₁ n₁ - latRaw ℓ₀ n₀, b₁⟫ := by
      rw [inner_sub_left, o2, sub_zero]
    rw [this, D]
    simp only [inner_sub_left, o3]
    ring
  have P2 : ⟪lat2 ℓ₁ n₁ - lat2 ℓ₀ n₀, c₁⟫
      = ‖latRaw ℓ₀ n₀‖⁻¹ * (-⟪ℓ₁ - ℓ₀, c₁⟫ + ⟪ℓ₀, n₀⟫ * ⟪n₁ - n₀, c₁⟫) := by
    have o1 : ⟪lat2 ℓ₁ n₁, c₁⟫ = 0 := by rw [real_inner_comm]; exact inner_lat1_lat2
    have o2 : ⟪latRaw ℓ₁ n₁, c₁⟫ = 0 := inner_latRaw_lat1
    have o3 : ⟪n₁, c₁⟫ = 0 := by rw [real_inner_comm]; exact inner_lat1_n
    rw [inner_sub_left, o1, zero_sub, lat2_eq, real_inner_smul_left]
    have : ⟪latRaw ℓ₀ n₀, c₁⟫ = -⟪latRaw ℓ₁ n₁ - latRaw ℓ₀ n₀, c₁⟫ := by
      rw [inner_sub_left, o2]; ring
    rw [this, D]
    simp only [inner_sub_left, o3]
    ring
  rw [P1, P2]
  -- bound each bracket by ‖Δℓ‖ + sb ‖Δn‖
  have hb₁ : ‖b₁‖ = 1 := lat1_unit hn₀ hℓ₀ f0
  have hc₁ : ‖c₁‖ = 1 := lat1_unit hn₁ hℓ₁ f1
  have K : ∀ (u : E3), ‖u‖ = 1 → ∀ f : ℝ, |f| ≤ sb →
      |-⟪ℓ₁ - ℓ₀, u⟫ + f * ⟪n₁ - n₀, u⟫| ≤ ‖ℓ₁ - ℓ₀‖ + sb * ‖n₁ - n₀‖ := by
    intro u hu f hf
    have a1 := abs_real_inner_le_norm (ℓ₁ - ℓ₀) u
    have a2 := abs_real_inner_le_norm (n₁ - n₀) u
    rw [hu, mul_one] at a1 a2
    calc |-⟪ℓ₁ - ℓ₀, u⟫ + f * ⟪n₁ - n₀, u⟫| ≤ |⟪ℓ₁ - ℓ₀, u⟫| + |f| * |⟪n₁ - n₀, u⟫| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_neg, abs_mul]
      _ ≤ ‖ℓ₁ - ℓ₀‖ + sb * ‖n₁ - n₀‖ := by
          gcongr
  have k1 := K b₁ hb₁ _ hf₁
  have k2 := K c₁ hc₁ _ hf₀
  set Z := ‖ℓ₁ - ℓ₀‖ + sb * ‖n₁ - n₀‖
  have hZ : 0 ≤ Z := by positivity
  have t1 : |‖latRaw ℓ₁ n₁‖⁻¹ * (-⟪ℓ₁ - ℓ₀, b₁⟫ + ⟪ℓ₁, n₁⟫ * ⟪n₁ - n₀, b₁⟫)|
      ≤ Z / √(1 - sb ^ 2) := by
    rw [abs_mul, abs_of_nonneg hr₁, div_eq_mul_one_div, mul_comm Z]
    exact mul_le_mul hr₁le k1 (abs_nonneg _) (by positivity)
  have t2 : |‖latRaw ℓ₀ n₀‖⁻¹ * (-⟪ℓ₁ - ℓ₀, c₁⟫ + ⟪ℓ₀, n₀⟫ * ⟪n₁ - n₀, c₁⟫)|
      ≤ Z / √(1 - sb ^ 2) := by
    rw [abs_mul, abs_of_nonneg hr₀, div_eq_mul_one_div, mul_comm Z]
    exact mul_le_mul hr₀le k2 (abs_nonneg _) (by positivity)
  rw [abs_div, abs_neg, abs_two]
  have := abs_add_le (‖latRaw ℓ₀ n₀‖⁻¹ * (-⟪ℓ₁ - ℓ₀, c₁⟫ + ⟪ℓ₀, n₀⟫ * ⟪n₁ - n₀, c₁⟫))
    (‖latRaw ℓ₁ n₁‖⁻¹ * (-⟪ℓ₁ - ℓ₀, b₁⟫ + ⟪ℓ₁, n₁⟫ * ⟪n₁ - n₀, b₁⟫))
  linarith

end Step


/-! ## Helpers for second differences -/

theorem abs_inner_le_cross {n c x : E3} (hn : ‖n‖ = 1) (hc : ‖c‖ = 1) (hnc : ⟪n, c⟫ = 0) :
    |⟪x, c⟫| ≤ ‖cross n x‖ := by
  have hcc : ‖cross n c‖ = 1 := norm_cross_of_orthonormal hn hc hnc
  have h := inner_cross_cross n x n c
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  rw [hnn, one_mul, hnc, zero_mul, sub_zero] at h
  rw [← h]
  have := abs_real_inner_le_norm (cross n x) (cross n c)
  rwa [hcc, mul_one] at this

theorem abs_inner_sub_inner_le {ℓ ℓ' n n' : E3} (hℓ : ‖ℓ‖ = 1) (hn' : ‖n'‖ = 1) :
    |⟪ℓ', n'⟫ - ⟪ℓ, n⟫| ≤ ‖ℓ' - ℓ‖ + ‖n' - n‖ := by
  have e : ⟪ℓ', n'⟫ - ⟪ℓ, n⟫ = ⟪ℓ' - ℓ, n'⟫ + ⟪ℓ, n' - n⟫ := by
    rw [inner_sub_left, inner_sub_right]; ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · have := abs_real_inner_le_norm (ℓ' - ℓ) n'; rwa [hn', mul_one] at this
  · have := abs_real_inner_le_norm ℓ (n' - n); rwa [hℓ, one_mul] at this

theorem norm_latRaw_le_one {ℓ n : E3} (hn : ‖n‖ = 1) (hℓ : ‖ℓ‖ = 1) : ‖latRaw ℓ n‖ ≤ 1 := by
  have h := norm_latRaw_sq hn hℓ
  have : ‖latRaw ℓ n‖ ^ 2 ≤ 1 := by rw [h]; nlinarith [sq_nonneg ⟪ℓ, n⟫]
  nlinarith [norm_nonneg (latRaw ℓ n)]

theorem inv_norm_latRaw_sub_le {ℓ ℓ' n n' : E3} {sb : ℝ} (hn : ‖n‖ = 1) (hn' : ‖n'‖ = 1)
    (hℓ : ‖ℓ‖ = 1) (hℓ' : ‖ℓ'‖ = 1) (hf : |⟪ℓ, n⟫| ≤ sb) (hf' : |⟪ℓ', n'⟫| ≤ sb) (hsb : sb < 1) :
    |‖latRaw ℓ' n'‖⁻¹ - ‖latRaw ℓ n‖⁻¹|
      ≤ sb * (‖ℓ' - ℓ‖ + ‖n' - n‖) / √(1 - sb ^ 2) ^ 3 := by
  have hsb0 : 0 ≤ sb := (abs_nonneg _).trans hf
  have hs : 0 < √(1 - sb ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  set M := √(1 - sb ^ 2)
  have hM : ∀ {ℓ n : E3}, ‖n‖ = 1 → ‖ℓ‖ = 1 → |⟪ℓ, n⟫| ≤ sb → M ≤ ‖latRaw ℓ n‖ := by
    intro ℓ n hn hℓ hf
    rw [norm_latRaw hn hℓ]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_abs ⟪ℓ, n⟫, abs_nonneg ⟪ℓ, n⟫]
  have m0 := hM hn hℓ hf
  have m1 := hM hn' hℓ' hf'
  set A := ‖latRaw ℓ n‖; set B := ‖latRaw ℓ' n'‖
  have hA : 0 < A := hs.trans_le m0
  have hB : 0 < B := hs.trans_le m1
  have hAB : |A - B| ≤ sb * (‖ℓ' - ℓ‖ + ‖n' - n‖) / M := by
    have sA : A ^ 2 = 1 - ⟪ℓ, n⟫ ^ 2 := norm_latRaw_sq hn hℓ
    have sB : B ^ 2 = 1 - ⟪ℓ', n'⟫ ^ 2 := norm_latRaw_sq hn' hℓ'
    have hd := abs_inner_sub_inner_le (ℓ := ℓ) (ℓ' := ℓ') (n := n) hℓ hn'
    have hsum : |⟪ℓ', n'⟫ + ⟪ℓ, n⟫| ≤ 2 * sb := (abs_add_le _ _).trans (by linarith)
    have key : (A - B) * (A + B) = (⟪ℓ', n'⟫ - ⟪ℓ, n⟫) * (⟪ℓ', n'⟫ + ⟪ℓ, n⟫) := by
      nlinarith [sA, sB]
    have hpos : 2 * M ≤ A + B := by linarith
    rw [le_div_iff₀ hs]
    have h1 : |A - B| * (A + B) ≤ (‖ℓ' - ℓ‖ + ‖n' - n‖) * (2 * sb) := by
      rw [← abs_of_pos (by linarith : 0 < A + B), ← abs_mul, key, abs_mul]
      exact mul_le_mul hd hsum (abs_nonneg _) (by positivity)
    nlinarith [abs_nonneg (A - B), mul_le_mul_of_nonneg_left hpos (abs_nonneg (A - B))]
  have e : B⁻¹ - A⁻¹ = (A - B) / (A * B) := by field_simp
  rw [e, abs_div, abs_of_pos (mul_pos hA hB)]
  have hM3 : M ^ 3 = M * (M * M) := by ring
  rw [div_le_div_iff₀ (mul_pos hA hB) (by positivity), hM3]
  have hMM : M * M ≤ A * B := mul_le_mul m0 m1 hs.le hA.le
  have := mul_le_mul_of_nonneg_left hMM (abs_nonneg (A - B))
  have h2 : |A - B| * M ≤ sb * (‖ℓ' - ℓ‖ + ‖n' - n‖) := by
    rwa [le_div_iff₀ hs] at hAB
  nlinarith [mul_le_mul_of_nonneg_right h2 (mul_nonneg hs.le hs.le)]


/-! ## Two steps: change of the body-rate vector -/

theorem sq2_add_le {p₀ p₁ w₀ w₁ X W : ℝ} (hX : 0 ≤ X) (hW : 0 ≤ W)
    (hp : p₀ ^ 2 + p₁ ^ 2 ≤ X ^ 2) (hw : w₀ ^ 2 + w₁ ^ 2 ≤ W ^ 2) :
    (p₀ + w₀) ^ 2 + (p₁ + w₁) ^ 2 ≤ (X + W) ^ 2 := by
  have cs : (p₀ * w₀ + p₁ * w₁) ^ 2 ≤ (X * W) ^ 2 := by
    have : (p₀ * w₀ + p₁ * w₁) ^ 2 ≤ (p₀ ^ 2 + p₁ ^ 2) * (w₀ ^ 2 + w₁ ^ 2) := by
      nlinarith [sq_nonneg (p₀ * w₁ - p₁ * w₀)]
    calc _ ≤ (p₀ ^ 2 + p₁ ^ 2) * (w₀ ^ 2 + w₁ ^ 2) := this
      _ ≤ X ^ 2 * W ^ 2 := mul_le_mul hp hw (by positivity) (by positivity)
      _ = (X * W) ^ 2 := by ring
  have : p₀ * w₀ + p₁ * w₁ ≤ X * W := (abs_le_of_sq_le_sq' cs (by positivity)).2
  nlinarith



section Second

variable {ℓ₀ ℓ₁ ℓ₂ n₀ n₁ n₂ : E3} {sb dn dl d2n xn d2l db : ℝ}
  (hn₀ : ‖n₀‖ = 1) (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1)
  (hℓ₀ : ‖ℓ₀‖ = 1) (hℓ₁ : ‖ℓ₁‖ = 1) (hℓ₂ : ‖ℓ₂‖ = 1)
  (hf₀ : |⟪ℓ₀, n₀⟫| ≤ sb) (hf₁ : |⟪ℓ₁, n₁⟫| ≤ sb) (hf₂ : |⟪ℓ₂, n₂⟫| ≤ sb) (hsb : sb < 1)
  (hdn₀ : ‖n₁ - n₀‖ ≤ dn) (hdn₁ : ‖n₂ - n₁‖ ≤ dn)
  (hdl₀ : ‖ℓ₁ - ℓ₀‖ ≤ dl) (hdl₁ : ‖ℓ₂ - ℓ₁‖ ≤ dl)
  (hd2n : ‖n₂ - 2 • n₁ + n₀‖ ≤ d2n) (hxn : ‖cross n₁ (n₂ - 2 • n₁ + n₀)‖ ≤ xn)
  (hd2l : ‖ℓ₂ - 2 • ℓ₁ + ℓ₀‖ ≤ d2l)
  (hdb : ‖lat1 ℓ₁ n₁ - lat1 ℓ₀ n₀‖ ≤ db ∧ ‖lat1 ℓ₂ n₂ - lat1 ℓ₁ n₁‖ ≤ db ∧
    ‖lat2 ℓ₁ n₁ - lat2 ℓ₀ n₀‖ ≤ db ∧ ‖lat2 ℓ₂ n₂ - lat2 ℓ₁ n₁‖ ≤ db)

/-- Bound on the second difference of the projected reference `m = -ℓ + ⟪ℓ,n⟫ n`. -/
noncomputable def latD2m (sb dn dl d2n d2l : ℝ) : ℝ :=
  d2l + (d2l + d2n + 2 * dl * dn) + sb * d2n + 2 * (dl + dn) * dn

/-- Bound on the second difference of the lateral axis `b₂`. -/
noncomputable def latD2b2 (sb dn dl d2n d2l : ℝ) : ℝ :=
  latD2m sb dn dl d2n d2l / √(1 - sb ^ 2) + 2 * (sb * (dl + dn) / √(1 - sb ^ 2) ^ 3)

/-- Bound on the change of the yaw component. -/
noncomputable def latDYaw (sb dn dl d2n xn d2l db : ℝ) : ℝ :=
  (d2l + sb * xn + 2 * (dl + dn) * dn) / √(1 - sb ^ 2)
    + 2 * (sb * (dl + dn) / √(1 - sb ^ 2) ^ 3) * (dl + sb * dn)
    + latD2b2 sb dn dl d2n d2l / 2 * db + db * db

include hn₀ hn₁ hn₂ hℓ₀ hℓ₁ hℓ₂ hf₀ hf₁ hf₂ hsb hdn₀ hdn₁ hdl₀ hdl₁ hd2n hxn hd2l hdb

/-- **Change of the yaw component** over two steps. -/
theorem lat_aVec_yaw_second :
    |(aVec (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁) (lat1 ℓ₂ n₂) (lat2 ℓ₂ n₂)).ofLp 2
      - (aVec (lat1 ℓ₀ n₀) (lat2 ℓ₀ n₀) (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁)).ofLp 2|
      ≤ latDYaw sb dn dl d2n xn d2l db := by
  have f0 : |⟪ℓ₀, n₀⟫| < 1 := hf₀.trans_lt hsb
  have f1 : |⟪ℓ₁, n₁⟫| < 1 := hf₁.trans_lt hsb
  have f2 : |⟪ℓ₂, n₂⟫| < 1 := hf₂.trans_lt hsb
  have hsb0 : 0 ≤ sb := (abs_nonneg _).trans hf₀
  have hs : 0 < √(1 - sb ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  set M := √(1 - sb ^ 2) with hMdef
  have hdn0 : 0 ≤ dn := (norm_nonneg _).trans hdn₀
  have hdl0 : 0 ≤ dl := (norm_nonneg _).trans hdl₀
  have hdb0 : 0 ≤ db := (norm_nonneg _).trans hdb.1
  set C₀ := lat1 ℓ₀ n₀; set C₁ := lat1 ℓ₁ n₁; set C₂ := lat1 ℓ₂ n₂
  set B₀ := lat2 ℓ₀ n₀; set B₁ := lat2 ℓ₁ n₁; set B₂ := lat2 ℓ₂ n₂
  obtain ⟨-, -, e01⟩ := aVec_ofLp_diff (c₁ := C₁) (c₂ := B₁)
    (lat1_unit hn₀ hℓ₀ f0) (lat2_unit hn₀ hℓ₀ f0) inner_lat1_lat2 inner_lat1_lat2
  obtain ⟨-, -, e12⟩ := aVec_ofLp_diff (c₁ := C₂) (c₂ := B₂)
    (lat1_unit hn₁ hℓ₁ f1) (lat2_unit hn₁ hℓ₁ f1) inner_lat1_lat2 inner_lat1_lat2
  set D := B₂ - 2 • B₁ + B₀ with hD
  have E1 : (aVec C₁ B₁ C₂ B₂).ofLp 2 - (aVec C₀ B₀ C₁ B₁).ofLp 2
      = -(2 * ⟪D, C₁⟫ + ⟪D, C₂ - C₁⟫ + ⟪B₁ - B₀, C₂ - C₀⟫) / 2 := by
    rw [e01, e12, hD]
    simp only [two_smul, inner_add_left, inner_sub_left, inner_sub_right]
    ring
  rw [E1]
  -- ingredients
  set m₀ := latRaw ℓ₀ n₀; set m₁ := latRaw ℓ₁ n₁; set m₂ := latRaw ℓ₂ n₂
  set r₀ := ‖m₀‖⁻¹ with hr₀; set r₁ := ‖m₁‖⁻¹ with hr₁; set r₂ := ‖m₂‖⁻¹ with hr₂
  have hB₀ : B₀ = r₀ • m₀ := rfl
  have hB₁ : B₁ = r₁ • m₁ := rfl
  have hB₂ : B₂ = r₂ • m₂ := rfl
  have r1le : r₁ ≤ 1 / M := inv_norm_latRaw_le hn₁ hℓ₁ hf₁ hsb
  have r1nn : 0 ≤ r₁ := inv_nonneg.2 (norm_nonneg _)
  have dr01 : |r₁ - r₀| ≤ sb * (dl + dn) / M ^ 3 := by
    refine (inv_norm_latRaw_sub_le hn₀ hn₁ hℓ₀ hℓ₁ hf₀ hf₁ hsb).trans ?_
    gcongr
  have dr12 : |r₂ - r₁| ≤ sb * (dl + dn) / M ^ 3 := by
    refine (inv_norm_latRaw_sub_le hn₁ hn₂ hℓ₁ hℓ₂ hf₁ hf₂ hsb).trans ?_
    gcongr
  have hC₁ : ‖C₁‖ = 1 := lat1_unit hn₁ hℓ₁ f1
  have oC1n1 : ⟪n₁, C₁⟫ = 0 := by rw [real_inner_comm]; exact inner_lat1_n
  have oC1m1 : ⟪m₁, C₁⟫ = 0 := inner_latRaw_lat1
  have hinC : ∀ x : E3, |⟪x, C₁⟫| ≤ ‖x‖ := fun x => by
    have := abs_real_inner_le_norm x C₁; rwa [hC₁, mul_one] at this
  have hxC : |⟪n₂ - 2 • n₁ + n₀, C₁⟫| ≤ xn :=
    (abs_inner_le_cross hn₁ hC₁ oC1n1).trans hxn
  -- f differences
  have df01 : |⟪ℓ₁, n₁⟫ - ⟪ℓ₀, n₀⟫| ≤ dl + dn :=
    (abs_inner_sub_inner_le hℓ₀ hn₁).trans (add_le_add hdl₀ hdn₀)
  have df12 : |⟪ℓ₂, n₂⟫ - ⟪ℓ₁, n₁⟫| ≤ dl + dn :=
    (abs_inner_sub_inner_le hℓ₁ hn₂).trans (add_le_add hdl₁ hdn₁)
  have df02 : |⟪ℓ₂, n₂⟫ - ⟪ℓ₀, n₀⟫| ≤ 2 * (dl + dn) := by
    have := abs_add_le (⟪ℓ₂, n₂⟫ - ⟪ℓ₁, n₁⟫) (⟪ℓ₁, n₁⟫ - ⟪ℓ₀, n₀⟫)
    rw [sub_add_sub_cancel] at this; linarith
  -- E3: projection of the second difference of m on C₁
  have E3 : ⟪m₂ - 2 • m₁ + m₀, C₁⟫ = -⟪ℓ₂ - 2 • ℓ₁ + ℓ₀, C₁⟫
      + ⟪ℓ₂, n₂⟫ * ⟪n₂ - 2 • n₁ + n₀, C₁⟫ + (⟪ℓ₂, n₂⟫ - ⟪ℓ₀, n₀⟫) * ⟪n₁ - n₀, C₁⟫ := by
    simp only [m₂, m₁, m₀, latRaw, two_smul, inner_add_left, inner_sub_left, inner_neg_left,
      inner_smul_left, RCLike.conj_to_real, oC1n1]
    ring
  have bE3 : |⟪m₂ - 2 • m₁ + m₀, C₁⟫| ≤ d2l + sb * xn + 2 * (dl + dn) * dn := by
    rw [E3]
    have a1 := (hinC (ℓ₂ - 2 • ℓ₁ + ℓ₀)).trans hd2l
    have a2 : |⟪ℓ₂, n₂⟫ * ⟪n₂ - 2 • n₁ + n₀, C₁⟫| ≤ sb * xn := by
      rw [abs_mul]; exact mul_le_mul hf₂ hxC (abs_nonneg _) hsb0
    have a3 : |(⟪ℓ₂, n₂⟫ - ⟪ℓ₀, n₀⟫) * ⟪n₁ - n₀, C₁⟫| ≤ 2 * (dl + dn) * dn := by
      rw [abs_mul]; exact mul_le_mul df02 ((hinC _).trans hdn₀) (abs_nonneg _) (by positivity)
    have := abs_add_le (-⟪ℓ₂ - 2 • ℓ₁ + ℓ₀, C₁⟫ + ⟪ℓ₂, n₂⟫ * ⟪n₂ - 2 • n₁ + n₀, C₁⟫)
      ((⟪ℓ₂, n₂⟫ - ⟪ℓ₀, n₀⟫) * ⟪n₁ - n₀, C₁⟫)
    have := abs_add_le (-⟪ℓ₂ - 2 • ℓ₁ + ℓ₀, C₁⟫) (⟪ℓ₂, n₂⟫ * ⟪n₂ - 2 • n₁ + n₀, C₁⟫)
    rw [abs_neg] at this
    linarith
  -- E4: first differences of m projected on C₁
  have E4a : |⟪m₂ - m₁, C₁⟫| ≤ dl + sb * dn := by
    have : ⟪m₂ - m₁, C₁⟫ = -⟪ℓ₂ - ℓ₁, C₁⟫ + ⟪ℓ₂, n₂⟫ * ⟪n₂ - n₁, C₁⟫ := by
      simp only [m₂, m₁, latRaw, inner_add_left, inner_sub_left, inner_neg_left,
        inner_smul_left, RCLike.conj_to_real, oC1n1]
      ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_mul]
    have := mul_le_mul hf₂ ((hinC _).trans hdn₁) (abs_nonneg _) hsb0
    linarith [(hinC (ℓ₂ - ℓ₁)).trans hdl₁]
  have E4b : |⟪m₁ - m₀, C₁⟫| ≤ dl + sb * dn := by
    have : ⟪m₁ - m₀, C₁⟫ = -⟪ℓ₁ - ℓ₀, C₁⟫ + ⟪ℓ₀, n₀⟫ * ⟪n₁ - n₀, C₁⟫ := by
      simp only [m₁, m₀, latRaw, inner_add_left, inner_sub_left, inner_neg_left,
        inner_smul_left, RCLike.conj_to_real, oC1n1]
      ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_mul]
    have := mul_le_mul hf₀ ((hinC _).trans hdn₀) (abs_nonneg _) hsb0
    linarith [(hinC (ℓ₁ - ℓ₀)).trans hdl₀]
  -- E2: projection of D on C₁
  have E2 : ⟪D, C₁⟫ = r₁ * ⟪m₂ - 2 • m₁ + m₀, C₁⟫ + (r₂ - r₁) * ⟪m₂ - m₁, C₁⟫
      + (r₁ - r₀) * ⟪m₁ - m₀, C₁⟫ := by
    rw [hD, hB₀, hB₁, hB₂]
    simp only [two_smul, inner_add_left, inner_sub_left, inner_smul_left, RCLike.conj_to_real,
      oC1m1]
    ring
  have bE2 : |⟪D, C₁⟫| ≤ (d2l + sb * xn + 2 * (dl + dn) * dn) / M
      + 2 * (sb * (dl + dn) / M ^ 3) * (dl + sb * dn) := by
    rw [E2]
    have t1 : |r₁ * ⟪m₂ - 2 • m₁ + m₀, C₁⟫| ≤ (d2l + sb * xn + 2 * (dl + dn) * dn) / M := by
      rw [abs_mul, abs_of_nonneg r1nn, div_eq_mul_one_div, mul_comm (d2l + _ + _)]
      exact mul_le_mul r1le bE3 (abs_nonneg _) (by positivity)
    have t2 : |(r₂ - r₁) * ⟪m₂ - m₁, C₁⟫| ≤ sb * (dl + dn) / M ^ 3 * (dl + sb * dn) := by
      rw [abs_mul]; exact mul_le_mul dr12 E4a (abs_nonneg _) (by positivity)
    have t3 : |(r₁ - r₀) * ⟪m₁ - m₀, C₁⟫| ≤ sb * (dl + dn) / M ^ 3 * (dl + sb * dn) := by
      rw [abs_mul]; exact mul_le_mul dr01 E4b (abs_nonneg _) (by positivity)
    have := abs_add_le (r₁ * ⟪m₂ - 2 • m₁ + m₀, C₁⟫ + (r₂ - r₁) * ⟪m₂ - m₁, C₁⟫)
      ((r₁ - r₀) * ⟪m₁ - m₀, C₁⟫)
    have := abs_add_le (r₁ * ⟪m₂ - 2 • m₁ + m₀, C₁⟫) ((r₂ - r₁) * ⟪m₂ - m₁, C₁⟫)
    linarith
  -- E5/E6: norm of D
  have E6 : ‖m₂ - 2 • m₁ + m₀‖ ≤ latD2m sb dn dl d2n d2l := by
    have id1 : m₂ - 2 • m₁ + m₀ = -(ℓ₂ - 2 • ℓ₁ + ℓ₀)
        + ((⟪ℓ₂, n₂⟫ - 2 * ⟪ℓ₁, n₁⟫ + ⟪ℓ₀, n₀⟫) • n₁ + ⟪ℓ₂, n₂⟫ • (n₂ - 2 • n₁ + n₀)
          + (⟪ℓ₂, n₂⟫ - ⟪ℓ₀, n₀⟫) • (n₁ - n₀)) := by
      simp only [m₂, m₁, m₀, latRaw]; module
    have id2 : ⟪ℓ₂, n₂⟫ - 2 * ⟪ℓ₁, n₁⟫ + ⟪ℓ₀, n₀⟫ = ⟪ℓ₂ - 2 • ℓ₁ + ℓ₀, n₁⟫
        + ⟪ℓ₂, n₂ - 2 • n₁ + n₀⟫ + ⟪ℓ₂ - ℓ₀, n₁ - n₀⟫ := by
      simp only [two_smul, inner_add_left, inner_sub_left, inner_add_right, inner_sub_right]
      ring
    have bf : |⟪ℓ₂, n₂⟫ - 2 * ⟪ℓ₁, n₁⟫ + ⟪ℓ₀, n₀⟫| ≤ d2l + d2n + 2 * dl * dn := by
      rw [id2]
      have a1 := abs_real_inner_le_norm (ℓ₂ - 2 • ℓ₁ + ℓ₀) n₁
      have a2 := abs_real_inner_le_norm ℓ₂ (n₂ - 2 • n₁ + n₀)
      have a3 := abs_real_inner_le_norm (ℓ₂ - ℓ₀) (n₁ - n₀)
      rw [hn₁, mul_one] at a1; rw [hℓ₂, one_mul] at a2
      have hl02 : ‖ℓ₂ - ℓ₀‖ ≤ 2 * dl := by
        have := norm_add_le (ℓ₂ - ℓ₁) (ℓ₁ - ℓ₀)
        rw [sub_add_sub_cancel] at this; linarith
      have a3' : ‖ℓ₂ - ℓ₀‖ * ‖n₁ - n₀‖ ≤ 2 * dl * dn :=
        mul_le_mul hl02 hdn₀ (norm_nonneg _) (by positivity)
      have := abs_add_le (⟪ℓ₂ - 2 • ℓ₁ + ℓ₀, n₁⟫ + ⟪ℓ₂, n₂ - 2 • n₁ + n₀⟫) ⟪ℓ₂ - ℓ₀, n₁ - n₀⟫
      have := abs_add_le ⟪ℓ₂ - 2 • ℓ₁ + ℓ₀, n₁⟫ ⟪ℓ₂, n₂ - 2 • n₁ + n₀⟫
      linarith
    rw [id1]
    unfold latD2m
    have u1 : ‖(⟪ℓ₂, n₂⟫ - 2 * ⟪ℓ₁, n₁⟫ + ⟪ℓ₀, n₀⟫) • n₁‖ ≤ d2l + d2n + 2 * dl * dn := by
      rw [norm_smul, hn₁, mul_one, Real.norm_eq_abs]; exact bf
    have u2 : ‖⟪ℓ₂, n₂⟫ • (n₂ - 2 • n₁ + n₀)‖ ≤ sb * d2n := by
      rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul hf₂ hd2n (norm_nonneg _) hsb0
    have u3 : ‖(⟪ℓ₂, n₂⟫ - ⟪ℓ₀, n₀⟫) • (n₁ - n₀)‖ ≤ 2 * (dl + dn) * dn := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul df02 hdn₀ (norm_nonneg _) (by positivity)
    have v1 := norm_add_le (-(ℓ₂ - 2 • ℓ₁ + ℓ₀))
      ((⟪ℓ₂, n₂⟫ - 2 * ⟪ℓ₁, n₁⟫ + ⟪ℓ₀, n₀⟫) • n₁ + ⟪ℓ₂, n₂⟫ • (n₂ - 2 • n₁ + n₀)
          + (⟪ℓ₂, n₂⟫ - ⟪ℓ₀, n₀⟫) • (n₁ - n₀))
    have v2 := norm_add_le ((⟪ℓ₂, n₂⟫ - 2 * ⟪ℓ₁, n₁⟫ + ⟪ℓ₀, n₀⟫) • n₁
      + ⟪ℓ₂, n₂⟫ • (n₂ - 2 • n₁ + n₀)) ((⟪ℓ₂, n₂⟫ - ⟪ℓ₀, n₀⟫) • (n₁ - n₀))
    have v3 := norm_add_le ((⟪ℓ₂, n₂⟫ - 2 * ⟪ℓ₁, n₁⟫ + ⟪ℓ₀, n₀⟫) • n₁)
      (⟪ℓ₂, n₂⟫ • (n₂ - 2 • n₁ + n₀))
    rw [norm_neg] at v1
    linarith
  have E5 : ‖D‖ ≤ latD2b2 sb dn dl d2n d2l := by
    have id : D = r₁ • (m₂ - 2 • m₁ + m₀) + (r₂ - r₁) • m₂ - (r₁ - r₀) • m₀ := by
      rw [hD, hB₀, hB₁, hB₂]; module
    rw [id]
    unfold latD2b2
    refine (norm_sub_le _ _).trans ?_
    have n2 := norm_latRaw_le_one hn₂ hℓ₂
    have n0 := norm_latRaw_le_one hn₀ hℓ₀
    have t1 : ‖r₁ • (m₂ - 2 • m₁ + m₀)‖ ≤ latD2m sb dn dl d2n d2l / M := by
      rw [norm_smul, Real.norm_of_nonneg r1nn, div_eq_mul_one_div, mul_comm (latD2m _ _ _ _ _)]
      exact mul_le_mul r1le E6 (norm_nonneg _) (by positivity)
    have t2 : ‖(r₂ - r₁) • m₂‖ ≤ sb * (dl + dn) / M ^ 3 := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |r₂ - r₁| * ‖m₂‖ ≤ sb * (dl + dn) / M ^ 3 * 1 :=
            mul_le_mul dr12 n2 (norm_nonneg _) (by positivity)
        _ = _ := mul_one _
    have t3 : ‖(r₁ - r₀) • m₀‖ ≤ sb * (dl + dn) / M ^ 3 := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |r₁ - r₀| * ‖m₀‖ ≤ sb * (dl + dn) / M ^ 3 * 1 :=
            mul_le_mul dr01 n0 (norm_nonneg _) (by positivity)
        _ = _ := mul_one _
    have := norm_add_le (r₁ • (m₂ - 2 • m₁ + m₀)) ((r₂ - r₁) • m₂)
    linarith
  -- assemble
  unfold latDYaw
  have g1 : |⟪D, C₂ - C₁⟫| ≤ latD2b2 sb dn dl d2n d2l * db := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul E5 hdb.2.1 (norm_nonneg _) ((norm_nonneg _).trans E5)
  have g2 : |⟪B₁ - B₀, C₂ - C₀⟫| ≤ db * (2 * db) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have : ‖C₂ - C₀‖ ≤ 2 * db := by
      have := norm_add_le (C₂ - C₁) (C₁ - C₀)
      rw [sub_add_sub_cancel] at this; linarith [hdb.1, hdb.2.1]
    exact mul_le_mul hdb.2.2.1 this (norm_nonneg _) hdb0
  rw [abs_div, abs_neg, abs_two]
  have := abs_add_le (2 * ⟪D, C₁⟫ + ⟪D, C₂ - C₁⟫) ⟪B₁ - B₀, C₂ - C₀⟫
  have := abs_add_le (2 * ⟪D, C₁⟫) ⟪D, C₂ - C₁⟫
  rw [abs_mul, abs_two] at this
  linarith

omit hdn₁ hdl₀ hdl₁ hd2l in
/-- **Change of the roll and pitch components** over two steps. -/
theorem lat_aVec_rp_second :
    ((aVec (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁) (lat1 ℓ₂ n₂) (lat2 ℓ₂ n₂)).ofLp 0
        - (aVec (lat1 ℓ₀ n₀) (lat2 ℓ₀ n₀) (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁)).ofLp 0) ^ 2
      + ((aVec (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁) (lat1 ℓ₂ n₂) (lat2 ℓ₂ n₂)).ofLp 1
        - (aVec (lat1 ℓ₀ n₀) (lat2 ℓ₀ n₀) (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁)).ofLp 1) ^ 2
      ≤ (xn + d2n * db + 2 * dn * db) ^ 2 := by
  have f0 : |⟪ℓ₀, n₀⟫| < 1 := hf₀.trans_lt hsb
  have f1 : |⟪ℓ₁, n₁⟫| < 1 := hf₁.trans_lt hsb
  have f2 : |⟪ℓ₂, n₂⟫| < 1 := hf₂.trans_lt hsb
  have hdn0 : 0 ≤ dn := (norm_nonneg _).trans hdn₀
  have hdb0 : 0 ≤ db := (norm_nonneg _).trans hdb.1
  have hd2n0 : 0 ≤ d2n := (norm_nonneg _).trans hd2n
  have hxn0 : 0 ≤ xn := (norm_nonneg _).trans hxn
  set C₀ := lat1 ℓ₀ n₀; set C₁ := lat1 ℓ₁ n₁; set C₂ := lat1 ℓ₂ n₂
  set B₀ := lat2 ℓ₀ n₀; set B₁ := lat2 ℓ₁ n₁; set B₂ := lat2 ℓ₂ n₂
  obtain ⟨e0, e1, -⟩ := aVec_ofLp_diff (c₁ := C₁) (c₂ := B₁)
    (lat1_unit hn₀ hℓ₀ f0) (lat2_unit hn₀ hℓ₀ f0) inner_lat1_lat2 inner_lat1_lat2
  obtain ⟨g0, g1, -⟩ := aVec_ofLp_diff (c₁ := C₂) (c₂ := B₂)
    (lat1_unit hn₁ hℓ₁ f1) (lat2_unit hn₁ hℓ₁ f1) inner_lat1_lat2 inner_lat1_lat2
  have k0 : cross C₀ B₀ = n₀ := cross_lat1_lat2 hn₀ hℓ₀ f0
  have k1 : cross C₁ B₁ = n₁ := cross_lat1_lat2 hn₁ hℓ₁ f1
  have k2 : cross C₂ B₂ = n₂ := cross_lat1_lat2 hn₂ hℓ₂ f2
  rw [k0, k1] at e0 e1
  rw [k1, k2] at g0 g1
  set N := n₂ - 2 • n₁ + n₀ with hN
  have E0 : (aVec C₁ B₁ C₂ B₂).ofLp 0 - (aVec C₀ B₀ C₁ B₁).ofLp 0
      = -⟪N, B₁⟫ + (-(⟪N, B₂ - B₁⟫ + ⟪n₁ - n₀, B₂ - B₀⟫) / 2) := by
    rw [e0, g0, hN]; simp only [two_smul, inner_add_left, inner_sub_left, inner_sub_right]; ring
  have E1 : (aVec C₁ B₁ C₂ B₂).ofLp 1 - (aVec C₀ B₀ C₁ B₁).ofLp 1
      = ⟪N, C₁⟫ + (⟪N, C₂ - C₁⟫ + ⟪n₁ - n₀, C₂ - C₀⟫) / 2 := by
    rw [e1, g1, hN]; simp only [two_smul, inner_add_left, inner_sub_left, inner_sub_right]; ring
  rw [E0, E1]
  -- main part
  have P : (-⟪N, B₁⟫) ^ 2 + ⟪N, C₁⟫ ^ 2 ≤ xn ^ 2 := by
    have B := bessel_pair (lat1_unit hn₁ hℓ₁ f1) (lat2_unit hn₁ hℓ₁ f1) inner_lat1_lat2 N
    rw [k1] at B
    have hc := norm_cross_sq n₁ N
    rw [hn₁] at hc
    have hx2 : ‖cross n₁ N‖ ^ 2 ≤ xn ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxn 2
    rw [real_inner_comm N B₁, real_inner_comm N C₁] at B
    rw [real_inner_comm N n₁] at B
    have : ⟪N, n₁⟫ ^ 2 = ⟪n₁, N⟫ ^ 2 := by rw [real_inner_comm]
    nlinarith [sq_nonneg ⟪n₁, N⟫]
  -- remainder
  have hB : ‖B₂ - B₀‖ ≤ 2 * db := by
    have := norm_add_le (B₂ - B₁) (B₁ - B₀); rw [sub_add_sub_cancel] at this
    linarith [hdb.2.2.1, hdb.2.2.2]
  have hC : ‖C₂ - C₀‖ ≤ 2 * db := by
    have := norm_add_le (C₂ - C₁) (C₁ - C₀); rw [sub_add_sub_cancel] at this
    linarith [hdb.1, hdb.2.1]
  have q0 : |-(⟪N, B₂ - B₁⟫ + ⟪n₁ - n₀, B₂ - B₀⟫) / 2| ≤ (d2n * db + dn * (2 * db)) / 2 := by
    rw [abs_div, abs_neg, abs_two]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul hd2n hdb.2.2.2 (norm_nonneg _) hd2n0)
    · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul hdn₀ hB (norm_nonneg _) hdn0)
  have q1 : |(⟪N, C₂ - C₁⟫ + ⟪n₁ - n₀, C₂ - C₀⟫) / 2| ≤ (d2n * db + dn * (2 * db)) / 2 := by
    rw [abs_div, abs_two]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul hd2n hdb.2.1 (norm_nonneg _) hd2n0)
    · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul hdn₀ hC (norm_nonneg _) hdn0)
  set w₀ := -(⟪N, B₂ - B₁⟫ + ⟪n₁ - n₀, B₂ - B₀⟫) / 2
  set w₁ := (⟪N, C₂ - C₁⟫ + ⟪n₁ - n₀, C₂ - C₀⟫) / 2
  have hw : w₀ ^ 2 + w₁ ^ 2 ≤ (d2n * db + 2 * dn * db) ^ 2 := by
    have a0 : w₀ ^ 2 ≤ ((d2n * db + dn * (2 * db)) / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) q0 2
    have a1 : w₁ ^ 2 ≤ ((d2n * db + dn * (2 * db)) / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) q1 2
    have eqA : d2n * db + dn * (2 * db) = d2n * db + 2 * dn * db := by ring
    rw [eqA] at a0 a1
    have h4 : ((d2n * db + 2 * dn * db) / 2) ^ 2 = (d2n * db + 2 * dn * db) ^ 2 / 4 := by ring
    have h5 := sq_nonneg (d2n * db + 2 * dn * db)
    linarith
  have := sq2_add_le hxn0 (by positivity) P hw
  calc _ ≤ (xn + (d2n * db + 2 * dn * db)) ^ 2 := this
    _ = (xn + d2n * db + 2 * dn * db) ^ 2 := by ring

end Second


/-- **Crude frame steps** (used only to show consecutive frames are close). -/
theorem lat_steps_crude {ℓ₀ ℓ₁ n₀ n₁ : E3} {sb dn dl : ℝ}
    (hn₀ : ‖n₀‖ = 1) (hn₁ : ‖n₁‖ = 1) (hℓ₀ : ‖ℓ₀‖ = 1) (hℓ₁ : ‖ℓ₁‖ = 1)
    (hf₀ : |⟪ℓ₀, n₀⟫| ≤ sb) (hf₁ : |⟪ℓ₁, n₁⟫| ≤ sb) (hsb : sb < 1)
    (hdn : ‖n₁ - n₀‖ ≤ dn) (hdl : ‖ℓ₁ - ℓ₀‖ ≤ dl) :
    ‖lat2 ℓ₁ n₁ - lat2 ℓ₀ n₀‖ ≤ (2 * dl + 2 * dn) / √(1 - sb ^ 2) ∧
    ‖lat1 ℓ₁ n₁ - lat1 ℓ₀ n₀‖ ≤ (2 * dl + 2 * dn) / √(1 - sb ^ 2) + dn := by
  have hsb0 : 0 ≤ sb := (abs_nonneg _).trans hf₀
  have hs : 0 < √(1 - sb ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hM : ∀ {ℓ n : E3}, ‖n‖ = 1 → ‖ℓ‖ = 1 → |⟪ℓ, n⟫| ≤ sb →
      √(1 - sb ^ 2) ≤ ‖latRaw ℓ n‖ := by
    intro ℓ n hn hℓ hf
    rw [norm_latRaw hn hℓ]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_abs ⟪ℓ, n⟫, abs_nonneg ⟪ℓ, n⟫]
  have hraw : ‖latRaw ℓ₁ n₁ - latRaw ℓ₀ n₀‖ ≤ 2 * dl + 2 * dn := by
    have e : latRaw ℓ₁ n₁ - latRaw ℓ₀ n₀ = -(ℓ₁ - ℓ₀) + ((⟪ℓ₁, n₁⟫ - ⟪ℓ₀, n₀⟫) • n₁
        + ⟪ℓ₀, n₀⟫ • (n₁ - n₀)) := by simp only [latRaw]; module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    have t1 : ‖(⟪ℓ₁, n₁⟫ - ⟪ℓ₀, n₀⟫) • n₁‖ ≤ dl + dn := by
      rw [norm_smul, hn₁, mul_one, Real.norm_eq_abs]
      exact (abs_inner_sub_inner_le hℓ₀ hn₁).trans (add_le_add hdl hdn)
    have t2 : ‖⟪ℓ₀, n₀⟫ • (n₁ - n₀)‖ ≤ dn := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |⟪ℓ₀, n₀⟫| * ‖n₁ - n₀‖ ≤ 1 * dn :=
            mul_le_mul (hf₀.trans hsb.le) hdn (norm_nonneg _) zero_le_one
        _ = dn := one_mul _
    have := norm_add_le ((⟪ℓ₁, n₁⟫ - ⟪ℓ₀, n₀⟫) • n₁) (⟪ℓ₀, n₀⟫ • (n₁ - n₀))
    linarith
  have h2 : ‖lat2 ℓ₁ n₁ - lat2 ℓ₀ n₀‖ ≤ (2 * dl + 2 * dn) / √(1 - sb ^ 2) :=
    (norm_nrm_sub_le_sharp hs (hM hn₁ hℓ₁ hf₁) (hM hn₀ hℓ₀ hf₀)).trans
      (div_le_div_of_nonneg_right hraw hs.le)
  refine ⟨h2, ?_⟩
  have e : lat1 ℓ₁ n₁ - lat1 ℓ₀ n₀
      = cross (lat2 ℓ₁ n₁ - lat2 ℓ₀ n₀) n₁ + cross (lat2 ℓ₀ n₀) (n₁ - n₀) := by
    simp only [lat1]
    ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_cross_le _ _).trans ?_; rw [hn₁, mul_one]; exact h2
  · refine (norm_cross_le _ _).trans ?_
    rw [lat2_unit hn₀ hℓ₀ (hf₀.trans_lt hsb), one_mul]; exact hdn

end VisionTracking

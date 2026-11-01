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


/-- The up-components of the lateral frame when `ℓ = up × ĥ` with `ĥ` horizontal. -/
theorem lat_up_coords {hh n : E3} (hhu : ⟪hh, up⟫ = 0) :
    ⟪lat1 (cross up hh) n, up⟫ = ‖latRaw (cross up hh) n‖⁻¹ * ⟪hh, n⟫ ∧
    ⟪lat2 (cross up hh) n, up⟫ = ‖latRaw (cross up hh) n‖⁻¹ * (⟪cross up hh, n⟫ * ⟪n, up⟫) := by
  have huu : ⟪up, up⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_up']; norm_num
  have hlu : ⟪cross up hh, up⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_left _ _
  constructor
  · rw [lat1, lat2, nrm, cross_smul_left, real_inner_smul_left]
    congr 1
    have e1 : ∀ a : E3, ∀ c : ℝ, cross (-a + c • n) n = -cross a n := by
      intro a c; ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring_nf <;> simp
    rw [latRaw, e1, cross_cross_eq, inner_neg_left, inner_sub_left, real_inner_smul_left,
      real_inner_smul_left, huu, hhu]
    ring
  · rw [lat2, nrm, real_inner_smul_left, latRaw, inner_add_left, inner_neg_left,
      real_inner_smul_left, hlu]
    ring

end VisionTracking

import VisionTracking.LateralFrame

/-!
# Sharp change of the body-rate vector

For three consecutive orthonormal frames `b, c, e`, the change of the body-rate vector
(`aVec`, the antisymmetric part of the frame step) is exactly the second difference of the
frame read in the middle frame, plus products of *consecutive steps*:

* roll/pitch: `-⟪c₂, Δ²b₃⟫ - ½ (P₃₂)`, `⟪c₁, Δ²b₃⟫ + ½ (P₃₁)`;
* yaw: `-⟪c₁, Δ²b₂⟫ - ½ (P₁₂)`,

where `P_ij = ⟪Δ'bᵢ, Δ'bⱼ⟫ + ⟪Δbᵢ, Δbⱼ⟫`. Each product is bounded by a *tilt × twist* term
(plus third-order terms), not by the square of the whole frame step.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

theorem parseval3 {b₁ b₂ : E3} (h₁ : ‖b₁‖ = 1) (h₂ : ‖b₂‖ = 1) (h₁₂ : ⟪b₁, b₂⟫ = 0)
    (u v : E3) :
    ⟪u, v⟫ = ⟪b₁, u⟫ * ⟪b₁, v⟫ + ⟪b₂, u⟫ * ⟪b₂, v⟫ + ⟪cross b₁ b₂, u⟫ * ⟪cross b₁ b₂, v⟫ := by
  have h1 := bessel_pair h₁ h₂ h₁₂ (u + v)
  have h2 := bessel_pair h₁ h₂ h₁₂ (u - v)
  rw [norm_add_sq_real] at h1; rw [norm_sub_sq_real] at h2
  simp only [inner_add_right, inner_sub_right] at h1 h2
  linear_combination (h2 - h1) / 4

theorem abs_inner_unit_sub_one_le {b c : E3} {e : ℝ} (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (h : ‖c - b‖ ≤ e) : |⟪b, c⟫ - 1| ≤ e ^ 2 / 2 := by
  have k : ⟪b, c⟫ - 1 = -(‖c - b‖ ^ 2 / 2) := by
    rw [norm_sub_sq_real, hb, hc, real_inner_comm]; ring
  rw [k, abs_neg, abs_of_nonneg (by positivity)]
  have := pow_le_pow_left₀ (norm_nonneg _) h 2
  linarith

theorem abs_mul_le_of {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

theorem abs_sum3_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| :=
  (abs_add_le _ _).trans (by linarith [abs_add_le a b])

theorem abs_mul_le_half_sq (x y : ℝ) : |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

theorem abs_inner_le_of {b x : E3} {e : ℝ} (hb : ‖b‖ = 1) (h : ‖x‖ ≤ e) : |⟪b, x⟫| ≤ e := by
  have := abs_real_inner_le_norm b x; rw [hb, one_mul] at this; exact this.trans h

section Step

variable {b₁ b₂ c₁ c₂ : E3} (hb₁ : ‖b₁‖ = 1) (hb₂ : ‖b₂‖ = 1) (hb : ⟪b₁, b₂⟫ = 0)
  (hc₁ : ‖c₁‖ = 1) (hc₂ : ‖c₂‖ = 1) (hc : ⟪c₁, c₂⟫ = 0)
include hb₁ hb₂ hb hc₁ hc₂ hc

omit hc₁ hc₂ in
/-- **Twist of one step**, from the yaw component of the step. -/
theorem twist_le {tw db : ℝ} (hy : |(aVec b₁ b₂ c₁ c₂).ofLp 2| ≤ tw)
    (h1 : ‖c₁ - b₁‖ ≤ db) (h2 : ‖c₂ - b₂‖ ≤ db) :
    |⟪b₁, c₂⟫| ≤ tw + db ^ 2 / 2 ∧ |⟪b₂, c₁⟫| ≤ tw + db ^ 2 / 2 := by
  obtain ⟨-, -, e2⟩ := aVec_ofLp_diff (c₁ := c₁) (c₂ := c₂) hb₁ hb₂ hb hc
  have hdb : 0 ≤ db := (norm_nonneg _).trans h1
  have hX : |⟪c₁ - b₁, c₂ - b₂⟫| ≤ db ^ 2 := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := mul_le_mul h1 h2 (norm_nonneg _) hdb; nlinarith
  have k1 := real_inner_comm c₁ c₂; have k2 := real_inner_comm b₁ b₂
  have k3 := real_inner_comm b₁ c₂; have k4 := real_inner_comm b₂ c₁
  have eX : ⟪c₁ - b₁, c₂ - b₂⟫ = -⟪b₂, c₁⟫ - ⟪b₁, c₂⟫ := by
    simp only [inner_sub_left, inner_sub_right]; linarith
  have ea : (aVec b₁ b₂ c₁ c₂).ofLp 2 = (⟪b₂, c₁⟫ - ⟪b₁, c₂⟫) / 2 := by
    rw [e2]; simp only [inner_sub_left]; linarith
  rw [ea] at hy; rw [eX] at hX
  rw [abs_le] at hy hX
  constructor <;> rw [abs_le] <;> constructor <;> linarith [hy.1, hy.2, hX.1, hX.2]

/-- **Products of one step's frame changes.** -/
theorem step_prod {dn db T : ℝ} (hn : ‖cross c₁ c₂ - cross b₁ b₂‖ ≤ dn)
    (h1 : ‖c₁ - b₁‖ ≤ db) (h2 : ‖c₂ - b₂‖ ≤ db)
    (t1 : |⟪b₁, c₂⟫| ≤ T) (t2 : |⟪b₂, c₁⟫| ≤ T) :
    |⟪cross c₁ c₂ - cross b₁ b₂, c₂ - b₂⟫| ≤ dn * T + dn * (db ^ 2 / 2) + dn ^ 2 / 2 * db ∧
    |⟪cross c₁ c₂ - cross b₁ b₂, c₁ - b₁⟫| ≤ dn * (db ^ 2 / 2) + dn * T + dn ^ 2 / 2 * db ∧
    |⟪c₁ - b₁, c₂ - b₂⟫| ≤ db ^ 2 / 2 * T + T * (db ^ 2 / 2) + dn ^ 2 / 2 := by
  set b₃ := cross b₁ b₂ with hb₃
  set c₃ := cross c₁ c₂ with hc₃
  have hb3 : ‖b₃‖ = 1 := norm_cross_of_orthonormal hb₁ hb₂ hb
  have hc3 : ‖c₃‖ = 1 := norm_cross_of_orthonormal hc₁ hc₂ hc
  have o31 : ⟪b₃, b₁⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_left _ _
  have o32 : ⟪b₃, b₂⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_right _ _
  have p31 : ⟪c₁, c₃⟫ = 0 := inner_cross_left _ _
  have p32 : ⟪c₂, c₃⟫ = 0 := inner_cross_right _ _
  have o21 : ⟪b₂, b₁⟫ = 0 := by rw [real_inner_comm]; exact hb
  have hb33 : ⟪b₃, b₃⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hb3]; norm_num
  have hb11 : ⟪b₁, b₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hb₁]; norm_num
  have hb22 : ⟪b₂, b₂⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hb₂]; norm_num
  have hdn : 0 ≤ dn := (norm_nonneg _).trans hn
  have hdb : 0 ≤ db := (norm_nonneg _).trans h1
  -- coordinates of the step vectors in frame `b`
  have u1 : |⟪b₁, c₃ - b₃⟫| ≤ dn := abs_inner_le_of hb₁ hn
  have u2 : |⟪b₂, c₃ - b₃⟫| ≤ dn := abs_inner_le_of hb₂ hn
  have u3 : |⟪b₃, c₃ - b₃⟫| ≤ dn ^ 2 / 2 := by
    rw [inner_sub_right, hb33]; exact abs_inner_unit_sub_one_le hb3 hc3 hn
  have v12 : |⟪b₁, c₂ - b₂⟫| ≤ T := by rw [inner_sub_right, hb, sub_zero]; exact t1
  have v22 : |⟪b₂, c₂ - b₂⟫| ≤ db ^ 2 / 2 := by
    rw [inner_sub_right, hb22]; exact abs_inner_unit_sub_one_le hb₂ hc₂ h2
  have v32 : |⟪b₃, c₂ - b₂⟫| ≤ db := abs_inner_le_of hb3 h2
  have v11 : |⟪b₁, c₁ - b₁⟫| ≤ db ^ 2 / 2 := by
    rw [inner_sub_right, hb11]; exact abs_inner_unit_sub_one_le hb₁ hc₁ h1
  have v21 : |⟪b₂, c₁ - b₁⟫| ≤ T := by rw [inner_sub_right, o21, sub_zero]; exact t2
  have v31 : |⟪b₃, c₁ - b₁⟫| ≤ db := abs_inner_le_of hb3 h1
  refine ⟨?_, ?_, ?_⟩
  · rw [parseval3 hb₁ hb₂ hb]
    refine (abs_sum3_le _ _ _).trans ?_
    linarith [abs_mul_le_of u1 v12, abs_mul_le_of u2 v22, abs_mul_le_of u3 v32]
  · rw [parseval3 hb₁ hb₂ hb]
    refine (abs_sum3_le _ _ _).trans ?_
    linarith [abs_mul_le_of u1 v11, abs_mul_le_of u2 v21, abs_mul_le_of u3 v31]
  · rw [parseval3 hb₁ hb₂ hb]
    refine (abs_sum3_le _ _ _).trans ?_
    have w1 : |⟪b₁, c₁ - b₁⟫ * ⟪b₁, c₂ - b₂⟫| ≤ db ^ 2 / 2 * T := abs_mul_le_of v11 v12
    have w2 : |⟪b₂, c₁ - b₁⟫ * ⟪b₂, c₂ - b₂⟫| ≤ T * (db ^ 2 / 2) := abs_mul_le_of v21 v22
    -- the tilt × tilt term, via Bessel in frame `c`
    have w3 : |⟪b₃, c₁ - b₁⟫ * ⟪b₃, c₂ - b₂⟫| ≤ dn ^ 2 / 2 := by
      have e1 : ⟪b₃, c₁ - b₁⟫ = ⟪c₁, b₃ - c₃⟫ := by
        rw [inner_sub_right, o31, sub_zero, inner_sub_right, p31, sub_zero, real_inner_comm]
      have e2 : ⟪b₃, c₂ - b₂⟫ = ⟪c₂, b₃ - c₃⟫ := by
        rw [inner_sub_right, o32, sub_zero, inner_sub_right, p32, sub_zero, real_inner_comm]
      rw [e1, e2]
      have B := bessel_pair hc₁ hc₂ hc (b₃ - c₃)
      have hw : ‖b₃ - c₃‖ ^ 2 ≤ dn ^ 2 := by
        rw [norm_sub_rev]; exact pow_le_pow_left₀ (norm_nonneg _) hn 2
      refine (abs_mul_le_half_sq _ _).trans ?_
      have := sq_nonneg ⟪cross c₁ c₂, b₃ - c₃⟫
      linarith
    linarith

end Step

section TwoSteps

variable {b₁ b₂ c₁ c₂ e₁ e₂ : E3} (hb₁ : ‖b₁‖ = 1) (hb₂ : ‖b₂‖ = 1) (hb : ⟪b₁, b₂⟫ = 0)
  (hc₁ : ‖c₁‖ = 1) (hc₂ : ‖c₂‖ = 1) (hc : ⟪c₁, c₂⟫ = 0) (he : ⟪e₁, e₂⟫ = 0)
include hb₁ hb₂ hb hc₁ hc₂ hc he

/-- **Exact change of the yaw component.** -/
theorem dav_yaw_eq : (aVec c₁ c₂ e₁ e₂).ofLp 2 - (aVec b₁ b₂ c₁ c₂).ofLp 2
    = -⟪c₁, e₂ - 2 • c₂ + b₂⟫ - (⟪e₁ - c₁, e₂ - c₂⟫ + ⟪c₁ - b₁, c₂ - b₂⟫) / 2 := by
  obtain ⟨-, -, f⟩ := aVec_ofLp_diff (c₁ := c₁) (c₂ := c₂) hb₁ hb₂ hb hc
  obtain ⟨-, -, g⟩ := aVec_ofLp_diff (c₁ := e₁) (c₂ := e₂) hc₁ hc₂ hc he
  rw [f, g]
  simp only [two_smul, inner_sub_left, inner_add_right, inner_sub_right]
  linarith [real_inner_comm c₁ c₂, real_inner_comm b₁ b₂, real_inner_comm e₁ e₂,
    real_inner_comm b₁ c₂, real_inner_comm b₂ c₁, real_inner_comm c₁ e₂, real_inner_comm c₂ e₁,
    real_inner_comm b₁ e₂, real_inner_comm b₂ e₁]

/-- **Exact change of the roll/pitch components.** -/
theorem dav_rp_eq :
    (aVec c₁ c₂ e₁ e₂).ofLp 0 - (aVec b₁ b₂ c₁ c₂).ofLp 0
      = -⟪c₂, cross e₁ e₂ - 2 • cross c₁ c₂ + cross b₁ b₂⟫
        - (⟪cross e₁ e₂ - cross c₁ c₂, e₂ - c₂⟫ + ⟪cross c₁ c₂ - cross b₁ b₂, c₂ - b₂⟫) / 2 ∧
    (aVec c₁ c₂ e₁ e₂).ofLp 1 - (aVec b₁ b₂ c₁ c₂).ofLp 1
      = ⟪c₁, cross e₁ e₂ - 2 • cross c₁ c₂ + cross b₁ b₂⟫
        + (⟪cross e₁ e₂ - cross c₁ c₂, e₁ - c₁⟫ + ⟪cross c₁ c₂ - cross b₁ b₂, c₁ - b₁⟫) / 2 := by
  obtain ⟨f0, f1, -⟩ := aVec_ofLp_diff (c₁ := c₁) (c₂ := c₂) hb₁ hb₂ hb hc
  obtain ⟨g0, g1, -⟩ := aVec_ofLp_diff (c₁ := e₁) (c₂ := e₂) hc₁ hc₂ hc he
  set b₃ := cross b₁ b₂; set c₃ := cross c₁ c₂; set e₃ := cross e₁ e₂
  have q1 : ⟪b₁, b₃⟫ = 0 := inner_cross_left _ _
  have q2 : ⟪b₂, b₃⟫ = 0 := inner_cross_right _ _
  have q3 : ⟪c₁, c₃⟫ = 0 := inner_cross_left _ _
  have q4 : ⟪c₂, c₃⟫ = 0 := inner_cross_right _ _
  have q5 : ⟪e₁, e₃⟫ = 0 := inner_cross_left _ _
  have q6 : ⟪e₂, e₃⟫ = 0 := inner_cross_right _ _
  constructor
  · rw [f0, g0]
    simp only [two_smul, inner_sub_left, inner_add_right, inner_sub_right]
    linarith [real_inner_comm c₂ c₃, real_inner_comm b₂ b₃, real_inner_comm e₂ e₃,
      real_inner_comm c₂ e₃, real_inner_comm c₃ e₂, real_inner_comm b₂ c₃, real_inner_comm b₃ c₂,
      real_inner_comm b₂ e₃, real_inner_comm b₃ e₂]
  · rw [f1, g1]
    simp only [two_smul, inner_sub_left, inner_add_right, inner_sub_right]
    linarith [real_inner_comm c₁ c₃, real_inner_comm b₁ b₃, real_inner_comm e₁ e₃,
      real_inner_comm c₁ e₃, real_inner_comm c₃ e₁, real_inner_comm b₁ c₃, real_inner_comm b₃ c₁,
      real_inner_comm b₁ e₃, real_inner_comm b₃ e₁]

end TwoSteps

section Lateral

/-- First-order twist bound of the lateral-locked frame. -/
noncomputable def latTw (sb dn dl : ℝ) : ℝ := (dl + sb * dn) / √(1 - sb ^ 2)

/-- Bound on the yaw curvature `⟪b₁, Δ²b₂⟫` of the lateral-locked frame. -/
noncomputable def latYawCore (sb dn dl xn d2l : ℝ) : ℝ :=
  (d2l + sb * xn + 2 * (dl + dn) * dn) / √(1 - sb ^ 2)
    + 2 * (sb * (dl + dn) / √(1 - sb ^ 2) ^ 3) * (dl + sb * dn)

/-- Sharp bound on the change of the yaw component. -/
noncomputable def latYawSharp (sb dn dl xn d2l db : ℝ) : ℝ :=
  latYawCore sb dn dl xn d2l + dn ^ 2 / 2 + db ^ 2 * (latTw sb dn dl + db ^ 2 / 2)

/-- Sharp bound on the change of the roll/pitch components. -/
noncomputable def latRpSharp (sb dn dl xn db : ℝ) : ℝ :=
  xn + √2 * dn * (latTw sb dn dl + db ^ 2 + dn * db / 2)

variable {ℓ₀ ℓ₁ ℓ₂ n₀ n₁ n₂ : E3} {sb dn dl xn d2l db : ℝ}
  (hn₀ : ‖n₀‖ = 1) (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1)
  (hℓ₀ : ‖ℓ₀‖ = 1) (hℓ₁ : ‖ℓ₁‖ = 1) (hℓ₂ : ‖ℓ₂‖ = 1)
  (hf₀ : |⟪ℓ₀, n₀⟫| ≤ sb) (hf₁ : |⟪ℓ₁, n₁⟫| ≤ sb) (hf₂ : |⟪ℓ₂, n₂⟫| ≤ sb) (hsb : sb < 1)
  (hdn₀ : ‖n₁ - n₀‖ ≤ dn) (hdn₁ : ‖n₂ - n₁‖ ≤ dn)
  (hdl₀ : ‖ℓ₁ - ℓ₀‖ ≤ dl) (hdl₁ : ‖ℓ₂ - ℓ₁‖ ≤ dl)
  (hxn : ‖cross n₁ (n₂ - 2 • n₁ + n₀)‖ ≤ xn)
  (hd2l : ‖ℓ₂ - 2 • ℓ₁ + ℓ₀‖ ≤ d2l)

include hn₀ hn₁ hn₂ hℓ₀ hℓ₁ hℓ₂ hf₀ hf₁ hf₂ hsb hdn₀ hdn₁ hdl₀ hdl₁ hxn hd2l in
/-- **Yaw curvature of the lateral-locked frame.** -/
theorem lat_D_lat1_le :
    |⟪lat2 ℓ₂ n₂ - 2 • lat2 ℓ₁ n₁ + lat2 ℓ₀ n₀, lat1 ℓ₁ n₁⟫| ≤ latYawCore sb dn dl xn d2l := by
  have f0 : |⟪ℓ₀, n₀⟫| < 1 := hf₀.trans_lt hsb
  have f1 : |⟪ℓ₁, n₁⟫| < 1 := hf₁.trans_lt hsb
  have f2 : |⟪ℓ₂, n₂⟫| < 1 := hf₂.trans_lt hsb
  have hsb0 : 0 ≤ sb := (abs_nonneg _).trans hf₀
  have hs : 0 < √(1 - sb ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  set M := √(1 - sb ^ 2) with hMdef
  have hdn0 : 0 ≤ dn := (norm_nonneg _).trans hdn₀
  have hdl0 : 0 ≤ dl := (norm_nonneg _).trans hdl₀
  set C₀ := lat1 ℓ₀ n₀; set C₁ := lat1 ℓ₁ n₁; set C₂ := lat1 ℓ₂ n₂
  set B₀ := lat2 ℓ₀ n₀; set B₁ := lat2 ℓ₁ n₁; set B₂ := lat2 ℓ₂ n₂
  set D := B₂ - 2 • B₁ + B₀ with hD
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
  exact bE2

include hn₀ hn₁ hℓ₀ hℓ₁ hf₀ hf₁ hsb hdn₀ hdl₀ in
theorem lat_tw_le :
    |(aVec (lat1 ℓ₀ n₀) (lat2 ℓ₀ n₀) (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁)).ofLp 2| ≤ latTw sb dn dl := by
  have hsb0 : 0 ≤ sb := (abs_nonneg _).trans hf₀
  have hM : 0 < √(1 - sb ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  refine (lat_aVec_yaw hn₀ hn₁ hℓ₀ hℓ₁ hf₀ hf₁ hsb).trans (div_le_div_of_nonneg_right ?_ hM.le)
  have := mul_le_mul_of_nonneg_left hdn₀ hsb0
  linarith

variable (hdb : ‖lat1 ℓ₁ n₁ - lat1 ℓ₀ n₀‖ ≤ db ∧ ‖lat1 ℓ₂ n₂ - lat1 ℓ₁ n₁‖ ≤ db ∧
    ‖lat2 ℓ₁ n₁ - lat2 ℓ₀ n₀‖ ≤ db ∧ ‖lat2 ℓ₂ n₂ - lat2 ℓ₁ n₁‖ ≤ db)

include hn₀ hn₁ hn₂ hℓ₀ hℓ₁ hℓ₂ hf₀ hf₁ hf₂ hsb hdn₀ hdn₁ hdl₀ hdl₁ hxn hd2l hdb

/-- **Sharp change of the yaw component.** -/
theorem lat_yaw_sharp :
    |(aVec (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁) (lat1 ℓ₂ n₂) (lat2 ℓ₂ n₂)).ofLp 2
      - (aVec (lat1 ℓ₀ n₀) (lat2 ℓ₀ n₀) (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁)).ofLp 2|
      ≤ latYawSharp sb dn dl xn d2l db := by
  have f0 : |⟪ℓ₀, n₀⟫| < 1 := hf₀.trans_lt hsb
  have f1 : |⟪ℓ₁, n₁⟫| < 1 := hf₁.trans_lt hsb
  have f2 : |⟪ℓ₂, n₂⟫| < 1 := hf₂.trans_lt hsb
  have core := lat_D_lat1_le hn₀ hn₁ hn₂ hℓ₀ hℓ₁ hℓ₂ hf₀ hf₁ hf₂ hsb hdn₀ hdn₁ hdl₀ hdl₁ hxn hd2l
  have t0 := lat_tw_le hn₀ hn₁ hℓ₀ hℓ₁ hf₀ hf₁ hsb hdn₀ hdl₀
  have t1 := lat_tw_le hn₁ hn₂ hℓ₁ hℓ₂ hf₁ hf₂ hsb hdn₁ hdl₁
  have hC₀ := lat1_unit hn₀ hℓ₀ f0; have hB₀ := lat2_unit hn₀ hℓ₀ f0
  have hC₁ := lat1_unit hn₁ hℓ₁ f1; have hB₁ := lat2_unit hn₁ hℓ₁ f1
  have hC₂ := lat1_unit hn₂ hℓ₂ f2; have hB₂ := lat2_unit hn₂ hℓ₂ f2
  have o₀ : ⟪lat1 ℓ₀ n₀, lat2 ℓ₀ n₀⟫ = 0 := inner_lat1_lat2
  have o₁ : ⟪lat1 ℓ₁ n₁, lat2 ℓ₁ n₁⟫ = 0 := inner_lat1_lat2
  have o₂ : ⟪lat1 ℓ₂ n₂, lat2 ℓ₂ n₂⟫ = 0 := inner_lat1_lat2
  obtain ⟨s10, s11, s20, s21⟩ := hdb
  obtain ⟨T0a, T0b⟩ := twist_le hC₀ hB₀ o₀ o₁ t0 s10 s20
  obtain ⟨T1a, T1b⟩ := twist_le hC₁ hB₁ o₁ o₂ t1 s11 s21
  have k0 := cross_lat1_lat2 hn₀ hℓ₀ f0
  have k1 := cross_lat1_lat2 hn₁ hℓ₁ f1
  have k2 := cross_lat1_lat2 hn₂ hℓ₂ f2
  have hn01 : ‖cross (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁) - cross (lat1 ℓ₀ n₀) (lat2 ℓ₀ n₀)‖ ≤ dn := by
    rw [k0, k1]; exact hdn₀
  have hn12 : ‖cross (lat1 ℓ₂ n₂) (lat2 ℓ₂ n₂) - cross (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁)‖ ≤ dn := by
    rw [k1, k2]; exact hdn₁
  obtain ⟨-, -, P0⟩ := step_prod hC₀ hB₀ o₀ hC₁ hB₁ o₁ hn01 s10 s20 T0a T0b
  obtain ⟨-, -, P1⟩ := step_prod hC₁ hB₁ o₁ hC₂ hB₂ o₂ hn12 s11 s21 T1a T1b
  rw [dav_yaw_eq hC₀ hB₀ o₀ hC₁ hB₁ o₁ o₂]
  rw [real_inner_comm] at core
  unfold latYawSharp
  have e : db ^ 2 / 2 * (latTw sb dn dl + db ^ 2 / 2) + (latTw sb dn dl + db ^ 2 / 2) * (db ^ 2 / 2)
      + dn ^ 2 / 2 = db ^ 2 * (latTw sb dn dl + db ^ 2 / 2) + dn ^ 2 / 2 := by ring
  rw [e] at P0 P1
  set X := ⟪lat1 ℓ₁ n₁, lat2 ℓ₂ n₂ - 2 • lat2 ℓ₁ n₁ + lat2 ℓ₀ n₀⟫
  set p1 := ⟪lat1 ℓ₂ n₂ - lat1 ℓ₁ n₁, lat2 ℓ₂ n₂ - lat2 ℓ₁ n₁⟫
  set p0 := ⟪lat1 ℓ₁ n₁ - lat1 ℓ₀ n₀, lat2 ℓ₁ n₁ - lat2 ℓ₀ n₀⟫
  set W := db ^ 2 * (latTw sb dn dl + db ^ 2 / 2)
  rw [abs_le] at core P0 P1 ⊢
  constructor <;> linarith [core.1, core.2, P0.1, P0.2, P1.1, P1.2]

omit hd2l in
/-- **Sharp change of the roll/pitch components.** -/
theorem lat_rp_sharp :
    ((aVec (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁) (lat1 ℓ₂ n₂) (lat2 ℓ₂ n₂)).ofLp 0
        - (aVec (lat1 ℓ₀ n₀) (lat2 ℓ₀ n₀) (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁)).ofLp 0) ^ 2
      + ((aVec (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁) (lat1 ℓ₂ n₂) (lat2 ℓ₂ n₂)).ofLp 1
        - (aVec (lat1 ℓ₀ n₀) (lat2 ℓ₀ n₀) (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁)).ofLp 1) ^ 2
      ≤ latRpSharp sb dn dl xn db ^ 2 := by
  have f0 : |⟪ℓ₀, n₀⟫| < 1 := hf₀.trans_lt hsb
  have f1 : |⟪ℓ₁, n₁⟫| < 1 := hf₁.trans_lt hsb
  have f2 : |⟪ℓ₂, n₂⟫| < 1 := hf₂.trans_lt hsb
  have hsb0 : 0 ≤ sb := (abs_nonneg _).trans hf₀
  have hdn0 : 0 ≤ dn := (norm_nonneg _).trans hdn₀
  have hdl0 : 0 ≤ dl := (norm_nonneg _).trans hdl₀
  have hdb0 : 0 ≤ db := (norm_nonneg _).trans hdb.1
  have hxn0 : 0 ≤ xn := (norm_nonneg _).trans hxn
  have t0 := lat_tw_le hn₀ hn₁ hℓ₀ hℓ₁ hf₀ hf₁ hsb hdn₀ hdl₀
  have t1 := lat_tw_le hn₁ hn₂ hℓ₁ hℓ₂ hf₁ hf₂ hsb hdn₁ hdl₁
  have hC₀ := lat1_unit hn₀ hℓ₀ f0; have hB₀ := lat2_unit hn₀ hℓ₀ f0
  have hC₁ := lat1_unit hn₁ hℓ₁ f1; have hB₁ := lat2_unit hn₁ hℓ₁ f1
  have hC₂ := lat1_unit hn₂ hℓ₂ f2; have hB₂ := lat2_unit hn₂ hℓ₂ f2
  have o₀ : ⟪lat1 ℓ₀ n₀, lat2 ℓ₀ n₀⟫ = 0 := inner_lat1_lat2
  have o₁ : ⟪lat1 ℓ₁ n₁, lat2 ℓ₁ n₁⟫ = 0 := inner_lat1_lat2
  have o₂ : ⟪lat1 ℓ₂ n₂, lat2 ℓ₂ n₂⟫ = 0 := inner_lat1_lat2
  obtain ⟨s10, s11, s20, s21⟩ := hdb
  obtain ⟨T0a, T0b⟩ := twist_le hC₀ hB₀ o₀ o₁ t0 s10 s20
  obtain ⟨T1a, T1b⟩ := twist_le hC₁ hB₁ o₁ o₂ t1 s11 s21
  have k0 := cross_lat1_lat2 hn₀ hℓ₀ f0
  have k1 := cross_lat1_lat2 hn₁ hℓ₁ f1
  have k2 := cross_lat1_lat2 hn₂ hℓ₂ f2
  have hn01 : ‖cross (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁) - cross (lat1 ℓ₀ n₀) (lat2 ℓ₀ n₀)‖ ≤ dn := by
    rw [k0, k1]; exact hdn₀
  have hn12 : ‖cross (lat1 ℓ₂ n₂) (lat2 ℓ₂ n₂) - cross (lat1 ℓ₁ n₁) (lat2 ℓ₁ n₁)‖ ≤ dn := by
    rw [k1, k2]; exact hdn₁
  obtain ⟨Pa0, Pb0, -⟩ := step_prod hC₀ hB₀ o₀ hC₁ hB₁ o₁ hn01 s10 s20 T0a T0b
  obtain ⟨Pa1, Pb1, -⟩ := step_prod hC₁ hB₁ o₁ hC₂ hB₂ o₂ hn12 s11 s21 T1a T1b
  obtain ⟨E0, E1⟩ := dav_rp_eq hC₀ hB₀ o₀ hC₁ hB₁ o₁ o₂
  rw [E0, E1]
  rw [k0, k1] at Pa0 Pb0; rw [k1, k2] at Pa1 Pb1; rw [k0, k1, k2]
  set tw := latTw sb dn dl
  set N := n₂ - 2 • n₁ + n₀
  set K := tw + db ^ 2 + dn * db / 2 with hK
  -- main part
  have P : (-⟪lat2 ℓ₁ n₁, N⟫) ^ 2 + ⟪lat1 ℓ₁ n₁, N⟫ ^ 2 ≤ xn ^ 2 := by
    have B := bessel_pair hC₁ hB₁ o₁ N
    rw [k1] at B
    have hc := norm_cross_sq n₁ N
    rw [hn₁] at hc
    have hx2 : ‖cross n₁ N‖ ^ 2 ≤ xn ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxn 2
    rw [one_pow, one_mul] at hc
    rw [neg_sq]
    linarith
  -- remainder
  set w₀ := -((⟪n₂ - n₁, lat2 ℓ₂ n₂ - lat2 ℓ₁ n₁⟫ + ⟪n₁ - n₀, lat2 ℓ₁ n₁ - lat2 ℓ₀ n₀⟫) / 2)
  set w₁ := (⟪n₂ - n₁, lat1 ℓ₂ n₂ - lat1 ℓ₁ n₁⟫ + ⟪n₁ - n₀, lat1 ℓ₁ n₁ - lat1 ℓ₀ n₀⟫) / 2
  have eK : dn * (tw + db ^ 2 / 2) + dn * (db ^ 2 / 2) + dn ^ 2 / 2 * db = dn * K := by
    rw [hK]; ring
  have eK' : dn * (db ^ 2 / 2) + dn * (tw + db ^ 2 / 2) + dn ^ 2 / 2 * db = dn * K := by
    rw [hK]; ring
  rw [eK] at Pa0 Pa1; rw [eK'] at Pb0 Pb1
  have q0 : |w₀| ≤ dn * K := by
    simp only [w₀, abs_neg, abs_div, abs_two]
    have := abs_add_le (⟪n₂ - n₁, lat2 ℓ₂ n₂ - lat2 ℓ₁ n₁⟫) (⟪n₁ - n₀, lat2 ℓ₁ n₁ - lat2 ℓ₀ n₀⟫)
    linarith
  have q1 : |w₁| ≤ dn * K := by
    simp only [w₁, abs_div, abs_two]
    have := abs_add_le (⟪n₂ - n₁, lat1 ℓ₂ n₂ - lat1 ℓ₁ n₁⟫) (⟪n₁ - n₀, lat1 ℓ₁ n₁ - lat1 ℓ₀ n₀⟫)
    linarith
  have hK0 : 0 ≤ K := by
    have : 0 ≤ tw := by unfold tw latTw; have := Real.sqrt_nonneg (1 - sb ^ 2); positivity
    positivity
  have hw : w₀ ^ 2 + w₁ ^ 2 ≤ (√2 * dn * K) ^ 2 := by
    have a0 : w₀ ^ 2 ≤ (dn * K) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) q0 2
    have a1 : w₁ ^ 2 ≤ (dn * K) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) q1 2
    have : (√2 * dn * K) ^ 2 = 2 * (dn * K) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
    rw [this]; linarith
  have key := sq2_add_le hxn0 (by positivity) P hw
  unfold latRpSharp
  convert key using 2

end Lateral

end VisionTracking

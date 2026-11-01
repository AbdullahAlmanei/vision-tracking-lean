import VisionTracking.FrameRate
import VisionTracking.RateBound

/-!
# Body rates of an explicit frame sequence, componentwise

For consecutive orthonormal frames `b = (b₁, b₂, b₃)` and `c = (c₁, c₂, c₃)` the lifted
body rate is `δ⁻¹ psiVec a`, where `a` is the antisymmetric part of `[⟪bᵢ, cⱼ⟫]`:

  `a = ½ (⟪b₃,c₂⟫ - ⟪b₂,c₃⟫, ⟪b₁,c₃⟫ - ⟪b₃,c₁⟫, ⟪b₂,c₁⟫ - ⟪b₁,c₂⟫)`.

Each component is an inner product of a frame *difference* with frame vectors, which
gives sharp bounds (`aVec_zero_eq`, …). `psiVec_sub_le` bounds the change of `psiVec`
by `G ‖Δa‖ + (G - 1) ρ` with `G = 1/√(1-ρ²)`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

/-- BAC-CAB. -/
theorem cross_cross_eq (a b c : E3) : cross (cross a b) c = ⟪a, c⟫ • b - ⟪b, c⟫ • a := by
  ext i; fin_cases i <;> simp [cross, crossProduct, inner_eq_coords] <;> ring

theorem cross_comm_neg (a b : E3) : cross b a = -cross a b := by
  ext i; fin_cases i <;> simp [cross, crossProduct] <;> ring

section Frame

variable {b₁ b₂ : E3} (h₁ : ‖b₁‖ = 1) (h₂ : ‖b₂‖ = 1) (h₁₂ : ⟪b₁, b₂⟫ = 0)
include h₁ h₂ h₁₂

omit h₂ in
theorem cross_b₃_b₁ : cross (cross b₁ b₂) b₁ = b₂ := by
  have e11 : ⟪b₁, b₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h₁]; norm_num
  have e21 : ⟪b₂, b₁⟫ = 0 := by rw [real_inner_comm]; exact h₁₂
  rw [cross_cross_eq, e11, e21, one_smul, zero_smul, sub_zero]

omit h₁ in
theorem cross_b₂_b₃ : cross b₂ (cross b₁ b₂) = b₁ := by
  have e22 : ⟪b₂, b₂⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h₂]; norm_num
  rw [cross_comm_neg, cross_cross_eq, e22, h₁₂, one_smul, zero_smul, zero_sub, neg_neg]

end Frame

/-- The body-frame rotation vector (before `psiVec`) between frames `b` and `c`. -/
noncomputable def aVec (b₁ b₂ c₁ c₂ : E3) : E3 :=
  sigmaVec (toF b₁ b₂ c₁) (toF b₁ b₂ c₂)

section Comps

variable {b₁ b₂ c₁ c₂ : E3} (h₁ : ‖b₁‖ = 1) (h₂ : ‖b₂‖ = 1) (h₁₂ : ⟪b₁, b₂⟫ = 0)
include h₁ h₂ h₁₂

theorem aVec_ofLp :
    (aVec b₁ b₂ c₁ c₂).ofLp 0 = (⟪cross b₁ b₂, c₂⟫ - ⟪b₂, cross c₁ c₂⟫) / 2 ∧
    (aVec b₁ b₂ c₁ c₂).ofLp 1 = (⟪b₁, cross c₁ c₂⟫ - ⟪cross b₁ b₂, c₁⟫) / 2 ∧
    (aVec b₁ b₂ c₁ c₂).ofLp 2 = (⟪b₂, c₁⟫ - ⟪b₁, c₂⟫) / 2 := by
  obtain ⟨s0, s1, s2⟩ := sigmaVec_ofLp (toF b₁ b₂ c₁) (toF b₁ b₂ c₂)
  obtain ⟨r0, r1, r2⟩ := toF_ofLp b₁ b₂ c₁
  obtain ⟨t0, t1, t2⟩ := toF_ofLp b₁ b₂ c₂
  have k2 : ⟪b₂, cross c₁ c₂⟫ = ⟪cross b₁ b₂, c₁⟫ * ⟪b₁, c₂⟫ - ⟪b₁, c₁⟫ * ⟪cross b₁ b₂, c₂⟫ := by
    have := inner_cross_cross (cross b₁ b₂) b₁ c₁ c₂
    rw [cross_b₃_b₁ h₁ h₁₂] at this; rw [this]; ring
  have k1 : ⟪b₁, cross c₁ c₂⟫ = ⟪b₂, c₁⟫ * ⟪cross b₁ b₂, c₂⟫ - ⟪cross b₁ b₂, c₁⟫ * ⟪b₂, c₂⟫ := by
    have := inner_cross_cross b₂ (cross b₁ b₂) c₁ c₂
    rw [cross_b₂_b₃ h₂ h₁₂] at this; rw [this]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [aVec, s0, r0, r2, t0, t2, k2]; ring
  · rw [aVec, s1, r1, r2, t1, t2, k1]; ring
  · rw [aVec, s2, r1, t0]; ring

/-- The components of `a` as inner products of frame differences, for a next frame `c`
that is orthonormal. -/
theorem aVec_ofLp_diff (hc : ⟪c₁, c₂⟫ = 0) :
    (aVec b₁ b₂ c₁ c₂).ofLp 0 = -(⟪cross c₁ c₂ - cross b₁ b₂, c₂⟫
        + ⟪cross c₁ c₂ - cross b₁ b₂, b₂⟫) / 2 ∧
    (aVec b₁ b₂ c₁ c₂).ofLp 1 = (⟪cross c₁ c₂ - cross b₁ b₂, b₁⟫
        + ⟪cross c₁ c₂ - cross b₁ b₂, c₁⟫) / 2 ∧
    (aVec b₁ b₂ c₁ c₂).ofLp 2 = -(⟪c₂ - b₂, c₁⟫ + ⟪c₂ - b₂, b₁⟫) / 2 := by
  obtain ⟨e0, e1, e2⟩ := aVec_ofLp (c₁ := c₁) (c₂ := c₂) h₁ h₂ h₁₂
  have o1 : ⟪cross c₁ c₂, c₂⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_right _ _
  have o2 : ⟪cross b₁ b₂, b₂⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_right _ _
  have o3 : ⟪cross c₁ c₂, c₁⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_left _ _
  have o4 : ⟪cross b₁ b₂, b₁⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_left _ _
  have o5 : ⟪c₂, c₁⟫ = 0 := by rw [real_inner_comm]; exact hc
  have o6 : ⟪b₂, b₁⟫ = 0 := by rw [real_inner_comm]; exact h₁₂
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, inner_sub_left, inner_sub_left, o1, o2, real_inner_comm b₂]; ring
  · rw [e1, inner_sub_left, inner_sub_left, o3, o4, real_inner_comm b₁ (cross c₁ c₂)]; ring
  · rw [e2, inner_sub_left, inner_sub_left, o5, o6, real_inner_comm c₂ b₁]; ring

end Comps

/-- The lifted body rate is `δ⁻¹ psiVec a`. -/
theorem KinPlan.rate_eq_aVec {Q : QuadParams} {C : CameraParams} {δ : ℝ} (p : KinPlan Q C δ)
    (k : ℕ) : p.rate k = δ⁻¹ • psiVec (aVec (p.b₁ k) (p.b₂ k) (p.b₁ (k + 1)) (p.b₂ (k + 1))) :=
  p.rate_eq k

/-! ## The step of `psiVec` -/

theorem psiVec_smul_eq (σ : E3) : psiVec σ = (Real.arcsin ‖σ‖ / ‖σ‖) • σ := rfl

/-- Bounds on the scalar `arcsin r / r` for `0 < r ≤ ρ < 1`. -/
theorem one_le_arcsin_div {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) : 1 ≤ Real.arcsin r / r := by
  rw [le_div_iff₀ h0, one_mul]
  have := Real.sin_arcsin (by linarith) h1
  have hs := Real.sin_le (Real.arcsin_nonneg.2 h0.le)
  linarith

/-- **Step of `psiVec`.** For `‖a‖, ‖a'‖ ≤ ρ < 1` and `G = 1/√(1-ρ²)`:
`‖psiVec a' - psiVec a‖ ≤ G ‖a' - a‖ + (G - 1) ρ`, and the same bound holds for each
coordinate with `|a'ᵢ - aᵢ|` in place of `‖a' - a‖`. -/
theorem psiVec_sub_le {a a' : E3} {ρ : ℝ} (ha : ‖a‖ ≤ ρ) (ha' : ‖a'‖ ≤ ρ) (hρ : ρ < 1) :
    ‖psiVec a' - psiVec a‖ ≤ ‖a' - a‖ / √(1 - ρ ^ 2) + (1 / √(1 - ρ ^ 2) - 1) * ρ ∧
    ∀ i, |(psiVec a').ofLp i - (psiVec a).ofLp i|
      ≤ |a'.ofLp i - a.ofLp i| / √(1 - ρ ^ 2) + (1 / √(1 - ρ ^ 2) - 1) * ρ := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg a).trans ha
  have hs : 0 < √(1 - ρ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hs1 : √(1 - ρ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith)
  set G := 1 / √(1 - ρ ^ 2) with hG
  have hG1 : 1 ≤ G := by rw [hG, le_div_iff₀ hs, one_mul]; exact hs1
  have hGρ : 0 ≤ (G - 1) * ρ := mul_nonneg (by linarith) hρ0
  have hdivG : ∀ x : ℝ, x / √(1 - ρ ^ 2) = G * x := fun x => by rw [hG]; ring
  set g := Real.arcsin ‖a‖ / ‖a‖ with hgdef
  set g' := Real.arcsin ‖a'‖ / ‖a'‖ with hg'def
  have hgG : 0 ≤ g ∧ g ≤ G := by
    have := arcsin_div_le (norm_nonneg a) ha hρ; rw [hG]; exact this
  have hgG' : 0 ≤ g' ∧ g' ≤ G := by
    have := arcsin_div_le (norm_nonneg a') ha' hρ; rw [hG]; exact this
  have hpa : psiVec a = g • a := rfl
  have hpa' : psiVec a' = g' • a' := rfl
  rw [hpa, hpa']
  simp only [hdivG]
  by_cases h0 : a = 0
  · subst h0
    simp only [smul_zero, sub_zero, norm_smul, Real.norm_of_nonneg hgG'.1, WithLp.ofLp_zero,
      Pi.zero_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg hgG'.1]
    refine ⟨by nlinarith [norm_nonneg a'], fun i => by nlinarith [abs_nonneg (a'.ofLp i)]⟩
  by_cases h0' : a' = 0
  · subst h0'
    simp only [smul_zero, zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg hgG.1,
      WithLp.ofLp_zero, Pi.zero_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, abs_neg,
      abs_mul, abs_of_nonneg hgG.1]
    refine ⟨by nlinarith [norm_nonneg a], fun i => by nlinarith [abs_nonneg (a.ofLp i)]⟩
  have hg1 : 1 ≤ g := one_le_arcsin_div (norm_pos_iff.2 h0) (ha.trans hρ.le)
  have hg1' : 1 ≤ g' := one_le_arcsin_div (norm_pos_iff.2 h0') (ha'.trans hρ.le)
  have hgd : |g' - g| ≤ G - 1 := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have split : g' • a' - g • a = g' • (a' - a) + (g' - g) • a := by module
  refine ⟨?_, fun i => ?_⟩
  · rw [split]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hgG'.1, Real.norm_eq_abs]
    have t1 := mul_le_mul_of_nonneg_right hgG'.2 (norm_nonneg (a' - a))
    have t2 := mul_le_mul hgd ha (norm_nonneg _) (by linarith)
    linarith
  · have hi : (g' • a' - g • a).ofLp i = g' * (a'.ofLp i - a.ofLp i) + (g' - g) * a.ofLp i := by
      simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hai : |a.ofLp i| ≤ ρ := by
      have : |a.ofLp i| ≤ ‖a‖ := by
        have := PiLp.norm_apply_le a i
        simpa using this
      exact this.trans ha
    simp only [WithLp.ofLp_sub, Pi.sub_apply] at hi ⊢
    rw [show (g' • a').ofLp i - (g • a).ofLp i = g' * (a'.ofLp i - a.ofLp i)
        + (g' - g) * a.ofLp i by
      simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]; ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hgG'.1]
    have t1 := mul_le_mul_of_nonneg_right hgG'.2 (abs_nonneg (a'.ofLp i - a.ofLp i))
    have t2 := mul_le_mul hgd hai (abs_nonneg _) (by linarith)
    linarith

end VisionTracking

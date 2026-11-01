import VisionTracking.TargetBounds
import VisionTracking.OverheadPlan

/-!
# Target bounds in terms of the current speed

Speed-dependent versions of the copying-thrust bounds, used by the version-3 budget.
Throughout, `a = δ⁻¹ (v_{k+1} - v_k)` and `T* = a + g e₃ + c ‖v‖ v`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {P : TargetParams} {δ : ℝ} (T : TargetTraj P δ) (Q : QuadParams) (hδ : 0 < δ)
include hδ

/-- The acceleration at the current speed: `‖a_k‖ ≤ aTan + ‖v_k‖²/R`. -/
theorem norm_targetAcc_le_loc (k : ℕ) :
    ‖δ⁻¹ • (T.v (k + 1) - T.v k)‖ ≤ P.aTan + ‖T.v k‖ ^ 2 / P.turnRadius := by
  have hsplit : T.v (k + 1) - T.v k = (⟪T.v (k + 1) - T.v k, T.v k⟫ / ‖T.v k‖ ^ 2) • T.v k
      + ((T.v (k + 1) - T.v k) - (⟪T.v (k + 1) - T.v k, T.v k⟫ / ‖T.v k‖ ^ 2) • T.v k) := by abel
  have h1 := norm_tan_part_le T k
  have h2 := T.normal k
  have hΔ : ‖T.v (k + 1) - T.v k‖ ≤ δ * (P.aTan + ‖T.v k‖ ^ 2 / P.turnRadius) := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [mul_add, ← mul_div_assoc]; linarith
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hδ.le, inv_mul_le_iff₀ hδ]
  exact hΔ

/-- One step changes the speed by at most `δ Amax`. -/
theorem abs_speed_step_le (k : ℕ) : |‖T.v (k + 1)‖ - ‖T.v k‖| ≤ δ * P.Amax := by
  refine (abs_norm_sub_norm_le _ _).trans ?_
  have := norm_targetAcc_le T hδ k
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hδ.le, inv_mul_le_iff₀ hδ] at this
  exact this

omit hδ in
/-- The horizontal speed is at least `‖v‖ cos γ`. -/
theorem norm_horiz_v_ge (k : ℕ) : ‖T.v k‖ * Real.cos P.climbMax ≤ ‖horiz (T.v k)‖ := by
  have hcl := T.climb_le k
  have hcos : 0 ≤ Real.cos P.climbMax :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [P.climbMax_nonneg, Real.pi_pos], P.climbMax_lt.le⟩
  have hsq := norm_horiz_sq (T.v k)
  rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), hsq, mul_pow, Real.cos_sq']
  have : ⟪T.v k, up⟫ ^ 2 ≤ (‖T.v k‖ * Real.sin P.climbMax) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hcl 2
  nlinarith

omit hδ in
theorem sin_climb_nonneg (P : TargetParams) : 0 ≤ Real.sin P.climbMax :=
  Real.sin_nonneg_of_nonneg_of_le_pi P.climbMax_nonneg
    (by linarith [P.climbMax_lt, Real.pi_pos])

/-- The vertical component of the copying thrust, at the current speed. -/
theorem thrustStar_up_loc (k : ℕ) :
    Q.g - P.aVert - Q.drag * ‖T.v k‖ ^ 2 * Real.sin P.climbMax ≤
      ⟪thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)), up⟫ ∧
    ⟪thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)), up⟫ ≤
      Q.g + P.aVert + Q.drag * ‖T.v k‖ ^ 2 * Real.sin P.climbMax := by
  have h1 := abs_le.1 (targetAcc_up_abs_le T hδ k)
  have hc := Q.drag_pos
  have hcl := abs_le.1 (T.climb_le k)
  have hn := norm_nonneg (T.v k)
  have huu : ⟪up, up⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_up']; norm_num
  have h2 := mul_le_mul_of_nonneg_left hcl.1 (mul_nonneg hc.le hn)
  have h3 := mul_le_mul_of_nonneg_left hcl.2 (mul_nonneg hc.le hn)
  unfold thrustStar
  rw [inner_add_left, inner_add_left, real_inner_smul_left up up Q.g,
    real_inner_smul_left (T.v k) up (Q.drag * ‖T.v k‖), huu]
  constructor <;> nlinarith

omit hδ in
/-- Norm and horizontal part of the copying thrust. -/
theorem thrustStar_norm_horiz_le (k : ℕ) :
    ‖thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k))‖
      ≤ Q.g + ‖δ⁻¹ • (T.v (k + 1) - T.v k)‖ + Q.drag * ‖T.v k‖ ^ 2 ∧
    ‖horiz (thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)))‖
      ≤ ‖δ⁻¹ • (T.v (k + 1) - T.v k)‖ + Q.drag * ‖T.v k‖ ^ 2 := by
  have hc := Q.drag_pos
  have hd : ‖(Q.drag * ‖T.v k‖) • T.v k‖ = Q.drag * ‖T.v k‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]; ring
  constructor
  · unfold thrustStar
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    have hg : ‖Q.g • up‖ = Q.g := by
      rw [norm_smul, norm_up', Real.norm_of_nonneg Q.g_pos.le, mul_one]
    rw [hg, hd]; linarith
  · unfold thrustStar
    rw [horiz_add, horiz_add, horiz_smul Q.g up, horiz_up, smul_zero, add_zero,
      horiz_smul (Q.drag * ‖T.v k‖) (T.v k)]
    refine (norm_add_le _ _).trans (add_le_add (norm_horiz_le _) ?_)
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have := norm_horiz_le (T.v k)
    calc Q.drag * ‖T.v k‖ * ‖horiz (T.v k)‖ ≤ Q.drag * ‖T.v k‖ * ‖T.v k‖ := by gcongr
      _ = Q.drag * ‖T.v k‖ ^ 2 := by ring

/-- Thrust along the target's velocity: `⟪T*, v⟫ ≥ ‖v‖ (c ‖v‖² - aTan - g sin γ)`. -/
theorem thrustStar_along_v_ge (k : ℕ) :
    ‖T.v k‖ * (Q.drag * ‖T.v k‖ ^ 2 - P.aTan - Q.g * Real.sin P.climbMax) ≤
      ⟪thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)), T.v k⟫ := by
  have hc := Q.drag_pos
  have hn := norm_nonneg (T.v k)
  have ht := abs_le.1 (T.tangential k)
  have hcl := abs_le.1 (T.climb_le k)
  have ha : -(P.aTan * ‖T.v k‖) ≤ ⟪δ⁻¹ • (T.v (k + 1) - T.v k), T.v k⟫ := by
    rw [real_inner_smul_left]
    have : -(δ * P.aTan * ‖T.v k‖) ≤ ⟪T.v (k + 1) - T.v k, T.v k⟫ := ht.1
    have hδi : 0 < δ⁻¹ := inv_pos.2 hδ
    have := mul_le_mul_of_nonneg_left this hδi.le
    rw [show δ⁻¹ * -(δ * P.aTan * ‖T.v k‖) = -(P.aTan * ‖T.v k‖) by field_simp] at this
    exact this
  have hup : ⟪up, T.v k⟫ ≥ -(‖T.v k‖ * Real.sin P.climbMax) := by
    rw [real_inner_comm]; linarith [hcl.1]
  have hvv : ⟪T.v k, T.v k⟫ = ‖T.v k‖ ^ 2 := real_inner_self_eq_norm_sq _
  unfold thrustStar
  simp only [inner_add_left, real_inner_smul_left (T.v k) (T.v k), hvv]
  rw [real_inner_smul_left up (T.v k)]
  have := mul_le_mul_of_nonneg_left hup.le Q.g_pos.le
  nlinarith

omit hδ in
/-- A unit vector orthogonal to the velocity sees only the turning acceleration. -/
theorem abs_inner_targetAcc_perp_le (k : ℕ) {u : E3} (hu : ‖u‖ = 1) (hperp : ⟪u, T.v k⟫ = 0)
    (hδ' : 0 < δ) :
    |⟪u, δ⁻¹ • (T.v (k + 1) - T.v k)⟫| ≤ ‖T.v k‖ ^ 2 / P.turnRadius := by
  have h2 := T.normal k
  have e : ⟪u, T.v (k + 1) - T.v k⟫ = ⟪u, (T.v (k + 1) - T.v k)
      - (⟪T.v (k + 1) - T.v k, T.v k⟫ / ‖T.v k‖ ^ 2) • T.v k⟫ := by
    have : ⟪u, (T.v (k + 1) - T.v k) - (⟪T.v (k + 1) - T.v k, T.v k⟫ / ‖T.v k‖ ^ 2) • T.v k⟫
        = ⟪u, T.v (k + 1) - T.v k⟫ := by
      rw [inner_sub_right (𝕜 := ℝ) u (T.v (k + 1) - T.v k), real_inner_smul_right, hperp,
        mul_zero, sub_zero]
    exact this.symm
  rw [real_inner_smul_right, abs_mul, abs_inv, abs_of_pos hδ', e, inv_mul_le_iff₀ hδ']
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [hu, one_mul]
  calc _ ≤ δ * ‖T.v k‖ ^ 2 / P.turnRadius := h2
    _ = δ * (‖T.v k‖ ^ 2 / P.turnRadius) := by ring

omit hδ in
/-- Thrust along the horizontal heading: `⟪T*, ĥ⟫ ≥ c ‖v‖² cos γ - ‖a‖`. -/
theorem thrustStar_along_heading_ge (k : ℕ) :
    Q.drag * ‖T.v k‖ ^ 2 * Real.cos P.climbMax - ‖δ⁻¹ • (T.v (k + 1) - T.v k)‖ ≤
      ⟪thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)), nrm (horiz (T.v k))⟫ := by
  have hc := Q.drag_pos
  have hge := norm_horiz_v_ge T k
  have hvpos : 0 < ‖T.v k‖ := P.vMin_pos.trans_le (T.speed_ge k)
  have hcos : 0 < Real.cos P.climbMax :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [P.climbMax_nonneg, Real.pi_pos], P.climbMax_lt⟩
  have hH : 0 < ‖horiz (T.v k)‖ := lt_of_lt_of_le (by positivity) hge
  set H := horiz (T.v k)
  have hu : ‖nrm H‖ = 1 := by unfold nrm; exact norm_smul_inv_norm (norm_pos_iff.1 hH)
  have e1 : ⟪up, nrm H⟫ = 0 := by
    rw [nrm, inner_smul_right, real_inner_comm, horiz_up_inner, mul_zero]
  have e2 : ⟪T.v k, nrm H⟫ = ‖H‖ := by
    have hv : T.v k = H + ⟪T.v k, up⟫ • up := by simp [H, horiz]
    have huH : ⟪up, H⟫ = 0 := by rw [real_inner_comm]; exact horiz_up_inner _
    have : ⟪T.v k, H⟫ = ‖H‖ ^ 2 := by
      conv_lhs => rw [hv]
      rw [inner_add_left, real_inner_smul_left, huH, mul_zero, add_zero,
        real_inner_self_eq_norm_sq]
    rw [nrm, inner_smul_right, this]; field_simp
  have ha := abs_real_inner_le_norm (δ⁻¹ • (T.v (k + 1) - T.v k)) (nrm H)
  rw [hu, mul_one] at ha
  unfold thrustStar
  rw [inner_add_left, inner_add_left, real_inner_smul_left up (nrm H) Q.g,
    real_inner_smul_left (T.v k) (nrm H) (Q.drag * ‖T.v k‖), e1, e2]
  have : Q.drag * ‖T.v k‖ ^ 2 * Real.cos P.climbMax ≤ Q.drag * ‖T.v k‖ * ‖H‖ := by
    have := mul_le_mul_of_nonneg_left hge (mul_nonneg hc.le hvpos.le)
    nlinarith
  linarith [(abs_le.1 ha).1]

end VisionTracking

import VisionTracking.Planner
import VisionTracking.Regularity

/-!
# The thrust a copying drone needs

To copy the target's motion the drone needs specific thrust
`T* = A + g e₃ + c_D ‖V‖ V` (target velocity `V`, acceleration `A`). Over all admissible
target states (speed band, along-track and turn-radius limits, climb angle `γ`):

* `‖A‖ ≤ Amax = a∥ + v_max² / R`;
* `‖T*‖ ≤ g + Amax + c_D v_max²`;
* `g - Amax - c_D v_max² sin γ ≤ ⟪T*, e₃⟫ ≤ g + Amax + c_D v_max² sin γ`;
* `Hstar ≤ ‖T*_h‖ ≤ Amax + c_D v_max²` with
  `Hstar = c_D v_min² cos γ - a∥ - (v_max² / R) sin γ`.
  Positive `Hstar` means the thrust is never vertical, so the downhill frame (and yaw)
  is always well defined.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {P : TargetParams} {δ : ℝ}

/-- Horizontal part. -/
noncomputable def horiz (x : E3) : E3 := x - ⟪x, up⟫ • up

noncomputable def TargetParams.Amax (P : TargetParams) : ℝ := P.aTan + P.vMax ^ 2 / P.turnRadius

noncomputable def thrustStar (Q : QuadParams) (V A : E3) : E3 := A + Q.g • up + (Q.drag * ‖V‖) • V

noncomputable def Hstar (P : TargetParams) (Q : QuadParams) : ℝ :=
  Q.drag * P.vMin ^ 2 * Real.cos P.climbMax - P.aTan - P.vMax ^ 2 / P.turnRadius * Real.sin P.climbMax

theorem horiz_up_inner (x : E3) : ⟪horiz x, up⟫ = 0 := by
  have huu : ⟪up, up⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_up']; norm_num
  rw [horiz, inner_sub_left, real_inner_smul_left, huu, mul_one, sub_self]

theorem norm_horiz_sq (x : E3) : ‖horiz x‖ ^ 2 = ‖x‖ ^ 2 - ⟪x, up⟫ ^ 2 := by
  have huu : ⟪up, up⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_up']; norm_num
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, horiz]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, huu]
  rw [real_inner_comm up x]; ring

theorem norm_horiz_le (x : E3) : ‖horiz x‖ ≤ ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_horiz_sq]; nlinarith [sq_nonneg ⟪x, up⟫]

theorem horiz_add (x y : E3) : horiz (x + y) = horiz x + horiz y := by
  simp only [horiz, inner_add_left, add_smul]; abel

theorem horiz_smul (r : ℝ) (x : E3) : horiz (r • x) = r • horiz x := by
  simp only [horiz, real_inner_smul_left, smul_sub, smul_smul]

theorem horiz_up : horiz up = 0 := by
  have huu : ⟪up, up⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_up']; norm_num
  rw [horiz, huu, one_smul, sub_self]

variable (T : TargetTraj P δ) (Q : QuadParams) (hδ : 0 < δ)
include hδ

omit hδ in
theorem speed_pos (k : ℕ) : 0 < ‖T.v k‖ := P.vMin_pos.trans_le (T.speed_ge k)

omit hδ in
theorem norm_tan_part_le (k : ℕ) :
    ‖(⟪T.v (k + 1) - T.v k, T.v k⟫ / ‖T.v k‖ ^ 2) • T.v k‖ ≤ δ * P.aTan := by
  have hn := speed_pos T k
  rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < ‖T.v k‖ ^ 2)]
  have := T.tangential k
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc |⟪T.v (k + 1) - T.v k, T.v k⟫| * ‖T.v k‖ ≤ δ * P.aTan * ‖T.v k‖ * ‖T.v k‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = δ * P.aTan * ‖T.v k‖ ^ 2 := by ring

theorem norm_targetAcc_le (k : ℕ) : ‖δ⁻¹ • (T.v (k + 1) - T.v k)‖ ≤ P.Amax := by
  have hsplit : T.v (k + 1) - T.v k = (⟪T.v (k + 1) - T.v k, T.v k⟫ / ‖T.v k‖ ^ 2) • T.v k
      + ((T.v (k + 1) - T.v k) - (⟪T.v (k + 1) - T.v k, T.v k⟫ / ‖T.v k‖ ^ 2) • T.v k) := by abel
  have h1 := norm_tan_part_le T k
  have h2 := T.normal k
  have hv := T.speed_le k
  have hR := P.turnRadius_pos
  have hΔ : ‖T.v (k + 1) - T.v k‖ ≤ δ * P.Amax := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have : δ * ‖T.v k‖ ^ 2 / P.turnRadius ≤ δ * (P.vMax ^ 2 / P.turnRadius) := by
      rw [mul_div_assoc]
      gcongr
    unfold TargetParams.Amax; linarith
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hδ.le, inv_mul_le_iff₀ hδ]
  exact hΔ

theorem thrustStar_norm_le (k : ℕ) :
    ‖thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k))‖ ≤ Q.g + P.Amax + Q.drag * P.vMax ^ 2 := by
  have hA := norm_targetAcc_le T hδ k
  have hv := T.speed_le k
  have hc := Q.drag_pos
  unfold thrustStar
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  have hg : ‖Q.g • up‖ = Q.g := by rw [norm_smul, norm_up', Real.norm_of_nonneg Q.g_pos.le, mul_one]
  have hd : ‖(Q.drag * ‖T.v k‖) • T.v k‖ = Q.drag * (‖T.v k‖ * ‖T.v k‖) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]; ring
  have h1 : ‖T.v k‖ * ‖T.v k‖ ≤ P.vMax ^ 2 := by nlinarith [norm_nonneg (T.v k)]
  have := mul_le_mul_of_nonneg_left h1 hc.le
  linarith

theorem thrustStar_up_ge (k : ℕ) :
    Q.g - P.Amax - Q.drag * P.vMax ^ 2 * Real.sin P.climbMax ≤
      ⟪thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)), up⟫ := by
  have hA := norm_targetAcc_le T hδ k
  have hv := T.speed_le k
  have hc := Q.drag_pos
  have hcl := T.climb_le k
  have hsin : 0 ≤ Real.sin P.climbMax :=
    Real.sin_nonneg_of_nonneg_of_le_pi P.climbMax_nonneg (by linarith [P.climbMax_lt, Real.pi_pos])
  have huu : ⟪up, up⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_up']; norm_num
  have h1 : -P.Amax ≤ ⟪δ⁻¹ • (T.v (k + 1) - T.v k), up⟫ := by
    have := abs_real_inner_le_norm (δ⁻¹ • (T.v (k + 1) - T.v k)) up
    rw [norm_up', mul_one, abs_le] at this; linarith
  have h2 : -(Q.drag * P.vMax ^ 2 * Real.sin P.climbMax) ≤ Q.drag * ‖T.v k‖ * ⟪T.v k, up⟫ := by
    rw [abs_le] at hcl
    have hn := norm_nonneg (T.v k)
    have : ‖T.v k‖ * ‖T.v k‖ * Real.sin P.climbMax ≤ P.vMax ^ 2 * Real.sin P.climbMax := by
      apply mul_le_mul_of_nonneg_right _ hsin; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hcl.1 (mul_nonneg hc.le hn)]
  unfold thrustStar
  rw [inner_add_left, inner_add_left, real_inner_smul_left up up Q.g,
    real_inner_smul_left (T.v k) up (Q.drag * ‖T.v k‖), huu]
  linarith

theorem thrustStar_up_le (k : ℕ) :
    ⟪thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)), up⟫ ≤
      Q.g + P.Amax + Q.drag * P.vMax ^ 2 * Real.sin P.climbMax := by
  have hA := norm_targetAcc_le T hδ k
  have hv := T.speed_le k
  have hc := Q.drag_pos
  have hcl := T.climb_le k
  have hsin : 0 ≤ Real.sin P.climbMax :=
    Real.sin_nonneg_of_nonneg_of_le_pi P.climbMax_nonneg (by linarith [P.climbMax_lt, Real.pi_pos])
  have huu : ⟪up, up⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_up']; norm_num
  have h1 : ⟪δ⁻¹ • (T.v (k + 1) - T.v k), up⟫ ≤ P.Amax := by
    have := abs_real_inner_le_norm (δ⁻¹ • (T.v (k + 1) - T.v k)) up
    rw [norm_up', mul_one, abs_le] at this; linarith
  have h2 : Q.drag * ‖T.v k‖ * ⟪T.v k, up⟫ ≤ Q.drag * P.vMax ^ 2 * Real.sin P.climbMax := by
    rw [abs_le] at hcl
    have hn := norm_nonneg (T.v k)
    have : ‖T.v k‖ * ‖T.v k‖ * Real.sin P.climbMax ≤ P.vMax ^ 2 * Real.sin P.climbMax := by
      apply mul_le_mul_of_nonneg_right _ hsin; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hcl.2 (mul_nonneg hc.le hn)]
  unfold thrustStar
  rw [inner_add_left, inner_add_left, real_inner_smul_left up up Q.g,
    real_inner_smul_left (T.v k) up (Q.drag * ‖T.v k‖), huu]
  linarith

theorem thrustStar_horiz_le (k : ℕ) :
    ‖horiz (thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)))‖ ≤ P.Amax + Q.drag * P.vMax ^ 2 := by
  have hA := norm_targetAcc_le T hδ k
  have hv := T.speed_le k
  have hc := Q.drag_pos
  unfold thrustStar
  rw [horiz_add, horiz_add, horiz_smul Q.g up, horiz_up, smul_zero, add_zero,
    horiz_smul (Q.drag * ‖T.v k‖) (T.v k)]
  refine (norm_add_le _ _).trans ?_
  have e1 := norm_horiz_le (δ⁻¹ • (T.v (k + 1) - T.v k))
  have e2 : ‖(Q.drag * ‖T.v k‖) • horiz (T.v k)‖ ≤ Q.drag * P.vMax ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have := norm_horiz_le (T.v k)
    have hn := norm_nonneg (T.v k)
    have h1 : ‖T.v k‖ * ‖T.v k‖ ≤ P.vMax ^ 2 := by nlinarith
    calc Q.drag * ‖T.v k‖ * ‖horiz (T.v k)‖ ≤ Q.drag * ‖T.v k‖ * ‖T.v k‖ := by gcongr
      _ = Q.drag * (‖T.v k‖ * ‖T.v k‖) := by ring
      _ ≤ Q.drag * P.vMax ^ 2 := mul_le_mul_of_nonneg_left h1 hc.le
  linarith

theorem thrustStar_horiz_ge (k : ℕ) :
    Hstar P Q ≤ ‖horiz (thrustStar Q (T.v k) (δ⁻¹ • (T.v (k + 1) - T.v k)))‖ := by
  set V := T.v k with hV
  set Δ := T.v (k + 1) - T.v k with hΔ
  have hn := speed_pos T k
  rw [← hV] at hn
  have hc := Q.drag_pos
  have hγ0 := P.climbMax_nonneg
  have hγ1 := P.climbMax_lt
  have hcos : 0 ≤ Real.cos P.climbMax := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hγ1.le⟩
  have hsin : 0 ≤ Real.sin P.climbMax :=
    Real.sin_nonneg_of_nonneg_of_le_pi hγ0 (by linarith [Real.pi_pos])
  have hcl : |⟪V, up⟫| ≤ ‖V‖ * Real.sin P.climbMax := T.climb_le k
  -- The horizontal speed is at least `‖V‖ cos γ`.
  set nh := ‖horiz V‖ with hnh
  have hnh2 : nh ^ 2 = ‖V‖ ^ 2 - ⟪V, up⟫ ^ 2 := norm_horiz_sq V
  have hnhge : ‖V‖ * Real.cos P.climbMax ≤ nh := by
    rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), hnh2, mul_pow]
    have h2 : ⟪V, up⟫ ^ 2 ≤ (‖V‖ * Real.sin P.climbMax) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hcl 2
    have := Real.sin_sq_add_cos_sq P.climbMax
    nlinarith
  have hnhle : nh ≤ ‖V‖ := norm_horiz_le V
  have hnhpos : 0 < nh := by
    have : 0 < Real.cos P.climbMax := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hγ1⟩
    nlinarith
  set ĥ := nh⁻¹ • horiz V with hĥ
  have hĥn : ‖ĥ‖ = 1 := by
    rw [hĥ, norm_smul, norm_inv, norm_norm, ← hnh, inv_mul_cancel₀ hnhpos.ne']
  have hĥup : ⟪ĥ, up⟫ = 0 := by rw [hĥ, real_inner_smul_left, horiz_up_inner, mul_zero]
  have hVĥ : ⟪V, ĥ⟫ = nh := by
    have : ⟪V, horiz V⟫ = nh ^ 2 := by
      rw [hnh2, horiz, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
    rw [hĥ, real_inner_smul_right, this]; field_simp
  -- `‖horiz X‖ ≥ ⟪X, ĥ⟫`.
  have hproj : ∀ X : E3, ⟪X, ĥ⟫ ≤ ‖horiz X‖ := by
    intro X
    have h1 : ⟪horiz X, ĥ⟫ = ⟪X, ĥ⟫ := by
      rw [horiz, inner_sub_left, real_inner_smul_left, real_inner_comm ĥ up, hĥup, mul_zero,
        sub_zero]
    have := real_inner_le_norm (horiz X) ĥ
    rw [hĥn, mul_one, h1] at this; exact this
  refine le_trans ?_ (hproj _)
  -- Decompose the velocity change.
  set s := ⟪Δ, V⟫ / ‖V‖ ^ 2 with hs
  set N := Δ - s • V with hN
  have hNV : ⟪N, V⟫ = 0 := by
    rw [hN, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hs]; field_simp; ring
  have hNb : ‖N‖ ≤ δ * (‖V‖ ^ 2 / P.turnRadius) := by
    have := T.normal k; rw [mul_div_assoc] at this; exact this
  have hsb : |s| * nh ≤ δ * P.aTan := by
    have h1 := norm_tan_part_le T k
    rw [norm_smul, Real.norm_eq_abs] at h1
    calc |s| * nh ≤ |s| * ‖V‖ := by gcongr
      _ ≤ δ * P.aTan := h1
  -- The normal part is almost orthogonal to `ĥ`.
  have hĥV : ⟪ĥ, V⟫ = nh := by rw [real_inner_comm]; exact hVĥ
  have hnorm2 : ‖ĥ - (nh / ‖V‖ ^ 2) • V‖ ^ 2 = 1 - nh ^ 2 / ‖V‖ ^ 2 := by
    rw [norm_sub_sq_real, hĥn, real_inner_smul_right, hĥV, norm_smul,
      Real.norm_of_nonneg (by positivity)]
    field_simp; ring
  have hsinb : ‖ĥ - (nh / ‖V‖ ^ 2) • V‖ ≤ Real.sin P.climbMax := by
    rw [← sq_le_sq₀ (norm_nonneg _) hsin, hnorm2]
    have : ‖V‖ ^ 2 * Real.cos P.climbMax ^ 2 ≤ nh ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hnhge 2
    rw [Real.sin_sq, sub_le_sub_iff_left, le_div_iff₀ (by positivity)]
    linarith
  have hNĥ : -(δ * (P.vMax ^ 2 / P.turnRadius) * Real.sin P.climbMax) ≤ ⟪N, ĥ⟫ := by
    have e : ⟪N, ĥ⟫ = ⟪N, ĥ - (nh / ‖V‖ ^ 2) • V⟫ := by
      rw [inner_sub_right, real_inner_smul_right N V, hNV, mul_zero, sub_zero]
    rw [e]
    have := abs_real_inner_le_norm N (ĥ - (nh / ‖V‖ ^ 2) • V)
    rw [abs_le] at this
    have hv := T.speed_le k
    have hR := P.turnRadius_pos
    have h3 : ‖N‖ ≤ δ * (P.vMax ^ 2 / P.turnRadius) := by
      refine hNb.trans ?_
      gcongr
    have := mul_le_mul h3 hsinb (norm_nonneg _) (by positivity)
    linarith
  have hAĥ : -P.aTan - P.vMax ^ 2 / P.turnRadius * Real.sin P.climbMax ≤ ⟪δ⁻¹ • Δ, ĥ⟫ := by
    have hΔsplit : Δ = s • V + N := by rw [hN]; abel
    rw [real_inner_smul_left, hΔsplit, inner_add_left, real_inner_smul_left, hVĥ]
    have hs1 : -(δ * P.aTan) ≤ s * nh := by
      have := neg_abs_le s; nlinarith [abs_nonneg s]
    rw [le_inv_mul_iff₀ hδ]
    nlinarith
  unfold thrustStar Hstar
  rw [inner_add_left, inner_add_left, real_inner_smul_left up ĥ Q.g,
    real_inner_smul_left V ĥ (Q.drag * ‖V‖), real_inner_comm ĥ up, hĥup, mul_zero, add_zero, hVĥ]
  have hvmin := T.speed_ge k
  have e1 : P.vMin ^ 2 * Real.cos P.climbMax ≤ ‖V‖ ^ 2 * Real.cos P.climbMax :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ P.vMin_pos.le hvmin 2) hcos
  have e2 : ‖V‖ ^ 2 * Real.cos P.climbMax = ‖V‖ * (‖V‖ * Real.cos P.climbMax) := by ring
  have e3 : ‖V‖ * (‖V‖ * Real.cos P.climbMax) ≤ ‖V‖ * nh := mul_le_mul_of_nonneg_left hnhge hn.le
  have key : P.vMin ^ 2 * Real.cos P.climbMax ≤ ‖V‖ * nh := by rw [e2] at e1; exact e1.trans e3
  have key2 := mul_le_mul_of_nonneg_left key hc.le
  have r1 : Q.drag * P.vMin ^ 2 * Real.cos P.climbMax = Q.drag * (P.vMin ^ 2 * Real.cos P.climbMax) := by
    ring
  have r2 : Q.drag * ‖V‖ * nh = Q.drag * (‖V‖ * nh) := by ring
  linarith

end VisionTracking

import VisionTracking.Frame

/-!
# Rodrigues rotation is a proper rotation

`rotate ω` turns vectors by the angle `‖ω‖` about the axis `ω`. Its unit-axis form
`rodr c s k v = c v + s (k × v) + (1 - c) ⟪k, v⟫ k`, with `c² + s² = 1` and
`‖k‖ = 1`, preserves inner products and cross products (`inner_rotate`,
`rotate_cross`). So the attitude update of `QuadTraj` keeps the body frame a
right-handed orthonormal frame. And it turns a vector by at most `‖ω‖`
(`angle_rotate_le`), so body-rate limits bound tilt and heading rates.

The polynomial identities behind the first two are discharged with
`linear_combination`, using certificates computed by Gröbner-basis reduction modulo
`c² + s² = 1` and `‖k‖² = 1`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

/-- Rodrigues' formula with explicit cosine `c`, sine `s` and axis `k`. -/
noncomputable def rodr (cc ss : ℝ) (k v : E3) : E3 :=
  cc • v + ss • cross k v + ((1 - cc) * ⟪k, v⟫) • k

theorem rotate_eq_rodr (ω v : E3) :
    rotate ω v = rodr (Real.cos ‖ω‖) (Real.sin ‖ω‖) (‖ω‖⁻¹ • ω) v := rfl

theorem rotate_zero (v : E3) : rotate 0 v = v := by
  simp [rotate]

theorem rodr_apply (cc ss : ℝ) (k v : E3) (i : Fin 3) :
    (rodr cc ss k v).ofLp i = cc * v.ofLp i + ss * (cross k v).ofLp i
      + (1 - cc) * ⟪k, v⟫ * k.ofLp i := by
  simp [rodr]

theorem cross_ofLp_zero (a b : E3) :
    (cross a b).ofLp 0 = a.ofLp 1 * b.ofLp 2 - a.ofLp 2 * b.ofLp 1 := (cross_apply a b).1
theorem cross_ofLp_one (a b : E3) :
    (cross a b).ofLp 1 = a.ofLp 2 * b.ofLp 0 - a.ofLp 0 * b.ofLp 2 := (cross_apply a b).2.1
theorem cross_ofLp_two (a b : E3) :
    (cross a b).ofLp 2 = a.ofLp 0 * b.ofLp 1 - a.ofLp 1 * b.ofLp 0 := (cross_apply a b).2.2

theorem norm_sq_coords (k : E3) : ‖k‖ ^ 2 = (k.ofLp 0) ^ 2 + (k.ofLp 1) ^ 2 + (k.ofLp 2) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_coords]; ring

theorem inner_rodr {cc ss : ℝ} {k : E3} (hsc : ss ^ 2 + cc ^ 2 = 1) (hk1 : ‖k‖ = 1)
    (a b : E3) : ⟪rodr cc ss k a, rodr cc ss k b⟫ = ⟪a, b⟫ := by
  have hk : (k.ofLp 0) ^ 2 + (k.ofLp 1) ^ 2 + (k.ofLp 2) ^ 2 = 1 := by
    rw [← norm_sq_coords, hk1]; norm_num
  rw [inner_eq_coords (rodr cc ss k a), inner_eq_coords a b]
  simp only [rodr_apply, inner_eq_coords k a, inner_eq_coords k b, cross_ofLp_zero,
    cross_ofLp_one, cross_ofLp_two]
  linear_combination ((a.ofLp 0)*(b.ofLp 0)*(k.ofLp 0)^4 + (a.ofLp 0)*(b.ofLp 0)*(k.ofLp 0)^2*(k.ofLp 1)^2 + (a.ofLp 0)*(b.ofLp 0)*(k.ofLp 0)^2*(k.ofLp 2)^2 - 2*(a.ofLp 0)*(b.ofLp 0)*(k.ofLp 0)^2 + (a.ofLp 0)*(b.ofLp 0) + (a.ofLp 0)*(b.ofLp 1)*(k.ofLp 0)^3*(k.ofLp 1) + (a.ofLp 0)*(b.ofLp 1)*(k.ofLp 0)*(k.ofLp 1)^3 + (a.ofLp 0)*(b.ofLp 1)*(k.ofLp 0)*(k.ofLp 1)*(k.ofLp 2)^2 - 2*(a.ofLp 0)*(b.ofLp 1)*(k.ofLp 0)*(k.ofLp 1) + (a.ofLp 0)*(b.ofLp 2)*(k.ofLp 0)^3*(k.ofLp 2) + (a.ofLp 0)*(b.ofLp 2)*(k.ofLp 0)*(k.ofLp 1)^2*(k.ofLp 2) + (a.ofLp 0)*(b.ofLp 2)*(k.ofLp 0)*(k.ofLp 2)^3 - 2*(a.ofLp 0)*(b.ofLp 2)*(k.ofLp 0)*(k.ofLp 2) + (a.ofLp 1)*(b.ofLp 0)*(k.ofLp 0)^3*(k.ofLp 1) + (a.ofLp 1)*(b.ofLp 0)*(k.ofLp 0)*(k.ofLp 1)^3 + (a.ofLp 1)*(b.ofLp 0)*(k.ofLp 0)*(k.ofLp 1)*(k.ofLp 2)^2 - 2*(a.ofLp 1)*(b.ofLp 0)*(k.ofLp 0)*(k.ofLp 1) + (a.ofLp 1)*(b.ofLp 1)*(k.ofLp 0)^2*(k.ofLp 1)^2 + (a.ofLp 1)*(b.ofLp 1)*(k.ofLp 1)^4 + (a.ofLp 1)*(b.ofLp 1)*(k.ofLp 1)^2*(k.ofLp 2)^2 - 2*(a.ofLp 1)*(b.ofLp 1)*(k.ofLp 1)^2 + (a.ofLp 1)*(b.ofLp 1) + (a.ofLp 1)*(b.ofLp 2)*(k.ofLp 0)^2*(k.ofLp 1)*(k.ofLp 2) + (a.ofLp 1)*(b.ofLp 2)*(k.ofLp 1)^3*(k.ofLp 2) + (a.ofLp 1)*(b.ofLp 2)*(k.ofLp 1)*(k.ofLp 2)^3 - 2*(a.ofLp 1)*(b.ofLp 2)*(k.ofLp 1)*(k.ofLp 2) + (a.ofLp 2)*(b.ofLp 0)*(k.ofLp 0)^3*(k.ofLp 2) + (a.ofLp 2)*(b.ofLp 0)*(k.ofLp 0)*(k.ofLp 1)^2*(k.ofLp 2) + (a.ofLp 2)*(b.ofLp 0)*(k.ofLp 0)*(k.ofLp 2)^3 - 2*(a.ofLp 2)*(b.ofLp 0)*(k.ofLp 0)*(k.ofLp 2) + (a.ofLp 2)*(b.ofLp 1)*(k.ofLp 0)^2*(k.ofLp 1)*(k.ofLp 2) + (a.ofLp 2)*(b.ofLp 1)*(k.ofLp 1)^3*(k.ofLp 2) + (a.ofLp 2)*(b.ofLp 1)*(k.ofLp 1)*(k.ofLp 2)^3 - 2*(a.ofLp 2)*(b.ofLp 1)*(k.ofLp 1)*(k.ofLp 2) + (a.ofLp 2)*(b.ofLp 2)*(k.ofLp 0)^2*(k.ofLp 2)^2 + (a.ofLp 2)*(b.ofLp 2)*(k.ofLp 1)^2*(k.ofLp 2)^2 + (a.ofLp 2)*(b.ofLp 2)*(k.ofLp 2)^4 - 2*(a.ofLp 2)*(b.ofLp 2)*(k.ofLp 2)^2 + (a.ofLp 2)*(b.ofLp 2)) * hsc + (-2*(a.ofLp 0)*(b.ofLp 0)*cc*(k.ofLp 0)^2 - (a.ofLp 0)*(b.ofLp 0)*(k.ofLp 0)^2*ss^2 + 2*(a.ofLp 0)*(b.ofLp 0)*(k.ofLp 0)^2 + (a.ofLp 0)*(b.ofLp 0)*ss^2 - 2*(a.ofLp 0)*(b.ofLp 1)*cc*(k.ofLp 0)*(k.ofLp 1) - (a.ofLp 0)*(b.ofLp 1)*(k.ofLp 0)*(k.ofLp 1)*ss^2 + 2*(a.ofLp 0)*(b.ofLp 1)*(k.ofLp 0)*(k.ofLp 1) - 2*(a.ofLp 0)*(b.ofLp 2)*cc*(k.ofLp 0)*(k.ofLp 2) - (a.ofLp 0)*(b.ofLp 2)*(k.ofLp 0)*(k.ofLp 2)*ss^2 + 2*(a.ofLp 0)*(b.ofLp 2)*(k.ofLp 0)*(k.ofLp 2) - 2*(a.ofLp 1)*(b.ofLp 0)*cc*(k.ofLp 0)*(k.ofLp 1) - (a.ofLp 1)*(b.ofLp 0)*(k.ofLp 0)*(k.ofLp 1)*ss^2 + 2*(a.ofLp 1)*(b.ofLp 0)*(k.ofLp 0)*(k.ofLp 1) - 2*(a.ofLp 1)*(b.ofLp 1)*cc*(k.ofLp 1)^2 - (a.ofLp 1)*(b.ofLp 1)*(k.ofLp 1)^2*ss^2 + 2*(a.ofLp 1)*(b.ofLp 1)*(k.ofLp 1)^2 + (a.ofLp 1)*(b.ofLp 1)*ss^2 - 2*(a.ofLp 1)*(b.ofLp 2)*cc*(k.ofLp 1)*(k.ofLp 2) - (a.ofLp 1)*(b.ofLp 2)*(k.ofLp 1)*(k.ofLp 2)*ss^2 + 2*(a.ofLp 1)*(b.ofLp 2)*(k.ofLp 1)*(k.ofLp 2) - 2*(a.ofLp 2)*(b.ofLp 0)*cc*(k.ofLp 0)*(k.ofLp 2) - (a.ofLp 2)*(b.ofLp 0)*(k.ofLp 0)*(k.ofLp 2)*ss^2 + 2*(a.ofLp 2)*(b.ofLp 0)*(k.ofLp 0)*(k.ofLp 2) - 2*(a.ofLp 2)*(b.ofLp 1)*cc*(k.ofLp 1)*(k.ofLp 2) - (a.ofLp 2)*(b.ofLp 1)*(k.ofLp 1)*(k.ofLp 2)*ss^2 + 2*(a.ofLp 2)*(b.ofLp 1)*(k.ofLp 1)*(k.ofLp 2) - 2*(a.ofLp 2)*(b.ofLp 2)*cc*(k.ofLp 2)^2 - (a.ofLp 2)*(b.ofLp 2)*(k.ofLp 2)^2*ss^2 + 2*(a.ofLp 2)*(b.ofLp 2)*(k.ofLp 2)^2 + (a.ofLp 2)*(b.ofLp 2)*ss^2) * hk

theorem rodr_cross {cc ss : ℝ} {k : E3} (hsc : ss ^ 2 + cc ^ 2 = 1) (hk1 : ‖k‖ = 1)
    (a b : E3) : rodr cc ss k (cross a b) = cross (rodr cc ss k a) (rodr cc ss k b) := by
  have hk : (k.ofLp 0) ^ 2 + (k.ofLp 1) ^ 2 + (k.ofLp 2) ^ 2 = 1 := by
    rw [← norm_sq_coords, hk1]; norm_num
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, rodr_apply, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two,
      inner_eq_coords]
    linear_combination (-(a.ofLp 0)*(b.ofLp 1)*(k.ofLp 0)*(k.ofLp 2) + (a.ofLp 0)*(b.ofLp 2)*(k.ofLp 0)*(k.ofLp 1) + (a.ofLp 1)*(b.ofLp 0)*(k.ofLp 0)*(k.ofLp 2) + (a.ofLp 1)*(b.ofLp 2)*(k.ofLp 1)^2 + (a.ofLp 1)*(b.ofLp 2)*(k.ofLp 2)^2 - (a.ofLp 1)*(b.ofLp 2) - (a.ofLp 2)*(b.ofLp 0)*(k.ofLp 0)*(k.ofLp 1) - (a.ofLp 2)*(b.ofLp 1)*(k.ofLp 1)^2 - (a.ofLp 2)*(b.ofLp 1)*(k.ofLp 2)^2 + (a.ofLp 2)*(b.ofLp 1)) * hsc + ((a.ofLp 0)*(b.ofLp 1)*cc*(k.ofLp 1)*ss - (a.ofLp 0)*(b.ofLp 1)*(k.ofLp 1)*ss + (a.ofLp 0)*(b.ofLp 2)*cc*(k.ofLp 2)*ss - (a.ofLp 0)*(b.ofLp 2)*(k.ofLp 2)*ss - (a.ofLp 1)*(b.ofLp 0)*cc*(k.ofLp 1)*ss + (a.ofLp 1)*(b.ofLp 0)*(k.ofLp 1)*ss - (a.ofLp 1)*(b.ofLp 2)*cc - (a.ofLp 1)*(b.ofLp 2)*ss^2 + (a.ofLp 1)*(b.ofLp 2) - (a.ofLp 2)*(b.ofLp 0)*cc*(k.ofLp 2)*ss + (a.ofLp 2)*(b.ofLp 0)*(k.ofLp 2)*ss + (a.ofLp 2)*(b.ofLp 1)*cc + (a.ofLp 2)*(b.ofLp 1)*ss^2 - (a.ofLp 2)*(b.ofLp 1)) * hk
  · simp only [Fin.mk_one, rodr_apply, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two,
      inner_eq_coords]
    linear_combination (-(a.ofLp 0)*(b.ofLp 1)*(k.ofLp 1)*(k.ofLp 2) - (a.ofLp 0)*(b.ofLp 2)*(k.ofLp 0)^2 - (a.ofLp 0)*(b.ofLp 2)*(k.ofLp 2)^2 + (a.ofLp 0)*(b.ofLp 2) + (a.ofLp 1)*(b.ofLp 0)*(k.ofLp 1)*(k.ofLp 2) - (a.ofLp 1)*(b.ofLp 2)*(k.ofLp 0)*(k.ofLp 1) + (a.ofLp 2)*(b.ofLp 0)*(k.ofLp 0)^2 + (a.ofLp 2)*(b.ofLp 0)*(k.ofLp 2)^2 - (a.ofLp 2)*(b.ofLp 0) + (a.ofLp 2)*(b.ofLp 1)*(k.ofLp 0)*(k.ofLp 1)) * hsc + (-(a.ofLp 0)*(b.ofLp 1)*cc*(k.ofLp 0)*ss + (a.ofLp 0)*(b.ofLp 1)*(k.ofLp 0)*ss + (a.ofLp 0)*(b.ofLp 2)*cc + (a.ofLp 0)*(b.ofLp 2)*ss^2 - (a.ofLp 0)*(b.ofLp 2) + (a.ofLp 1)*(b.ofLp 0)*cc*(k.ofLp 0)*ss - (a.ofLp 1)*(b.ofLp 0)*(k.ofLp 0)*ss + (a.ofLp 1)*(b.ofLp 2)*cc*(k.ofLp 2)*ss - (a.ofLp 1)*(b.ofLp 2)*(k.ofLp 2)*ss - (a.ofLp 2)*(b.ofLp 0)*cc - (a.ofLp 2)*(b.ofLp 0)*ss^2 + (a.ofLp 2)*(b.ofLp 0) - (a.ofLp 2)*(b.ofLp 1)*cc*(k.ofLp 2)*ss + (a.ofLp 2)*(b.ofLp 1)*(k.ofLp 2)*ss) * hk
  · simp only [Fin.reduceFinMk, rodr_apply, cross_ofLp_zero, cross_ofLp_one, cross_ofLp_two,
      inner_eq_coords]
    linear_combination ((a.ofLp 0)*(b.ofLp 1)*(k.ofLp 0)^2 + (a.ofLp 0)*(b.ofLp 1)*(k.ofLp 1)^2 - (a.ofLp 0)*(b.ofLp 1) + (a.ofLp 0)*(b.ofLp 2)*(k.ofLp 1)*(k.ofLp 2) - (a.ofLp 1)*(b.ofLp 0)*(k.ofLp 0)^2 - (a.ofLp 1)*(b.ofLp 0)*(k.ofLp 1)^2 + (a.ofLp 1)*(b.ofLp 0) - (a.ofLp 1)*(b.ofLp 2)*(k.ofLp 0)*(k.ofLp 2) - (a.ofLp 2)*(b.ofLp 0)*(k.ofLp 1)*(k.ofLp 2) + (a.ofLp 2)*(b.ofLp 1)*(k.ofLp 0)*(k.ofLp 2)) * hsc + (-(a.ofLp 0)*(b.ofLp 1)*cc - (a.ofLp 0)*(b.ofLp 1)*ss^2 + (a.ofLp 0)*(b.ofLp 1) - (a.ofLp 0)*(b.ofLp 2)*cc*(k.ofLp 0)*ss + (a.ofLp 0)*(b.ofLp 2)*(k.ofLp 0)*ss + (a.ofLp 1)*(b.ofLp 0)*cc + (a.ofLp 1)*(b.ofLp 0)*ss^2 - (a.ofLp 1)*(b.ofLp 0) - (a.ofLp 1)*(b.ofLp 2)*cc*(k.ofLp 1)*ss + (a.ofLp 1)*(b.ofLp 2)*(k.ofLp 1)*ss + (a.ofLp 2)*(b.ofLp 0)*cc*(k.ofLp 0)*ss - (a.ofLp 2)*(b.ofLp 0)*(k.ofLp 0)*ss + (a.ofLp 2)*(b.ofLp 1)*cc*(k.ofLp 1)*ss - (a.ofLp 2)*(b.ofLp 1)*(k.ofLp 1)*ss) * hk

/-- Rodrigues rotation preserves inner products. -/
theorem inner_rotate (ω a b : E3) : ⟪rotate ω a, rotate ω b⟫ = ⟪a, b⟫ := by
  by_cases h0 : ω = 0
  · simp [h0, rotate_zero]
  · rw [rotate_eq_rodr, rotate_eq_rodr]
    exact inner_rodr (by rw [Real.sin_sq_add_cos_sq]) (norm_smul_inv_norm h0) a b

theorem norm_rotate (ω a : E3) : ‖rotate ω a‖ = ‖a‖ := by
  have h := inner_rotate ω a a
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- Rodrigues rotation preserves cross products (it is a proper rotation). -/
theorem rotate_cross (ω a b : E3) :
    rotate ω (cross a b) = cross (rotate ω a) (rotate ω b) := by
  by_cases h0 : ω = 0
  · simp [h0, rotate_zero]
  · rw [rotate_eq_rodr, rotate_eq_rodr, rotate_eq_rodr]
    exact rodr_cross (by rw [Real.sin_sq_add_cos_sq]) (norm_smul_inv_norm h0) a b

/-- A rotation by `ω` with `‖ω‖ ≤ π` turns any nonzero vector by at most `‖ω‖`. -/
theorem angle_rotate_le (ω v : E3) (hv : v ≠ 0) (hω : ‖ω‖ ≤ π) :
    angle (rotate ω v) v ≤ ‖ω‖ := by
  by_cases h0 : ω = 0
  · simp [h0, rotate_zero, angle_self hv]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hin : Real.cos ‖ω‖ * ‖v‖ ^ 2 ≤ ⟪rotate ω v, v⟫ := by
    rw [rotate_eq_rodr, rodr, inner_add_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hz : ⟪cross (‖ω‖⁻¹ • ω) v, v⟫ = 0 := by
      rw [real_inner_comm]; exact inner_cross_right _ _
    rw [hz, mul_zero, add_zero]
    have h1 : 0 ≤ 1 - Real.cos ‖ω‖ := by linarith [Real.cos_le_one ‖ω‖]
    have h2 : 0 ≤ (1 - Real.cos ‖ω‖) * ⟪‖ω‖⁻¹ • ω, v⟫ * ⟪‖ω‖⁻¹ • ω, v⟫ := by
      rw [mul_assoc]; exact mul_nonneg h1 (mul_self_nonneg _)
    linarith
  unfold angle
  rw [norm_rotate]
  calc Real.arccos (⟪rotate ω v, v⟫ / (‖v‖ * ‖v‖))
      ≤ Real.arccos (Real.cos ‖ω‖) := by
        apply Real.arccos_le_arccos
        rw [le_div_iff₀ (by positivity)]; nlinarith
    _ = ‖ω‖ := Real.arccos_cos (norm_nonneg _) hω

end VisionTracking

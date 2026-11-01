import VisionTracking.PlanLemmas
import VisionTracking.SharpNorm

/-!
# Geometry of a clamped hinge pointing straight up

For a body frame whose thrust axis is tilted by less than a right angle, let
`u = (⟪b₁,e₃⟫, ⟪b₂,e₃⟫, ⟪b₃,e₃⟫)` and `φ = arctan (u₁/u₃)` the in-plane pitch. A hinge angle
`η` gives `⟪cos η b₁ + sin η b₃, e₃⟫ = ρ cos (π/2 - η - φ)` with `ρ = √(u₁² + u₃²)`. The
clamp to the hinge range is 1-Lipschitz, and the in-plane pitch moves by at most
`π/2 · ‖Δ(u₃,u₁)‖ / ρ_min`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

/-- Clamping is 1-Lipschitz. -/
theorem clamp_lip (l u x y : ℝ) : |max l (min u x) - max l (min u y)| ≤ |x - y| := by
  rw [max_comm l, max_comm l]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

/-- The distance from a point to its clamp. -/
theorem clamp_dist {l u a b x : ℝ} (hlu : l ≤ u) (ha : a ≤ x) (hb : x ≤ b) :
    |x - max l (min u x)| ≤ max 0 (max (b - u) (l - a)) := by
  rcases le_total x u with h1 | h1 <;> rcases le_total l x with h2 | h2
  · rw [min_eq_right h1, max_eq_right h2, sub_self, abs_zero]; exact le_max_left _ _
  · rw [min_eq_right h1, max_eq_left h2, abs_of_nonpos (by linarith)]
    exact le_trans (by linarith) ((le_max_right _ _).trans (le_max_right _ _))
  · rw [min_eq_left h1, max_eq_right hlu, abs_of_nonneg (by linarith)]
    exact le_trans (by linarith) ((le_max_left _ _).trans (le_max_right _ _))
  · rw [min_eq_left h1, max_eq_right hlu, abs_of_nonneg (by linarith)]
    exact le_trans (by linarith) ((le_max_left _ _).trans (le_max_right _ _))

theorem cos_arctan_div {x y : ℝ} (hx : 0 < x) :
    Real.cos (Real.arctan (y / x)) = x / √(x ^ 2 + y ^ 2) ∧
      Real.sin (Real.arctan (y / x)) = y / √(x ^ 2 + y ^ 2) := by
  have hr : √(1 + (y / x) ^ 2) = √(x ^ 2 + y ^ 2) / x := by
    rw [show 1 + (y / x) ^ 2 = (x ^ 2 + y ^ 2) / x ^ 2 by field_simp, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq hx.le]
  have hpos : 0 < √(x ^ 2 + y ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [Real.cos_arctan, Real.sin_arctan, hr]
  constructor <;> field_simp

/-- **Camera elevation on an in-plane hinge**. -/
theorem inner_cam_up_eq {u₁ u₃ η : ℝ} (h3 : 0 < u₃) :
    Real.cos η * u₁ + Real.sin η * u₃
      = √(u₃ ^ 2 + u₁ ^ 2) * Real.cos (π / 2 - η - Real.arctan (u₁ / u₃)) := by
  obtain ⟨hc, hs⟩ := cos_arctan_div (y := u₁) h3
  have hpos : 0 < √(u₃ ^ 2 + u₁ ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [show π / 2 - η - Real.arctan (u₁ / u₃) = π / 2 - (η + Real.arctan (u₁ / u₃)) by ring,
    Real.cos_pi_div_two_sub, Real.sin_add, hc, hs]
  field_simp
  ring

/-- **Step of the in-plane pitch.** -/
theorem abs_arctan_sub_le {x y x' y' m : ℝ} (hx : 0 < x) (hx' : 0 < x') (hm : 0 < m)
    (hr : m ≤ √(x ^ 2 + y ^ 2)) (hr' : m ≤ √(x' ^ 2 + y' ^ 2)) :
    |Real.arctan (y' / x') - Real.arctan (y / x)| ≤ π / 2 * ((|x' - x| + |y' - y|) / m) := by
  set P : E3 := !₂[x, y, 0]
  set P' : E3 := !₂[x', y', 0]
  have nP : ‖P‖ = √(x ^ 2 + y ^ 2) := by
    rw [EuclideanSpace.norm_eq]; congr 1; simp [P, Fin.sum_univ_three]
  have nP' : ‖P'‖ = √(x' ^ 2 + y' ^ 2) := by
    rw [EuclideanSpace.norm_eq]; congr 1; simp [P', Fin.sum_univ_three]
  have hpos : 0 < ‖P‖ := hm.trans_le (nP ▸ hr)
  have hpos' : 0 < ‖P'‖ := hm.trans_le (nP' ▸ hr')
  set φ := Real.arctan (y / x)
  set φ' := Real.arctan (y' / x')
  obtain ⟨c, s⟩ := cos_arctan_div (y := y) hx
  obtain ⟨c', s'⟩ := cos_arctan_div (y := y') hx'
  -- the angle between P and P' is |φ' - φ|
  have hang : angle P P' = |φ' - φ| := by
    have hin : ⟪P, P'⟫ / (‖P‖ * ‖P'‖) = Real.cos (φ' - φ) := by
      rw [Real.cos_sub, c, s, c', s', nP, nP']
      simp only [P, P', inner_eq_coords]
      simp
      field_simp
    have hb : |φ' - φ| ≤ π := by
      have := Real.arctan_lt_pi_div_two (y / x); have := Real.neg_pi_div_two_lt_arctan (y / x)
      have := Real.arctan_lt_pi_div_two (y' / x'); have := Real.neg_pi_div_two_lt_arctan (y' / x')
      rw [abs_le]; constructor <;> linarith
    rw [angle, hin, arccos_cos_eq_abs hb]
  rw [← hang]
  have h1 : angle P P' = angle (nrm P) (nrm P') := by
    rw [nrm, nrm, angle_smul_left_of_pos _ _ (inv_pos.2 hpos),
      angle_smul_right_of_pos _ _ (inv_pos.2 hpos')]
  rw [h1]
  have u1 : ‖nrm P‖ = 1 := by unfold nrm; exact norm_smul_inv_norm (norm_pos_iff.1 hpos)
  have u2 : ‖nrm P'‖ = 1 := by unfold nrm; exact norm_smul_inv_norm (norm_pos_iff.1 hpos')
  refine (angle_le_chord u1 u2).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [norm_sub_rev]
  refine (norm_nrm_sub_le_sharp hm (nP' ▸ hr') (nP ▸ hr)).trans ?_
  apply div_le_div_of_nonneg_right _ hm.le
  have : ‖P' - P‖ ^ 2 = (x' - x) ^ 2 + (y' - y) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]; simp only [P, P', inner_eq_coords]; simp; ring
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), this]
  nlinarith [abs_nonneg (x' - x), abs_nonneg (y' - y), sq_abs (x' - x), sq_abs (y' - y)]

end VisionTracking

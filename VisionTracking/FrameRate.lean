import VisionTracking.Lifting
import VisionTracking.RateBound

/-!
# Body rates and their changes from frame differences

For a kinematic plan whose frame vectors move by at most `D₁` per step (first
differences) with second differences at most `D₂`, and `2 D₁ < 1`:

* `KinPlan.norm_rate_le`: `‖Ω_k‖ ≤ 2 D₁ / (δ √(1 - 4 D₁²))`;
* `KinPlan.norm_rate_sub_le`: `‖Ω_{k+1} - Ω_k‖ ≤ 18 (D₂ + D₁²) / (δ √(1 - 4 D₁²))`;
* `frameTrace_ge_of_step`: the plan's `near` condition holds.

The torque budget is `J ‖Ω_{k+1} - Ω_k‖ / δ + ‖Ω_k‖ ‖J Ω_k‖`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {Q : QuadParams} {C : CameraParams} {δ : ℝ}

theorem inner_unit_eq {b b' : E3} (hb : ‖b‖ = 1) (hb' : ‖b'‖ = 1) :
    ⟪b, b'⟫ = 1 - ‖b - b'‖ ^ 2 / 2 := by
  rw [norm_sub_sq_real, hb, hb']; ring

theorem frameTrace_ge_of_step {a₁ a₂ c₁ c₂ : E3} (ha₁ : ‖a₁‖ = 1) (ha₂ : ‖a₂‖ = 1)
    (ha : ⟪a₁, a₂⟫ = 0) (hc₁ : ‖c₁‖ = 1) (hc₂ : ‖c₂‖ = 1) (hc : ⟪c₁, c₂⟫ = 0) {D : ℝ}
    (h₁ : ‖a₁ - c₁‖ ≤ D) (h₂ : ‖a₂ - c₂‖ ≤ D) (h₃ : ‖cross a₁ a₂ - cross c₁ c₂‖ ≤ D) :
    3 - 3 * D ^ 2 / 2 ≤ frameTrace a₁ a₂ c₁ c₂ := by
  unfold frameTrace
  rw [inner_unit_eq ha₁ hc₁, inner_unit_eq ha₂ hc₂,
    inner_unit_eq (norm_cross_of_orthonormal ha₁ ha₂ ha) (norm_cross_of_orthonormal hc₁ hc₂ hc)]
  have := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  have := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
  have := pow_le_pow_left₀ (norm_nonneg _) h₃ 2
  linarith

theorem norm_le_abs_coords (v : E3) : ‖v‖ ≤ |v.ofLp 0| + |v.ofLp 1| + |v.ofLp 2| := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), norm_sq_coords]
  nlinarith [abs_nonneg (v.ofLp 0), abs_nonneg (v.ofLp 1), abs_nonneg (v.ofLp 2), sq_abs (v.ofLp 0),
    sq_abs (v.ofLp 1), sq_abs (v.ofLp 2), mul_nonneg (abs_nonneg (v.ofLp 0)) (abs_nonneg (v.ofLp 1)),
    mul_nonneg (abs_nonneg (v.ofLp 0)) (abs_nonneg (v.ofLp 2)),
    mul_nonneg (abs_nonneg (v.ofLp 1)) (abs_nonneg (v.ofLp 2))]

/-- The step identity behind the second-order bound. -/
theorem inner_step_le {x x' y y' y'' : E3} (hx' : ‖x'‖ = 1) (hg : ⟪x', y'⟫ = ⟪x, y⟫) :
    |⟪x', y''⟫ - ⟪x, y'⟫| ≤ ‖y'' - 2 • y' + y‖ + ‖x' - x‖ * ‖y' - y‖ := by
  have hid : ⟪x', y''⟫ - ⟪x, y'⟫ = ⟪x', y'' - 2 • y' + y⟫ + ⟪x' - x, y' - y⟫ := by
    simp only [two_smul, inner_add_right, inner_sub_right, inner_sub_left]
    linarith
  rw [hid]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · have := abs_real_inner_le_norm x' (y'' - 2 • y' + y); rwa [hx', one_mul] at this
  · exact abs_real_inner_le_norm _ _

theorem toF_sub (a₁ a₂ u v : E3) : toF a₁ a₂ (u - v) = toF a₁ a₂ u - toF a₁ a₂ v := by
  ext j; fin_cases j <;> simp [toF, inner_sub_right]

namespace KinPlan

variable (p : KinPlan Q C δ)

noncomputable def rr (k : ℕ) : E3 := toF (p.b₁ k) (p.b₂ k) (p.b₁ (k + 1))
noncomputable def ss (k : ℕ) : E3 := toF (p.b₁ k) (p.b₂ k) (p.b₂ (k + 1))

theorem rr_unit (k : ℕ) : ‖p.rr k‖ = 1 := by
  rw [rr, norm_toF (p.b₁_unit k) (p.b₂_unit k) (p.b₁₂_orth k), p.b₁_unit]
theorem ss_unit (k : ℕ) : ‖p.ss k‖ = 1 := by
  rw [ss, norm_toF (p.b₁_unit k) (p.b₂_unit k) (p.b₁₂_orth k), p.b₂_unit]

theorem toF_self_one (k : ℕ) : toF (p.b₁ k) (p.b₂ k) (p.b₁ k) = ex := by
  have e21 : ⟪p.b₂ k, p.b₁ k⟫ = 0 := by rw [real_inner_comm]; exact p.b₁₂_orth k
  have e31 : ⟪cross (p.b₁ k) (p.b₂ k), p.b₁ k⟫ = 0 := by
    rw [real_inner_comm]; exact inner_cross_left _ _
  ext j; fin_cases j <;> simp [toF, ex, e21, e31, p.b₁_unit k]
theorem toF_self_two (k : ℕ) : toF (p.b₁ k) (p.b₂ k) (p.b₂ k) = ey := by
  have e12 := p.b₁₂_orth k
  have e32 : ⟪cross (p.b₁ k) (p.b₂ k), p.b₂ k⟫ = 0 := by
    rw [real_inner_comm]; exact inner_cross_right _ _
  ext j; fin_cases j <;> simp [toF, ey, e12, e32, p.b₂_unit k]

variable {D₁ D₂ : ℝ}
  (hstep : ∀ k, ‖p.b₁ (k + 1) - p.b₁ k‖ ≤ D₁ ∧ ‖p.b₂ (k + 1) - p.b₂ k‖ ≤ D₁ ∧
    ‖p.b₃ (k + 1) - p.b₃ k‖ ≤ D₁)
  (hsec : ∀ k, ‖p.b₁ (k + 2) - 2 • p.b₁ (k + 1) + p.b₁ k‖ ≤ D₂ ∧
    ‖p.b₂ (k + 2) - 2 • p.b₂ (k + 1) + p.b₂ k‖ ≤ D₂)
include hstep

theorem norm_sigma_le (k : ℕ) : ‖sigmaVec (p.rr k) (p.ss k)‖ ≤ 2 * D₁ := by
  have h0 : sigmaVec ex ey = 0 := by ext j; fin_cases j <;> simp [sigmaVec, ex, ey]
  have hex : ‖ex‖ = 1 := by simp [ex]
  have := norm_sigmaVec_sub_le (r := p.rr k) (s := p.ss k) (r' := ex) (s' := ey)
    (p.ss_unit k) hex
  rw [h0, sub_zero] at this
  have hr : ‖p.rr k - ex‖ ≤ D₁ := by
    rw [rr, ← p.toF_self_one k, ← toF_sub, norm_toF (p.b₁_unit k) (p.b₂_unit k) (p.b₁₂_orth k)]
    exact (hstep k).1
  have hs : ‖p.ss k - ey‖ ≤ D₁ := by
    rw [ss, ← p.toF_self_two k, ← toF_sub, norm_toF (p.b₁_unit k) (p.b₂_unit k) (p.b₁₂_orth k)]
    exact (hstep k).2.1
  linarith

theorem norm_rate_le (hδ : 0 < δ) (hD : 2 * D₁ < 1) (k : ℕ) :
    ‖p.rate k‖ ≤ 2 * D₁ / (δ * √(1 - (2 * D₁) ^ 2)) := by
  have hσ := p.norm_sigma_le hstep k
  have h0 : 0 ≤ 2 * D₁ := (norm_nonneg _).trans hσ
  have hs1 : 0 < √(1 - (2 * D₁) ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  rw [p.rate_eq k, norm_smul, norm_inv, Real.norm_of_nonneg hδ.le]
  have := norm_psiVec_le hσ hD
  rw [← rr, ← ss]
  calc δ⁻¹ * ‖psiVec (sigmaVec (p.rr k) (p.ss k))‖
      ≤ δ⁻¹ * (2 * D₁ / √(1 - (2 * D₁) ^ 2)) := by
        gcongr
        exact this.trans (div_le_div_of_nonneg_right hσ hs1.le)
    _ = 2 * D₁ / (δ * √(1 - (2 * D₁) ^ 2)) := by field_simp

include hsec

theorem norm_rr_sub_le (k : ℕ) : ‖p.rr (k + 1) - p.rr k‖ ≤ 3 * (D₂ + D₁ ^ 2) := by
  refine (norm_le_abs_coords _).trans ?_
  obtain ⟨a0, a1, a2⟩ := toF_ofLp (p.b₁ (k + 1)) (p.b₂ (k + 1)) (p.b₁ (k + 1 + 1))
  obtain ⟨c0, c1, c2⟩ := toF_ofLp (p.b₁ k) (p.b₂ k) (p.b₁ (k + 1))
  have g : ∀ {x x' : E3}, ‖x'‖ = 1 → ⟪x', p.b₁ (k + 1)⟫ = ⟪x, p.b₁ k⟫ → ‖x' - x‖ ≤ D₁ →
      |⟪x', p.b₁ (k + 1 + 1)⟫ - ⟪x, p.b₁ (k + 1)⟫| ≤ D₂ + D₁ ^ 2 := by
    intro x x' hx' hg hd
    refine (inner_step_le hx' hg).trans ?_
    have : ‖p.b₁ (k + 1 + 1) - 2 • p.b₁ (k + 1) + p.b₁ k‖ ≤ D₂ := (hsec k).1
    have := mul_le_mul hd (hstep k).1 (norm_nonneg _) ((norm_nonneg _).trans hd)
    nlinarith
  simp only [rr, WithLp.ofLp_sub, Pi.sub_apply, a0, a1, a2, c0, c1, c2]
  have e11 : ∀ j, ⟪p.b₁ j, p.b₁ j⟫ = 1 := fun j => by
    rw [real_inner_self_eq_norm_sq, p.b₁_unit]; norm_num
  have e21 : ∀ j, ⟪p.b₂ j, p.b₁ j⟫ = 0 := fun j => by rw [real_inner_comm]; exact p.b₁₂_orth j
  have e31 : ∀ j, ⟪cross (p.b₁ j) (p.b₂ j), p.b₁ j⟫ = 0 := fun j => by
    rw [real_inner_comm]; exact inner_cross_left _ _
  have u3 : ∀ j, ‖cross (p.b₁ j) (p.b₂ j)‖ = 1 := fun j =>
    norm_cross_of_orthonormal (p.b₁_unit j) (p.b₂_unit j) (p.b₁₂_orth j)
  have t0 := g (p.b₁_unit (k + 1)) (by rw [e11, e11]) (hstep k).1
  have t1 := g (p.b₂_unit (k + 1)) (by rw [e21, e21]) (hstep k).2.1
  have t2 := g (x := cross (p.b₁ k) (p.b₂ k)) (x' := cross (p.b₁ (k + 1)) (p.b₂ (k + 1)))
    (u3 (k + 1)) (by rw [e31, e31]) (hstep k).2.2
  linarith

theorem norm_ss_sub_le (k : ℕ) : ‖p.ss (k + 1) - p.ss k‖ ≤ 3 * (D₂ + D₁ ^ 2) := by
  refine (norm_le_abs_coords _).trans ?_
  obtain ⟨a0, a1, a2⟩ := toF_ofLp (p.b₁ (k + 1)) (p.b₂ (k + 1)) (p.b₂ (k + 1 + 1))
  obtain ⟨c0, c1, c2⟩ := toF_ofLp (p.b₁ k) (p.b₂ k) (p.b₂ (k + 1))
  have g : ∀ {x x' : E3}, ‖x'‖ = 1 → ⟪x', p.b₂ (k + 1)⟫ = ⟪x, p.b₂ k⟫ → ‖x' - x‖ ≤ D₁ →
      |⟪x', p.b₂ (k + 1 + 1)⟫ - ⟪x, p.b₂ (k + 1)⟫| ≤ D₂ + D₁ ^ 2 := by
    intro x x' hx' hg hd
    refine (inner_step_le hx' hg).trans ?_
    have : ‖p.b₂ (k + 1 + 1) - 2 • p.b₂ (k + 1) + p.b₂ k‖ ≤ D₂ := (hsec k).2
    have := mul_le_mul hd (hstep k).2.1 (norm_nonneg _) ((norm_nonneg _).trans hd)
    nlinarith
  simp only [ss, WithLp.ofLp_sub, Pi.sub_apply, a0, a1, a2, c0, c1, c2]
  have e12 : ∀ j, ⟪p.b₁ j, p.b₂ j⟫ = 0 := fun j => p.b₁₂_orth j
  have e22 : ∀ j, ⟪p.b₂ j, p.b₂ j⟫ = 1 := fun j => by
    rw [real_inner_self_eq_norm_sq, p.b₂_unit]; norm_num
  have e32 : ∀ j, ⟪cross (p.b₁ j) (p.b₂ j), p.b₂ j⟫ = 0 := fun j => by
    rw [real_inner_comm]; exact inner_cross_right _ _
  have u3 : ∀ j, ‖cross (p.b₁ j) (p.b₂ j)‖ = 1 := fun j =>
    norm_cross_of_orthonormal (p.b₁_unit j) (p.b₂_unit j) (p.b₁₂_orth j)
  have t0 := g (p.b₁_unit (k + 1)) (by rw [e12, e12]) (hstep k).1
  have t1 := g (p.b₂_unit (k + 1)) (by rw [e22, e22]) (hstep k).2.1
  have t2 := g (x := cross (p.b₁ k) (p.b₂ k)) (x' := cross (p.b₁ (k + 1)) (p.b₂ (k + 1)))
    (u3 (k + 1)) (by rw [e32, e32]) (hstep k).2.2
  linarith

theorem norm_rate_sub_le (hδ : 0 < δ) (hD : 2 * D₁ < 1) (k : ℕ) :
    ‖p.rate (k + 1) - p.rate k‖ ≤ 18 * (D₂ + D₁ ^ 2) / (δ * √(1 - (2 * D₁) ^ 2)) := by
  have h0 : 0 ≤ 2 * D₁ := (norm_nonneg _).trans (p.norm_sigma_le hstep k)
  have hs1 : 0 < √(1 - (2 * D₁) ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  rw [p.rate_eq, p.rate_eq, ← smul_sub, norm_smul, norm_inv, Real.norm_of_nonneg hδ.le]
  rw [← rr, ← ss, ← rr, ← ss]
  have hψ := norm_psiVec_sub_le (p.norm_sigma_le hstep (k + 1)) (p.norm_sigma_le hstep k) hD
  have hσ := norm_sigmaVec_sub_le (r := p.rr (k + 1)) (s := p.ss (k + 1)) (r' := p.rr k)
    (s' := p.ss k) (p.ss_unit _) (p.rr_unit _)
  have h1 := p.norm_rr_sub_le hstep hsec k
  have h2 := p.norm_ss_sub_le hstep hsec k
  have hb : ‖psiVec (sigmaVec (p.rr (k + 1)) (p.ss (k + 1))) - psiVec (sigmaVec (p.rr k) (p.ss k))‖
      ≤ 18 * (D₂ + D₁ ^ 2) / √(1 - (2 * D₁) ^ 2) := by
    refine hψ.trans ?_
    rw [div_le_div_iff_of_pos_right hs1]
    linarith
  calc δ⁻¹ * ‖psiVec (sigmaVec (p.rr (k + 1)) (p.ss (k + 1))) - psiVec (sigmaVec (p.rr k) (p.ss k))‖
      ≤ δ⁻¹ * (18 * (D₂ + D₁ ^ 2) / √(1 - (2 * D₁) ^ 2)) := by gcongr
    _ = 18 * (D₂ + D₁ ^ 2) / (δ * √(1 - (2 * D₁) ^ 2)) := by field_simp

end KinPlan

end VisionTracking

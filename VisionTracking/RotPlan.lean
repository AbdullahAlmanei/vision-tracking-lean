import VisionTracking.Transport
import VisionTracking.Lifting
import VisionTracking.FrameRate

/-!
# Plans whose frames evolve by chosen rotations

A `RotPlan` prescribes, besides positions and the hinge, a world-frame rotation vector
`ω k` per step, and the body frame evolves by `b (k+1) = rotate (ω k) (b k)`. The body
rates are then simply `ω k` in body coordinates divided by `δ`. No axis-angle
recovery is needed, and the rate bounds are direct:
`‖Ω_k‖ = ‖ω_k‖/δ` and `‖Ω_{k+1} - Ω_k‖ ≤ (‖ω_{k+1} - ω_k‖ + 3 ‖ω_k‖ ‖ω_{k+1}‖)/δ`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {Q : QuadParams} {C : CameraParams} {δ : ℝ}

structure RotPlan (Q : QuadParams) (C : CameraParams) (δ : ℝ) where
  x : ℕ → E3
  v : ℕ → E3
  b₁ : ℕ → E3
  b₂ : ℕ → E3
  η : ℕ → ℝ
  ω : ℕ → E3
  steps : StepsWith δ x v
  b₁_unit : ∀ k, ‖b₁ k‖ = 1
  b₂_unit : ∀ k, ‖b₂ k‖ = 1
  b₁₂_orth : ∀ k, ⟪b₁ k, b₂ k⟫ = 0
  evolve : ∀ k, b₁ (k + 1) = rotate (ω k) (b₁ k) ∧ b₂ (k + 1) = rotate (ω k) (b₂ k)

namespace RotPlan

variable (p : RotPlan Q C δ)

noncomputable def b₃ (k : ℕ) : E3 := cross (p.b₁ k) (p.b₂ k)
noncomputable def rate (k : ℕ) : E3 := δ⁻¹ • toF (p.b₁ k) (p.b₂ k) (p.ω k)
noncomputable def thrust (k : ℕ) : E3 :=
  δ⁻¹ • (p.v (k + 1) - p.v k) + Q.g • up + (Q.drag * ‖p.v k‖) • p.v k
noncomputable def torque (k : ℕ) : E3 :=
  Q.inertia (δ⁻¹ • (p.rate (k + 1) - p.rate k)) + cross (p.rate k) (Q.inertia (p.rate k))

theorem b₃_evolve (k : ℕ) : p.b₃ (k + 1) = rotate (p.ω k) (p.b₃ k) := by
  rw [b₃, b₃, (p.evolve k).1, (p.evolve k).2, rotate_cross]

theorem norm_rate (hδ : 0 < δ) (k : ℕ) : ‖p.rate k‖ = ‖p.ω k‖ / δ := by
  rw [rate, norm_smul, norm_inv, Real.norm_of_nonneg hδ.le,
    norm_toF (p.b₁_unit k) (p.b₂_unit k) (p.b₁₂_orth k), inv_mul_eq_div]

theorem norm_rate_sub_le (hδ : 0 < δ) (k : ℕ) :
    ‖p.rate (k + 1) - p.rate k‖
      ≤ (‖p.ω (k + 1) - p.ω k‖ + 3 * (‖p.ω k‖ * ‖p.ω (k + 1)‖)) / δ := by
  set A := toF (p.b₁ (k + 1)) (p.b₂ (k + 1)) (p.ω (k + 1)) - toF (p.b₁ k) (p.b₂ k) (p.ω (k + 1))
    with hA
  have e1 : p.rate (k + 1) - p.rate k
      = δ⁻¹ • (A + toF (p.b₁ k) (p.b₂ k) (p.ω (k + 1) - p.ω k)) := by
    rw [rate, rate, hA, toF_sub]; module
  have hcoord : ∀ {x x' : E3}, ‖x‖ = 1 → x' = rotate (p.ω k) x →
      |⟪x', p.ω (k + 1)⟫ - ⟪x, p.ω (k + 1)⟫| ≤ ‖p.ω k‖ * ‖p.ω (k + 1)‖ := by
    intro x x' hx hx'
    rw [← inner_sub_left]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hx']
    have := norm_rotate_sub_le (p.ω k) x
    rw [hx, mul_one] at this
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hAn : ‖A‖ ≤ 3 * (‖p.ω k‖ * ‖p.ω (k + 1)‖) := by
    refine (norm_le_abs_coords A).trans ?_
    obtain ⟨a0, a1, a2⟩ := toF_ofLp (p.b₁ (k + 1)) (p.b₂ (k + 1)) (p.ω (k + 1))
    obtain ⟨c0, c1, c2⟩ := toF_ofLp (p.b₁ k) (p.b₂ k) (p.ω (k + 1))
    simp only [hA, WithLp.ofLp_sub, Pi.sub_apply, a0, a1, a2, c0, c1, c2]
    have t0 := hcoord (p.b₁_unit k) (p.evolve k).1
    have t1 := hcoord (p.b₂_unit k) (p.evolve k).2
    have t2 := hcoord (norm_cross_of_orthonormal (p.b₁_unit k) (p.b₂_unit k) (p.b₁₂_orth k))
      (p.b₃_evolve k)
    simp only [b₃] at t2
    linarith
  rw [e1, norm_smul, norm_inv, Real.norm_of_nonneg hδ.le, inv_mul_eq_div]
  apply div_le_div_of_nonneg_right _ hδ.le
  refine (norm_add_le _ _).trans ?_
  rw [norm_toF (p.b₁_unit k) (p.b₂_unit k) (p.b₁₂_orth k)]
  linarith

theorem rate_yaw (k : ℕ) : (p.rate k).ofLp 2 = δ⁻¹ * ⟪p.b₃ k, p.ω k⟫ := by
  simp [rate, toF, b₃]

end RotPlan

/-- **Lifting for rotation plans.** -/
noncomputable def QuadTraj.ofRotPlan (hkn : Q.normalDrag = 0) (p : RotPlan Q C δ) (hδ : δ ≠ 0)
    (hdir : ∀ k, p.thrust k = ‖p.thrust k‖ • p.b₃ k)
    (hmix : ∀ k, MixerOK Q (Q.mass * ‖p.thrust k‖) (p.torque k))
    (htilt : ∀ k, angle (p.b₃ k) up ≤ Q.tiltMax)
    (hrate : ∀ k, ‖p.rate k‖ ≤ Q.rateMax)
    (hspeed : ∀ k, ‖p.v k‖ ≤ Q.speedEnv)
    (hge : ∀ k, C.hingeLo ≤ p.η k) (hle : ∀ k, p.η k ≤ C.hingeHi)
    (hηrate : ∀ k, |p.η (k + 1) - p.η k| ≤ δ * C.hingeRate) : QuadTraj Q C δ where
  x := p.x
  v := p.v
  b₁ := p.b₁
  b₂ := p.b₂
  b₃ := p.b₃
  Ω := p.rate
  f k := Classical.choose (exists_motors_of_wrench (Q := Q) _ _ (hmix k).1 (hmix k).2.1
    (hmix k).2.2.1 (hmix k).2.2.2)
  η := p.η
  steps := p.steps
  translational k := by
    obtain ⟨-, hF, -⟩ := Classical.choose_spec (exists_motors_of_wrench (Q := Q) _ _
      (hmix k).1 (hmix k).2.1 (hmix k).2.2.1 (hmix k).2.2.2)
    rw [hF, mul_div_cancel_left₀ _ Q.mass_pos.ne', hkn, zero_mul, zero_mul, sub_zero, ← hdir k,
      RotPlan.thrust]
    simp only [smul_add, smul_sub, smul_smul, mul_inv_cancel₀ hδ, one_smul]
    abel
  rotational k := by
    obtain ⟨-, -, hτ⟩ := Classical.choose_spec (exists_motors_of_wrench (Q := Q) _ _
      (hmix k).1 (hmix k).2.1 (hmix k).2.2.1 (hmix k).2.2.2)
    rw [hτ]
    simp only [RotPlan.torque]
    rw [add_sub_cancel_right, inertiaInv_inertia, smul_smul, mul_inv_cancel₀ hδ, one_smul,
      add_sub_cancel]
  attitude k := by
    have hw : δ • worldRate (p.b₁ k) (p.b₂ k) (p.b₃ k) (p.rate k) = p.ω k := by
      have h : worldRate (p.b₁ k) (p.b₂ k) (p.b₃ k) (p.rate k) = ofF (p.b₁ k) (p.b₂ k) (p.rate k) :=
        rfl
      rw [h, RotPlan.rate, ofF_smul, smul_smul, mul_inv_cancel₀ hδ, one_smul,
        ofF_toF (p.b₁_unit k) (p.b₂_unit k) (p.b₁₂_orth k)]
    rw [hw]
    exact ⟨(p.evolve k).1, (p.evolve k).2, p.b₃_evolve k⟩
  b₁_unit := p.b₁_unit
  b₂_unit := p.b₂_unit
  b₁₂_orth := p.b₁₂_orth
  b₃_cross _ := rfl
  motor_nonneg k i := ((Classical.choose_spec (exists_motors_of_wrench (Q := Q) _ _
      (hmix k).1 (hmix k).2.1 (hmix k).2.2.1 (hmix k).2.2.2)).1 i).1
  motor_le k i := ((Classical.choose_spec (exists_motors_of_wrench (Q := Q) _ _
      (hmix k).1 (hmix k).2.1 (hmix k).2.2.1 (hmix k).2.2.2)).1 i).2
  tilt_le := htilt
  rate_le := hrate
  speed_le := hspeed
  hinge_ge := hge
  hinge_le := hle
  hinge_rate := hηrate

end VisionTracking

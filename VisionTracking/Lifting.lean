import VisionTracking.AxisAngle
import VisionTracking.Motors

/-!
# Lifting a kinematic plan to a rigid-body trajectory

A `KinPlan` fixes positions, velocities, a body frame and a hinge angle at every
step, with consecutive frames close enough to be one rotation apart. From it, the
dynamics of `QuadTraj` determine everything else:

* the thrust vector `T_k = (v_{k+1} - v_k)/δ + g e₃ + c_D ‖v_k‖ v_k`, which must point
  along `b₃` (`hdir`);
* the body rates `Ω_k`: the axis-angle vector of the frame change, in body
  coordinates, divided by `δ`;
* the torque `τ_k = J (Ω_{k+1} - Ω_k)/δ + Ω_k × J Ω_k`;
* the motor thrusts, from the inverse mixer, provided the wrench `(m ‖T_k‖, τ_k)`
  fits the motors (`MixerOK`).

`QuadTraj.ofPlan` turns a plan satisfying these budgets into a valid `QuadTraj`
with exactly the planned positions, frames and hinge.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {Q : QuadParams} {C : CameraParams} {δ : ℝ}

/-- The four mixer inequalities of `exists_motors_of_wrench`. -/
def MixerOK (Q : QuadParams) (F : ℝ) (τ : E3) : Prop :=
  |τ.ofLp 0| / (2 * Q.arm) + |τ.ofLp 2| / (4 * Q.kYaw) ≤ F / 4 ∧
  |τ.ofLp 1| / (2 * Q.arm) + |τ.ofLp 2| / (4 * Q.kYaw) ≤ F / 4 ∧
  F / 4 + |τ.ofLp 0| / (2 * Q.arm) + |τ.ofLp 2| / (4 * Q.kYaw) ≤ Q.fMotor ∧
  F / 4 + |τ.ofLp 1| / (2 * Q.arm) + |τ.ofLp 2| / (4 * Q.kYaw) ≤ Q.fMotor

/-- A kinematic plan. -/
structure KinPlan (Q : QuadParams) (C : CameraParams) (δ : ℝ) where
  x : ℕ → E3
  v : ℕ → E3
  b₁ : ℕ → E3
  b₂ : ℕ → E3
  η : ℕ → ℝ
  steps : StepsWith δ x v
  b₁_unit : ∀ k, ‖b₁ k‖ = 1
  b₂_unit : ∀ k, ‖b₂ k‖ = 1
  b₁₂_orth : ∀ k, ⟪b₁ k, b₂ k⟫ = 0
  near : ∀ k, 1 ≤ frameTrace (b₁ k) (b₂ k) (b₁ (k + 1)) (b₂ (k + 1))

namespace KinPlan

variable (p : KinPlan Q C δ)

noncomputable def b₃ (k : ℕ) : E3 := cross (p.b₁ k) (p.b₂ k)

/-- The rotation vector taking frame `k` to frame `k + 1`. -/
noncomputable def rotVec (k : ℕ) : E3 :=
  frameRotVec (p.b₁ k) (p.b₂ k) (p.b₁ (k + 1)) (p.b₂ (k + 1))

/-- Body rates: the rotation vector in body coordinates, per unit time. -/
noncomputable def rate (k : ℕ) : E3 := δ⁻¹ • toF (p.b₁ k) (p.b₂ k) (p.rotVec k)

/-- Required thrust per unit mass. -/
noncomputable def thrust (k : ℕ) : E3 :=
  δ⁻¹ • (p.v (k + 1) - p.v k) + Q.g • up + (Q.drag * ‖p.v k‖) • p.v k

/-- Required collective thrust per unit mass: the thrust plus what cancels the rotor-disc
normal force `-k_n ‖v‖ ⟪v, b₃⟫ b₃`. -/
noncomputable def collective (k : ℕ) : ℝ :=
  ‖p.thrust k‖ + Q.normalDrag * ‖p.v k‖ * ⟪p.v k, p.b₃ k⟫

/-- Required body torque. -/
noncomputable def torque (k : ℕ) : E3 :=
  Q.inertia (δ⁻¹ • (p.rate (k + 1) - p.rate k)) + cross (p.rate k) (Q.inertia (p.rate k))

theorem rotVec_spec (k : ℕ) :
    ‖p.rotVec k‖ = rotAngle (p.b₁ k) (p.b₂ k) (p.b₁ (k + 1)) (p.b₂ (k + 1)) ∧
      rotate (p.rotVec k) (p.b₁ k) = p.b₁ (k + 1) ∧
      rotate (p.rotVec k) (p.b₂ k) = p.b₂ (k + 1) ∧
      rotate (p.rotVec k) (p.b₃ k) = p.b₃ (k + 1) :=
  frameRotVec_spec (p.b₁_unit k) (p.b₂_unit k) (p.b₁₂_orth k)
    (p.b₁_unit (k + 1)) (p.b₂_unit (k + 1)) (p.b₁₂_orth (k + 1)) (p.near k)

/-- The world angular velocity of the planned body rates, times `δ`, is the rotation
vector of the frame change. -/
theorem smul_worldRate_rate (hδ : δ ≠ 0) (k : ℕ) :
    δ • worldRate (p.b₁ k) (p.b₂ k) (p.b₃ k) (p.rate k) = p.rotVec k := by
  have h : worldRate (p.b₁ k) (p.b₂ k) (p.b₃ k) (p.rate k)
      = ofF (p.b₁ k) (p.b₂ k) (p.rate k) := rfl
  rw [h, rate, ofF_smul, smul_smul, mul_inv_cancel₀ hδ, one_smul,
    ofF_toF (p.b₁_unit k) (p.b₂_unit k) (p.b₁₂_orth k)]

/-- The body rates are the explicit rotation vector in body coordinates, per unit time. -/
theorem rate_eq (k : ℕ) : p.rate k = δ⁻¹ • psiVec (sigmaVec (toF (p.b₁ k) (p.b₂ k) (p.b₁ (k + 1)))
    (toF (p.b₁ k) (p.b₂ k) (p.b₂ (k + 1)))) := by
  rw [rate, rotVec, frameRotVec, toF_ofF (p.b₁_unit k) (p.b₂_unit k) (p.b₁₂_orth k)]

end KinPlan

/-- With no normal force, the collective is the thrust. -/
theorem KinPlan.collective_of_kn (p : KinPlan Q C δ) (hkn : Q.normalDrag = 0) (k : ℕ) :
    p.collective k = ‖p.thrust k‖ := by
  simp [KinPlan.collective, hkn]

theorem inertiaInv_inertia (Q : QuadParams) (y : E3) : Q.inertiaInv (Q.inertia y) = y := by
  have := Q.Jx_pos.ne'; have := Q.Jy_pos.ne'; have := Q.Jz_pos.ne'
  ext i; fin_cases i <;> simp [QuadParams.inertia, QuadParams.inertiaInv] <;> field_simp

/-- **Lifting.** A kinematic plan whose thrust points along `b₃` and whose wrench,
tilt, body rates, speed and hinge fit the quadrotor's limits is a valid rigid-body
trajectory with exactly the planned positions, frames and hinge. -/
noncomputable def QuadTraj.ofPlan (p : KinPlan Q C δ) (hδ : δ ≠ 0)
    (hdir : ∀ k, p.thrust k = ‖p.thrust k‖ • p.b₃ k)
    (hmix : ∀ k, MixerOK Q (Q.mass * p.collective k) (p.torque k))
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
    rw [hF, mul_div_cancel_left₀ _ Q.mass_pos.ne', KinPlan.collective, add_sub_cancel_right,
      ← hdir k, KinPlan.thrust]
    simp only [smul_add, smul_sub, smul_smul, mul_inv_cancel₀ hδ, one_smul]
    abel
  rotational k := by
    obtain ⟨-, -, hτ⟩ := Classical.choose_spec (exists_motors_of_wrench (Q := Q) _ _
      (hmix k).1 (hmix k).2.1 (hmix k).2.2.1 (hmix k).2.2.2)
    rw [hτ]
    simp only [KinPlan.torque]
    rw [add_sub_cancel_right, inertiaInv_inertia, smul_smul,
      mul_inv_cancel₀ hδ, one_smul, add_sub_cancel]
  attitude k := by
    rw [p.smul_worldRate_rate hδ k]
    obtain ⟨-, h1, h2, h3⟩ := p.rotVec_spec k
    exact ⟨h1.symm, h2.symm, h3.symm⟩
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

section OfPlan

variable (p : KinPlan Q C δ) (hδ : δ ≠ 0)
  (hdir : ∀ k, p.thrust k = ‖p.thrust k‖ • p.b₃ k)
  (hmix : ∀ k, MixerOK Q (Q.mass * p.collective k) (p.torque k))
  (htilt : ∀ k, angle (p.b₃ k) up ≤ Q.tiltMax) (hrate : ∀ k, ‖p.rate k‖ ≤ Q.rateMax)
  (hspeed : ∀ k, ‖p.v k‖ ≤ Q.speedEnv) (hge : ∀ k, C.hingeLo ≤ p.η k)
  (hle : ∀ k, p.η k ≤ C.hingeHi) (hηrate : ∀ k, |p.η (k + 1) - p.η k| ≤ δ * C.hingeRate)

theorem ofPlan_x : (QuadTraj.ofPlan p hδ hdir hmix htilt hrate hspeed hge hle hηrate).x = p.x :=
  rfl
theorem ofPlan_b₁ :
    (QuadTraj.ofPlan p hδ hdir hmix htilt hrate hspeed hge hle hηrate).b₁ = p.b₁ := rfl
theorem ofPlan_b₃ :
    (QuadTraj.ofPlan p hδ hdir hmix htilt hrate hspeed hge hle hηrate).b₃ = p.b₃ := rfl
theorem ofPlan_η : (QuadTraj.ofPlan p hδ hdir hmix htilt hrate hspeed hge hle hηrate).η = p.η :=
  rfl

end OfPlan

end VisionTracking

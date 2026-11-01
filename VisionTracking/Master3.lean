import VisionTracking.UnderTraj

/-!
# The master inequality, version 3 (camera on top, drone underneath, up to 55 m/s)

`master_sufficient3`: if `MasterIneq3` holds for a planner with four frames of lag, a
position-only strategy keeps every target that starts in steady flight in view in every
frame. The drone flies under the target as a valid rigid-body quadrotor, with its yaw locked
to the target's lateral direction and its top camera's hinge pointing straight up.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {P : TargetParams} {Q : QuadParams} {C : CameraParams} {δ : ℝ}

/-- A position-only strategy for targets that start in steady flight. -/
structure SteadyStrategy (P : TargetParams) (Q : QuadParams) (C : CameraParams) (δ : ℝ)
    (p₀ v₀ a₀ : E3) where
  play : (T : TargetTraj P δ) → T.StartsSteady p₀ v₀ a₀ → QuadTraj Q C δ
  pos_causal : ∀ (T T' : TargetTraj P δ) (hT : T.StartsSteady p₀ v₀ a₀)
    (hT' : T'.StartsSteady p₀ v₀ a₀) (k : ℕ), (∀ j ≤ k, T.p j = T'.p j) →
    (∀ j ≤ k + 1, (play T hT).state j = (play T' hT').state j) ∧
      ∀ j ≤ k, (play T hT).f j = (play T' hT').f j

/-- **Maintainable from a steady start.** -/
def MaintainableSteady (P : TargetParams) (Q : QuadParams) (C : CameraParams) (δ : ℝ)
    (p₀ v₀ a₀ : E3) : Prop :=
  ∃ σ : SteadyStrategy P Q C δ p₀ v₀ a₀, ∀ (T : TargetTraj P δ) (hT : T.StartsSteady p₀ v₀ a₀),
    KeepsInView C P.size (σ.play T hT) T

namespace Under

open Budget3 Overhead

variable {F : FIR} {d : ℝ}

theorem traj_causal (hlag : ∀ i < 4, F.h i = 0) (h : MasterIneq3 P Q C δ F d)
    (T T' : TargetTraj P δ) (a₀ : E3) (hS : T.StartsSteady (T.p 0) (T.v 0) a₀)
    (hS' : T'.StartsSteady (T'.p 0) (T'.v 0) a₀) (hv0 : T.v 0 = T'.v 0) (k : ℕ)
    (hp : ∀ j ≤ k, T.p j = T'.p j) :
    (∀ j ≤ k + 1, (traj T a₀ h hS).state j = (traj T' a₀ h hS').state j) ∧
      ∀ j ≤ k, (traj T a₀ h hS).f j = (traj T' a₀ h hS').f j := by
  have hδ := h.δ_pos
  have e0 := F.planPos_congr_lag hlag T T' a₀ ((-d) • up) k hp hv0
  have e1 : ∀ j ≤ k + 3, vP T a₀ F j = vP T' a₀ F j := by
    intro j hj
    have a := F.planPos_succ T a₀ ((-d) • up) j
    have b := F.planPos_succ T' a₀ ((-d) • up) j
    rw [e0 (j + 1) (by omega), e0 j (by omega)] at a
    have : δ • vP T a₀ F j = δ • vP T' a₀ F j := by
      unfold vP; rw [← add_right_inj (F.planPos T' a₀ ((-d) • up) j), ← a, b]
    exact smul_right_injective E3 hδ.ne' this
  have e2 : ∀ j ≤ k + 2, F.planAcc T a₀ j = F.planAcc T' a₀ j := by
    intro j hj
    have a' : vP T a₀ F (j + 1) = vP T a₀ F j + δ • F.planAcc T a₀ j :=
      F.planVel_succ T a₀ hδ.ne' j
    have b' : vP T' a₀ F (j + 1) = vP T' a₀ F j + δ • F.planAcc T' a₀ j :=
      F.planVel_succ T' a₀ hδ.ne' j
    rw [e1 (j + 1) (by omega), e1 j (by omega)] at a'
    have : δ • F.planAcc T a₀ j = δ • F.planAcc T' a₀ j := by
      rw [← add_right_inj (vP T' a₀ F j), ← a', b']
    exact smul_right_injective E3 hδ.ne' this
  have ethr : ∀ j ≤ k + 2, thr T a₀ Q F j = thr T' a₀ Q F j := by
    intro j hj; unfold thr; rw [e2 j hj, e1 j (by omega)]
  have en : ∀ j ≤ k + 2, nP T a₀ Q F j = nP T' a₀ Q F j := by
    intro j hj; unfold nP; rw [ethr j hj]
  have el : ∀ j ≤ k + 2, lP T a₀ F j = lP T' a₀ F j := by
    intro j hj; unfold lP hP; rw [e1 j (by omega)]
  have eB1 : ∀ j ≤ k + 2, B1 T a₀ Q F j = B1 T' a₀ Q F j := by
    intro j hj; unfold B1; rw [en j hj, el j hj]
  have eB2 : ∀ j ≤ k + 2, B2 T a₀ Q F j = B2 T' a₀ Q F j := by
    intro j hj; unfold B2; rw [en j hj, el j hj]
  have eeta : ∀ j ≤ k + 2, eta T a₀ Q C F j = eta T' a₀ Q C F j := by
    intro j hj; unfold eta phi; rw [eB1 j hj, en j hj]
  have erate : ∀ j ≤ k + 1, (kp T a₀ h hS).rate j = (kp T' a₀ h hS').rate j := by
    intro j hj
    simp only [KinPlan.rate, KinPlan.rotVec, kp]
    rw [eB1 j (by omega), eB2 j (by omega), eB1 (j + 1) (by omega), eB2 (j + 1) (by omega)]
  have etorque : ∀ j ≤ k, (kp T a₀ h hS).torque j = (kp T' a₀ h hS').torque j := by
    intro j hj
    simp only [KinPlan.torque]
    rw [erate j (by omega), erate (j + 1) (by omega)]
  have ethrust : ∀ j ≤ k, (kp T a₀ h hS).thrust j = (kp T' a₀ h hS').thrust j := by
    intro j hj
    rw [kp_thrust, kp_thrust, ethr j (by omega)]
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · simp only [QuadTraj.state, traj, QuadTraj.ofPlan]
    have hx : (kp T a₀ h hS).x j = (kp T' a₀ h hS').x j := e0 j (by omega)
    have hv : (kp T a₀ h hS).v j = (kp T' a₀ h hS').v j := e1 j (by omega)
    have h1 : (kp T a₀ h hS).b₁ j = (kp T' a₀ h hS').b₁ j := eB1 j (by omega)
    have h2 : (kp T a₀ h hS).b₂ j = (kp T' a₀ h hS').b₂ j := eB2 j (by omega)
    have h3 : (kp T a₀ h hS).b₃ j = (kp T' a₀ h hS').b₃ j := by
      rw [kp_b₃, kp_b₃, en j (by omega)]
    have h4 : (kp T a₀ h hS).η j = (kp T' a₀ h hS').η j := eeta j (by omega)
    rw [hx, hv, h1, h2, h3, erate j hj, h4]
  · simp only [traj, QuadTraj.ofPlan]
    exact motors_congr (by rw [ethrust j hj]) (etorque j hj)
      (kp_mix T a₀ h hS j).1 (kp_mix T a₀ h hS j).2.1 (kp_mix T a₀ h hS j).2.2.1
      (kp_mix T a₀ h hS j).2.2.2 (kp_mix T' a₀ h hS' j).1 (kp_mix T' a₀ h hS' j).2.1
      (kp_mix T' a₀ h hS' j).2.2.1 (kp_mix T' a₀ h hS' j).2.2.2

end Under

/-- **Master inequality, version 3, sufficient side.** If `MasterIneq3` holds for a planner
with four frames of lag, a position-only strategy keeps every target that starts in steady
flight in view in every frame: the drone flies underneath as a valid rigid-body quadrotor,
yaw locked to the target's lateral direction, top camera pointing straight up. -/
theorem master_sufficient3 (F : FIR) (hlag : ∀ i < 4, F.h i = 0) {d : ℝ}
    (h : MasterIneq3 P Q C δ F d) (p₀ v₀ a₀ : E3) : MaintainableSteady P Q C δ p₀ v₀ a₀ := by
  have hS_of : ∀ T : TargetTraj P δ, T.StartsSteady p₀ v₀ a₀ →
      T.StartsSteady (T.p 0) (T.v 0) a₀ :=
    fun T hT => ⟨⟨rfl, rfl, by rw [hT.1.2.1]; exact hT.1.2.2⟩, hT.2⟩
  exact ⟨{ play := fun T hT => Under.traj T a₀ h (hS_of T hT)
           pos_causal := fun T T' hT hT' k hp =>
             Under.traj_causal hlag h T T' a₀ (hS_of T hT) (hS_of T' hT')
               (by rw [hT.1.2.1, hT'.1.2.1]) k hp },
    fun T hT => Under.traj_keeps T a₀ h (hS_of T hT)⟩

end VisionTracking

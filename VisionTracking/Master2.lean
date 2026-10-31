import VisionTracking.DownPlan
import VisionTracking.Master

/-!
# The master inequality, version 2 (yaw-free down-looking camera)

`master_sufficient2`: if `MasterIneq2` holds for a planner with four frames of lag, a
position-only strategy keeps every target with the given start in view. The drone
flies the yaw-free overhead formation (camera straight down, frame parallel
transported) as a valid rigid-body quadrotor.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {P : TargetParams} {Q : QuadParams} {C : CameraParams} {δ : ℝ}

namespace Down

open Budget2 Overhead

variable {F : FIR} {d : ℝ}

theorem traj_causal (hlag : ∀ i < 4, F.h i = 0) (h : MasterIneq2 P Q C δ F d)
    (T T' : TargetTraj P δ) (a₀ : E3) (hS : T.StartsAt (T.p 0) (T.v 0) a₀)
    (hS' : T'.StartsAt (T'.p 0) (T'.v 0) a₀) (hv0 : T.v 0 = T'.v 0) (k : ℕ)
    (hp : ∀ j ≤ k, T.p j = T'.p j) :
    (∀ j ≤ k + 1, (traj T a₀ h hS).state j = (traj T' a₀ h hS').state j) ∧
      ∀ j ≤ k, (traj T a₀ h hS).f j = (traj T' a₀ h hS').f j := by
  have hδ := h.δ_pos
  have e0 := F.planPos_congr_lag hlag T T' a₀ (d • up) k hp hv0
  have e1 : ∀ j ≤ k + 3, vP T a₀ F j = vP T' a₀ F j := by
    intro j hj
    have a := F.planPos_succ T a₀ (d • up) j
    have b := F.planPos_succ T' a₀ (d • up) j
    rw [e0 (j + 1) (by omega), e0 j (by omega)] at a
    have : δ • vP T a₀ F j = δ • vP T' a₀ F j := by
      unfold vP; rw [← add_right_inj (F.planPos T' a₀ (d • up) j), ← a, b]
    exact smul_right_injective E3 hδ.ne' this
  have e2 : ∀ j ≤ k + 2, F.planAcc T a₀ j = F.planAcc T' a₀ j := by
    intro j hj
    have a' : vP T a₀ F (j + 1) = vP T a₀ F j + δ • F.planAcc T a₀ j := F.planVel_succ T a₀ hδ.ne' j
    have b' : vP T' a₀ F (j + 1) = vP T' a₀ F j + δ • F.planAcc T' a₀ j :=
      F.planVel_succ T' a₀ hδ.ne' j
    rw [e1 (j + 1) (by omega), e1 j (by omega)] at a'
    have : δ • F.planAcc T a₀ j = δ • F.planAcc T' a₀ j := by
      rw [← add_right_inj (vP T' a₀ F j), ← a', b']
    exact smul_right_injective E3 hδ.ne' this
  have en : ∀ j ≤ k + 2, n T a₀ Q F j = n T' a₀ Q F j := by
    intro j hj; unfold n thr; rw [e2 j hj, e1 j (by omega)]
  have eω : ∀ j ≤ k + 1, ω T a₀ Q F j = ω T' a₀ Q F j := by
    intro j hj; unfold ω; rw [en j (by omega), en (j + 1) (by omega)]
  have eb1 : ∀ j ≤ k + 2, b1 T a₀ Q F j = b1 T' a₀ Q F j := by
    intro j
    induction j with
    | zero => intro _; simp only [b1]; rw [en 0 (by omega)]
    | succ j ih => intro hj; simp only [b1]; rw [ih (by omega), eω j (by omega)]
  have eb2 : ∀ j ≤ k + 2, b2 T a₀ Q F j = b2 T' a₀ Q F j := by
    intro j hj; unfold b2; rw [en j hj, eb1 j hj]
  have erate : ∀ j ≤ k + 1, (rp T a₀ h hS).rate j = (rp T' a₀ h hS').rate j := by
    intro j hj
    simp only [RotPlan.rate, rp]
    rw [eb1 j (by omega), eb2 j (by omega), eω j hj]
  have etorque : ∀ j ≤ k, (rp T a₀ h hS).torque j = (rp T' a₀ h hS').torque j := by
    intro j hj
    simp only [RotPlan.torque]
    rw [erate j (by omega), erate (j + 1) (by omega)]
  have ethrust : ∀ j ≤ k, (rp T a₀ h hS).thrust j = (rp T' a₀ h hS').thrust j := by
    intro j hj
    rw [rp_thrust, rp_thrust]; unfold thr; rw [e2 j (by omega), e1 j (by omega)]
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · simp only [QuadTraj.state, traj, QuadTraj.ofRotPlan]
    have hx : (rp T a₀ h hS).x j = (rp T' a₀ h hS').x j := e0 j (by omega)
    have hv : (rp T a₀ h hS).v j = (rp T' a₀ h hS').v j := e1 j (by omega)
    have h1 : (rp T a₀ h hS).b₁ j = (rp T' a₀ h hS').b₁ j := eb1 j (by omega)
    have h2 : (rp T a₀ h hS).b₂ j = (rp T' a₀ h hS').b₂ j := eb2 j (by omega)
    have h3 : (rp T a₀ h hS).b₃ j = (rp T' a₀ h hS').b₃ j := by
      rw [rp_b₃, rp_b₃, en j (by omega)]
    rw [hx, hv, h1, h2, h3, erate j hj]
    rfl
  · simp only [traj, QuadTraj.ofRotPlan]
    exact motors_congr (by rw [ethrust j hj]) (etorque j hj)
      (rp_mix T a₀ h hS j).1 (rp_mix T a₀ h hS j).2.1 (rp_mix T a₀ h hS j).2.2.1
      (rp_mix T a₀ h hS j).2.2.2 (rp_mix T' a₀ h hS' j).1 (rp_mix T' a₀ h hS' j).2.1
      (rp_mix T' a₀ h hS' j).2.2.1 (rp_mix T' a₀ h hS' j).2.2.2

end Down

/-- **Master inequality, version 2, sufficient side.** -/
theorem master_sufficient2 (F : FIR) (hlag : ∀ i < 4, F.h i = 0) {d : ℝ}
    (h : MasterIneq2 P Q C δ F d) (p₀ v₀ a₀ : E3) : Maintainable P Q C δ p₀ v₀ a₀ := by
  have hS_of : ∀ T : TargetTraj P δ, T.StartsAt p₀ v₀ a₀ → T.StartsAt (T.p 0) (T.v 0) a₀ :=
    fun T hT => ⟨rfl, rfl, by rw [hT.2.1]; exact hT.2.2⟩
  have pos : ∀ (T T' : TargetTraj P δ) (hT : T.StartsAt p₀ v₀ a₀) (hT' : T'.StartsAt p₀ v₀ a₀)
      (k : ℕ), (∀ j ≤ k, T.p j = T'.p j) →
      (∀ j ≤ k + 1, (Down.traj T a₀ h (hS_of T hT)).state j
          = (Down.traj T' a₀ h (hS_of T' hT')).state j) ∧
        ∀ j ≤ k, (Down.traj T a₀ h (hS_of T hT)).f j = (Down.traj T' a₀ h (hS_of T' hT')).f j :=
    fun T T' hT hT' k hp => Down.traj_causal hlag h T T' a₀ (hS_of T hT) (hS_of T' hT')
      (by rw [hT.2.1, hT'.2.1]) k hp
  exact ⟨{ play := fun T hT => Down.traj T a₀ h (hS_of T hT)
           causal := fun T T' hT hT' k hpv => pos T T' hT hT' k (fun j hj => (hpv j hj).1)
           pos_causal := pos }, fun T hT => Down.traj_keeps T a₀ h (hS_of T hT)⟩

end VisionTracking

import VisionTracking.OverheadPlan
import VisionTracking.DirectionalSpeed

/-!
# The master inequality

**Sufficiency** (`master_sufficient`): if the master budget `MasterIneq` holds for a
planner filter with four frames of lag and a standoff `d`, then tracking is
maintainable by a position-only strategy: the overhead formation flown by a valid
rigid-body quadrotor.

**Necessity** (`master_necessary`): if tracking is maintainable even with full
information, then the target can fly faster than the quadrotor can sustain in no
admissible direction (directional speed limits).
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {P : TargetParams} {Q : QuadParams} {C : CameraParams} {δ : ℝ}

/-- Causality with lag `L`: if the filter vanishes below lag `L`, the planned position at
step `j ≤ k + L` depends only on target positions up to `k`. -/
theorem FIR.planPos_congr_lag (F : FIR) {L : ℕ} (hlag : ∀ i < L, F.h i = 0)
    (T T' : TargetTraj P δ) (a₀ off : E3) (k : ℕ) (hp : ∀ j ≤ k, T.p j = T'.p j)
    (hv : T.v 0 = T'.v 0) : ∀ j ≤ k + L, F.planPos T a₀ off j = F.planPos T' a₀ off j := by
  intro j hj
  unfold FIR.planPos
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i < L
  · simp [hlag i hi]
  · congr 1
    unfold TargetTraj.ext
    split_ifs with hn
    · exact hp _ (by omega)
    · rw [hp 0 (by omega), hv]

theorem motors_congr {F F' : ℝ} {τ τ' : E3} (hF : F = F') (hτ : τ = τ') (h1 h2 h3 h4 h1' h2' h3' h4') :
    Classical.choose (exists_motors_of_wrench (Q := Q) F τ h1 h2 h3 h4)
      = Classical.choose (exists_motors_of_wrench (Q := Q) F' τ' h1' h2' h3' h4') := by
  subst hF; subst hτ; rfl

namespace Overhead

open Budget

variable {F : FIR} {d : ℝ}

/-- **Causality of the overhead plan.** -/
theorem traj_causal (hlag : ∀ i < 4, F.h i = 0) (h : MasterIneq P Q C δ F d)
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
    have a := F.planVel_succ T a₀ hδ.ne' j
    have b := F.planVel_succ T' a₀ hδ.ne' j
    have a' : vP T a₀ F (j + 1) = vP T a₀ F j + δ • F.planAcc T a₀ j := a
    have b' : vP T' a₀ F (j + 1) = vP T' a₀ F j + δ • F.planAcc T' a₀ j := b
    rw [e1 (j + 1) (by omega), e1 j (by omega)] at a'
    have : δ • F.planAcc T a₀ j = δ • F.planAcc T' a₀ j := by
      rw [← add_right_inj (vP T' a₀ F j), ← a', b']
    exact smul_right_injective E3 hδ.ne' this
  have e3 : ∀ j ≤ k + 2, thr T a₀ Q F j = thr T' a₀ Q F j := by
    intro j hj; unfold thr; rw [e2 j hj, e1 j (by omega)]
  have eb3 : ∀ j ≤ k + 2, b3 T a₀ Q F j = b3 T' a₀ Q F j := by
    intro j hj; unfold b3; rw [e3 j hj]
  have eb1 : ∀ j ≤ k + 2, b1 T a₀ Q F j = b1 T' a₀ Q F j := by
    intro j hj; unfold b1; rw [eb3 j hj]
  have eb2 : ∀ j ≤ k + 2, b2 T a₀ Q F j = b2 T' a₀ Q F j := by
    intro j hj; unfold b2; rw [eb3 j hj, eb1 j hj]
  have eη : ∀ j ≤ k + 2, eta T a₀ Q C F j = eta T' a₀ Q C F j := by
    intro j hj; unfold eta tilt; rw [eb3 j hj]
  have erate : ∀ j ≤ k + 1, (kin T a₀ h hS).rate j = (kin T' a₀ h hS').rate j := by
    intro j hj
    simp only [KinPlan.rate, KinPlan.rotVec, kin]
    rw [eb1 j (by omega), eb2 j (by omega), eb1 (j + 1) (by omega), eb2 (j + 1) (by omega)]
  have etorque : ∀ j ≤ k, (kin T a₀ h hS).torque j = (kin T' a₀ h hS').torque j := by
    intro j hj
    simp only [KinPlan.torque]
    rw [erate j (by omega), erate (j + 1) (by omega)]
  have ethrust : ∀ j ≤ k, (kin T a₀ h hS).thrust j = (kin T' a₀ h hS').thrust j := by
    intro j hj; rw [kin_thrust, kin_thrust, e3 j (by omega)]
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · simp only [QuadTraj.state, traj, QuadTraj.ofPlan]
    have hx : (kin T a₀ h hS).x j = (kin T' a₀ h hS').x j := e0 j (by omega)
    have hv : (kin T a₀ h hS).v j = (kin T' a₀ h hS').v j := e1 j (by omega)
    have h1 : (kin T a₀ h hS).b₁ j = (kin T' a₀ h hS').b₁ j := eb1 j (by omega)
    have h2 : (kin T a₀ h hS).b₂ j = (kin T' a₀ h hS').b₂ j := eb2 j (by omega)
    have h3 : (kin T a₀ h hS).b₃ j = (kin T' a₀ h hS').b₃ j := by
      rw [kin_b₃, kin_b₃, eb3 j (by omega)]
    have hη : (kin T a₀ h hS).η j = (kin T' a₀ h hS').η j := eη j (by omega)
    rw [hx, hv, h1, h2, h3, erate j hj, hη]
  · simp only [traj, QuadTraj.ofPlan]
    exact motors_congr (by rw [ethrust j hj]) (etorque j hj)
      (kin_mix T a₀ h hS j).1 (kin_mix T a₀ h hS j).2.1 (kin_mix T a₀ h hS j).2.2.1
      (kin_mix T a₀ h hS j).2.2.2 (kin_mix T' a₀ h hS' j).1 (kin_mix T' a₀ h hS' j).2.1
      (kin_mix T' a₀ h hS' j).2.2.1 (kin_mix T' a₀ h hS' j).2.2.2

end Overhead

/-- **Master inequality, sufficient side.** -/
theorem master_sufficient (F : FIR) (hlag : ∀ i < 4, F.h i = 0) {d : ℝ}
    (h : MasterIneq P Q C δ F d) (p₀ v₀ a₀ : E3) : Maintainable P Q C δ p₀ v₀ a₀ := by
  have hS_of : ∀ T : TargetTraj P δ, T.StartsAt p₀ v₀ a₀ → T.StartsAt (T.p 0) (T.v 0) a₀ :=
    fun T hT => ⟨rfl, rfl, by rw [hT.2.1]; exact hT.2.2⟩
  have pos : ∀ (T T' : TargetTraj P δ) (hT : T.StartsAt p₀ v₀ a₀) (hT' : T'.StartsAt p₀ v₀ a₀)
      (k : ℕ), (∀ j ≤ k, T.p j = T'.p j) →
      (∀ j ≤ k + 1, (Overhead.traj T a₀ h (hS_of T hT)).state j
          = (Overhead.traj T' a₀ h (hS_of T' hT')).state j) ∧
        ∀ j ≤ k, (Overhead.traj T a₀ h (hS_of T hT)).f j
          = (Overhead.traj T' a₀ h (hS_of T' hT')).f j :=
    fun T T' hT hT' k hp => Overhead.traj_causal hlag h T T' a₀ (hS_of T hT) (hS_of T' hT')
      (by rw [hT.2.1, hT'.2.1]) k hp
  refine ⟨{ play := fun T hT => Overhead.traj T a₀ h (hS_of T hT)
            causal := fun T T' hT hT' k hpv => pos T T' hT hT' k (fun j hj => (hpv j hj).1)
            pos_causal := pos }, fun T hT => ?_⟩
  exact Overhead.traj_keeps T a₀ h (hS_of T hT)

/-- **Master inequality, necessary side.** -/
theorem master_necessary (hδ : 0 < δ) (hfine : δ * Q.drag * Q.speedEnv ≤ 1 / 2) (p₀ : E3)
    {u : E3} (hu : ‖u‖ = 1) (hclimb : |⟪u, up⟫| ≤ Real.sin P.climbMax)
    (h : MaintainableFullInfo P Q C δ p₀ (P.vMax • u) 0) : P.vMax ≤ Q.dirSpeed u := by
  by_contra hlt
  exact not_maintainable_of_dirSpeed_lt hδ hfine p₀ hu hclimb (lt_of_not_ge hlt) h

end VisionTracking

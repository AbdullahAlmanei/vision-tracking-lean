import VisionTracking.Master3
import VisionTracking.DirectionalSpeed

/-!
# P3, necessary side (full information)

Necessity results are stated in the strongest form: **no drone trajectory at all** keeps
the escaping target in view, even one planned with knowledge of the target's whole future.
The escaping targets start in steady flight, so they belong to the class covered by
`master_sufficient3`.

* `no_traj_keeps_of_dirSpeed_lt`: a target flying straight along an admissible direction
  `u` faster than the drone's drag-limited directional speed `dirSpeed u` (motors, tilt
  envelope, gravity) escapes every trajectory.
* `NecIneq3`: the directional speed wall in every admissible direction.
* `p3_bracket`: `MasterIneq3 ⇒` maintainable from every steady start `⇒ NecIneq3`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {P : TargetParams} {Q : QuadParams} {C : CameraParams} {δ : ℝ}

/-- **Directional speed wall, trajectory form.** -/
theorem no_traj_keeps_of_dirSpeed_lt (hkn : Q.normalDrag = 0) (hδ : 0 < δ)
    (hfine : δ * Q.drag * Q.speedEnv ≤ 1 / 2) (p₀ : E3) {u : E3} (hu : ‖u‖ = 1)
    (hclimb : |⟪u, up⟫| ≤ Real.sin P.climbMax) (hslow : Q.dirSpeed u < P.vMax)
    (d : QuadTraj Q C δ) :
    ¬ KeepsInView C P.size d (straightTarget P hδ.le p₀ u hu hclimb) := by
  intro hkeep
  have hc := Q.drag_pos
  obtain ⟨V, K, hV, hx⟩ : ∃ V K : ℝ, V < P.vMax ∧ ∀ k : ℕ, ⟪d.x k - d.x 0, u⟫ ≤ k * δ * V + K := by
    rcases le_or_gt P.vMax Q.speedEnv with henv | henv
    · set V := (Q.dirSpeed u + P.vMax) / 2 with hVdef
      have hds0 : 0 ≤ Q.dirSpeed u := Real.sqrt_nonneg _
      have hdsV : Q.dirSpeed u ≤ V := by rw [hVdef]; linarith
      have hV0 : 0 < V := by
        have := P.vMin_pos.trans_le P.vMin_le_vMax; positivity
      have hVlt : V < P.vMax := by rw [hVdef]; linarith
      have hpush : Q.push u ≤ Q.drag * V ^ 2 := by
        have h1 : Q.dirSpeed u ^ 2 = max 0 (Q.push u) / Q.drag :=
          Real.sq_sqrt (div_nonneg (le_max_left _ _) hc.le)
        have h2 : Q.dirSpeed u ^ 2 ≤ V ^ 2 := pow_le_pow_left₀ hds0 hdsV 2
        have h3 : max 0 (Q.push u) ≤ Q.drag * V ^ 2 := by
          rw [h1, div_le_iff₀ hc] at h2; linarith
        exact (le_max_right _ _).trans h3
      exact ⟨V, _, hVlt, dir_displacement_le hkn d hδ hfine hu hV0 (by linarith) hpush⟩
    · refine ⟨Q.speedEnv, 0, henv, ?_⟩
      have hv : ∀ k, ⟪d.v k, u⟫ ≤ Q.speedEnv := fun k => by
        have := real_inner_le_norm (d.v k) u
        rw [hu, mul_one] at this
        exact this.trans (d.speed_le k)
      intro k
      simpa using inner_displacement_le hδ.le d.steps hv k
  obtain ⟨k, hk⟩ := straightTarget_escapes_of_displacement P hδ p₀ u hu hclimb hx hV
    (C.detectRange P.size)
  exact absurd (hkeep k).1 (not_le.2 hk)

/-- The straight target starts in steady flight. -/
theorem straightTarget_startsSteady (hδ : 0 < δ) (p₀ : E3) {u : E3} (hu : ‖u‖ = 1)
    (hclimb : |⟪u, up⟫| ≤ Real.sin P.climbMax) :
    (straightTarget P hδ.le p₀ u hu hclimb).StartsSteady p₀ (P.vMax • u) 0 :=
  ⟨straightTarget_startsAt P hδ.le p₀ u hu hclimb, by simp [straightTarget]⟩

theorem not_maintainableSteady_of_dirSpeed_lt (hkn : Q.normalDrag = 0) (hδ : 0 < δ)
    (hfine : δ * Q.drag * Q.speedEnv ≤ 1 / 2) (p₀ : E3) {u : E3} (hu : ‖u‖ = 1)
    (hclimb : |⟪u, up⟫| ≤ Real.sin P.climbMax) (hslow : Q.dirSpeed u < P.vMax) :
    ¬ MaintainableSteady P Q C δ p₀ (P.vMax • u) 0 := by
  rintro ⟨σ, hσ⟩
  have hS := straightTarget_startsSteady (P := P) hδ p₀ hu hclimb
  exact no_traj_keeps_of_dirSpeed_lt hkn hδ hfine p₀ hu hclimb hslow _ (hσ _ hS)

/-- **The necessary inequality**: in every admissible direction, the drone's drag-limited
directional speed covers the target's top speed. -/
def NecIneq3 (P : TargetParams) (Q : QuadParams) : Prop :=
  ∀ u : E3, ‖u‖ = 1 → |⟪u, up⟫| ≤ Real.sin P.climbMax → P.vMax ≤ Q.dirSpeed u

/-- **Master inequality, version 3, necessary side.** If every target starting in steady
flight can be kept in view (by any strategy with full information, indeed by any
trajectory), then `NecIneq3` holds. -/
theorem master_necessary3 (hkn : Q.normalDrag = 0) (hδ : 0 < δ) (hfine : δ * Q.drag * Q.speedEnv ≤ 1 / 2)
    (h : ∀ p₀ v₀ a₀ : E3, MaintainableSteady P Q C δ p₀ v₀ a₀) : NecIneq3 P Q := by
  intro u hu hclimb
  by_contra hlt
  exact not_maintainableSteady_of_dirSpeed_lt hkn hδ hfine 0 hu hclimb (not_le.1 hlt)
    (h 0 (P.vMax • u) 0)

/-- **P3 bracket** for the isotropic drag model (`k_n = 0`): `MasterIneq3` is sufficient,
`NecIneq3` is necessary. -/
theorem p3_bracket (F : FIR) (hlag : ∀ i < 4, F.h i = 0) {d : ℝ}
    (hkn : Q.normalDrag = 0) (hδ : 0 < δ) (hfine : δ * Q.drag * Q.speedEnv ≤ 1 / 2) :
    (MasterIneq3 P Q C δ F d → ∀ p₀ v₀ a₀ : E3, MaintainableSteady P Q C δ p₀ v₀ a₀) ∧
    ((∀ p₀ v₀ a₀ : E3, MaintainableSteady P Q C δ p₀ v₀ a₀) → NecIneq3 P Q) :=
  ⟨fun h p₀ v₀ a₀ => master_sufficient3 F hlag h p₀ v₀ a₀,
    master_necessary3 hkn hδ hfine⟩

end VisionTracking

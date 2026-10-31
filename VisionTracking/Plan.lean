import VisionTracking.SteadyChase
import VisionTracking.DirectionalSpeed
import VisionTracking.Motors
import VisionTracking.Rotation
import VisionTracking.SteadyFormation

/-!
# The plan: main statements still to be proved

Every statement is about the full rigid-body quadrotor (`QuadTraj`: body frame, body
rates, four bounded motors, hinged camera). As each is proved it moves to its own
file.

* `exists_rotate_frame`: any two right-handed orthonormal frames differ by a single
  Rodrigues rotation of angle at most `π`. This is needed to lift planned attitude
  changes to body rates for manoeuvring formations.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {P : TargetParams} {Q : QuadParams} {C : CameraParams} {δ : ℝ}

/-- **Axis-angle.** Two right-handed orthonormal frames differ by one Rodrigues
rotation of angle at most `π`. -/
theorem exists_rotate_frame {a₁ a₂ c₁ c₂ : E3} (ha₁ : ‖a₁‖ = 1) (ha₂ : ‖a₂‖ = 1)
    (ha : ⟪a₁, a₂⟫ = 0) (hc₁ : ‖c₁‖ = 1) (hc₂ : ‖c₂‖ = 1) (hc : ⟪c₁, c₂⟫ = 0) :
    ∃ ω : E3, ‖ω‖ ≤ π ∧ rotate ω a₁ = c₁ ∧ rotate ω a₂ = c₂ ∧
      rotate ω (cross a₁ a₂) = cross c₁ c₂ := by
  sorry

end VisionTracking

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

Currently empty: the remaining plan lives in
`docs/superpowers/plans/2026-10-31-p3-master-inequality.md`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {P : TargetParams} {Q : QuadParams} {C : CameraParams} {δ : ℝ}

end VisionTracking

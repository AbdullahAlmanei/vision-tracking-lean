import VisionTracking.PlannerSharp
import VisionTracking.Budget

/-!
# The master budget, version 2: yaw-free down-looking camera

Same planner and copying thrust as version 1, but:

* sharp planner constants `G₁, G₂, G₃`;
* the target's vertical acceleration is limited by `aVert`, which enters the vertical
  thrust bounds;
* the thrust direction `n = T/‖T‖` turns by at most `D3 = dT / Zlo` per step (sharp
  normalisation);
* the body frame is parallel transported by the minimal rotations `ω_k`, with
  `‖ω_k‖ ≤ θm = D3/√(1-D3²)`, `‖ω_{k+1} - ω_k‖ ≤ dω = 3 X / √(1-D3²)` and
  `X = d2T/Zlo + 2 dT²/Zlo²`;
* there is no yaw: the yaw torque is only the gyroscopic `(J_y - J_x) Ω₀ Ω₁`;
* the camera is fixed straight down the thrust axis, so the target is visible once
  `Θhi + μ ≤ α`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

namespace Budget2

variable (P : TargetParams) (Q : QuadParams) (C : CameraParams) (δ : ℝ) (F : FIR) (d : ℝ)

noncomputable def εD : ℝ := F.G1 * δ * P.jerk
noncomputable def εV : ℝ := F.G2 * δ ^ 2 * P.jerk
noncomputable def ρ : ℝ := F.G3 * δ ^ 3 * P.jerk
noncomputable def Vb : ℝ := P.vMax + εV P δ F
noncomputable def εT : ℝ := εD P δ F + Q.drag * (2 * P.vMax + εV P δ F) * εV P δ F
noncomputable def Zlo : ℝ :=
  Q.g - P.aVert - Q.drag * P.vMax ^ 2 * Real.sin P.climbMax - εT P Q δ F
noncomputable def Fhi : ℝ := Q.g + P.Amax + Q.drag * P.vMax ^ 2 + εT P Q δ F
noncomputable def Hhi : ℝ := P.Amax + Q.drag * P.vMax ^ 2 + εT P Q δ F
noncomputable def Θhi : ℝ := Real.arctan (Hhi P Q δ F / Zlo P Q δ F)
noncomputable def dT : ℝ :=
  δ * (F.H0 * P.jerk + 2 * Q.drag * Vb P δ F * (P.Amax + εD P δ F))
noncomputable def d2T : ℝ := F.TV * δ * P.jerk +
  Q.drag * (2 * Vb P δ F * F.H0 * δ ^ 2 * P.jerk + 4 * δ ^ 2 * (P.Amax + εD P δ F) ^ 2)
noncomputable def D3 : ℝ := dT P Q δ F / Zlo P Q δ F
noncomputable def X : ℝ := d2T P Q δ F / Zlo P Q δ F + 2 * dT P Q δ F ^ 2 / Zlo P Q δ F ^ 2
noncomputable def θm : ℝ := D3 P Q δ F / √(1 - D3 P Q δ F ^ 2)
noncomputable def dω : ℝ := 3 * X P Q δ F / √(1 - D3 P Q δ F ^ 2)
noncomputable def Ωmax : ℝ := θm P Q δ F / δ
noncomputable def dΩ : ℝ := (dω P Q δ F + 3 * θm P Q δ F ^ 2) / δ
noncomputable def τrp : ℝ := Budget.Jmax Q * dΩ P Q δ F / δ + Budget.Jmax Q * Ωmax P Q δ F ^ 2
noncomputable def τyaw : ℝ := |Q.Jy - Q.Jx| * Ωmax P Q δ F ^ 2
noncomputable def μ : ℝ := Real.arcsin (ρ P δ F / d)

end Budget2

open Budget2 in
/-- **The master inequality, version 2** (yaw-free down-looking camera). -/
structure MasterIneq2 (P : TargetParams) (Q : QuadParams) (C : CameraParams) (δ : ℝ)
    (F : FIR) (d : ℝ) : Prop where
  δ_pos : 0 < δ
  d_pos : 0 < d
  fine : δ * Q.drag * Q.speedEnv ≤ 1 / 2
  εV_lt : εV P δ F < P.vMin
  Zlo_pos : 0 < Zlo P Q δ F
  D3_lt : D3 P Q δ F < 1
  tilt : Θhi P Q δ F ≤ Q.tiltMax
  speed : Vb P δ F ≤ Q.speedEnv
  rate : Ωmax P Q δ F ≤ Q.rateMax
  mix_lo : τrp P Q δ F / (2 * Q.arm) + τyaw P Q δ F / (4 * Q.kYaw) ≤ Q.mass * Zlo P Q δ F / 4
  mix_hi : Q.mass * Fhi P Q δ F / 4 + τrp P Q δ F / (2 * Q.arm) + τyaw P Q δ F / (4 * Q.kYaw)
    ≤ Q.fMotor
  cam_down : C.hingeLo = -(π / 2)
  ρ_lt : ρ P δ F < d
  see : Θhi P Q δ F + μ P δ F d ≤ C.halfFov
  range : d + ρ P δ F ≤ C.detectRange P.size

end VisionTracking

import VisionTracking.PlanLemmas
import VisionTracking.FrameRate

/-!
# The master budget

Every quantity in the master inequality, as an explicit function of the target,
quadrotor and camera parameters, the step `δ`, the planner filter `F` and the
overhead standoff `d`. `MasterIneq` collects the inequalities that make the
overhead formation plan valid, with the target visible in every frame.

Planner errors: `εD = H₁ δ j` (acceleration), `εV = H₂ δ² j` (velocity),
`ρ = H₃ δ³ j` (position).

Thrust: the planned thrust is within `εT` of the copying thrust `T*`, so its vertical
part lies in `[Zlo, Zhi]`, its horizontal part in `[Hlo, Hhi]`, its norm is at most
`Fhi`, and its tilt lies in `[Θlo, Θhi]`.

Smoothness: the thrust changes by at most `dT` per step, with second differences at
most `d2T`. Hence the frame vectors move by at most `D1` per step, with second
differences at most `D2`, and the body rates and torque are bounded by `Ωmax` and
`τreq`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

namespace Budget

variable (P : TargetParams) (Q : QuadParams) (C : CameraParams) (δ : ℝ) (F : FIR) (d : ℝ)

noncomputable def εD : ℝ := F.H1 * δ * P.jerk
noncomputable def εV : ℝ := F.H2 * δ ^ 2 * P.jerk
noncomputable def ρ : ℝ := F.H3 * δ ^ 3 * P.jerk
noncomputable def Vb : ℝ := P.vMax + εV P δ F
noncomputable def εT : ℝ := εD P δ F + Q.drag * (2 * P.vMax + εV P δ F) * εV P δ F
noncomputable def Zlo : ℝ :=
  Q.g - P.Amax - Q.drag * P.vMax ^ 2 * Real.sin P.climbMax - εT P Q δ F
noncomputable def Zhi : ℝ :=
  Q.g + P.Amax + Q.drag * P.vMax ^ 2 * Real.sin P.climbMax + εT P Q δ F
noncomputable def Fhi : ℝ := Q.g + P.Amax + Q.drag * P.vMax ^ 2 + εT P Q δ F
noncomputable def Hhi : ℝ := P.Amax + Q.drag * P.vMax ^ 2 + εT P Q δ F
noncomputable def Hlo : ℝ := Hstar P Q - εT P Q δ F
noncomputable def Θhi : ℝ := Real.arctan (Hhi P Q δ F / Zlo P Q δ F)
noncomputable def Θlo : ℝ := Real.arctan (Hlo P Q δ F / Zhi P Q δ F)
noncomputable def dT : ℝ :=
  δ * (F.H0 * P.jerk + 2 * Q.drag * Vb P δ F * (P.Amax + εD P δ F))
noncomputable def d2T : ℝ := F.TV * δ * P.jerk +
  Q.drag * (2 * Vb P δ F * F.H0 * δ ^ 2 * P.jerk + 4 * δ ^ 2 * (P.Amax + εD P δ F) ^ 2)
noncomputable def D3 : ℝ := 2 * dT P Q δ F / Zlo P Q δ F
noncomputable def D3' : ℝ :=
  2 * d2T P Q δ F / Zlo P Q δ F + 6 * dT P Q δ F ^ 2 / Zlo P Q δ F ^ 2
noncomputable def mh : ℝ := Hlo P Q δ F / Fhi P Q δ F
noncomputable def D1b : ℝ := 4 * D3 P Q δ F / mh P Q δ F
noncomputable def D1b' : ℝ := (4 * D3' P Q δ F + 4 * D3 P Q δ F ^ 2) / mh P Q δ F
  + 24 * D3 P Q δ F ^ 2 / mh P Q δ F ^ 2
noncomputable def D1 : ℝ := D3 P Q δ F + D1b P Q δ F
noncomputable def D2 : ℝ := D1b' P Q δ F + D3' P Q δ F + 2 * D3 P Q δ F * D1b P Q δ F
noncomputable def Ωmax : ℝ := 2 * D1 P Q δ F / (δ * √(1 - (2 * D1 P Q δ F) ^ 2))
noncomputable def dΩ : ℝ :=
  18 * (D2 P Q δ F + D1 P Q δ F ^ 2) / (δ * √(1 - (2 * D1 P Q δ F) ^ 2))
noncomputable def Jmax : ℝ := max Q.Jx (max Q.Jy Q.Jz)
noncomputable def τreq : ℝ := Jmax Q * dΩ P Q δ F / δ + Jmax Q * Ωmax P Q δ F ^ 2
noncomputable def mixK : ℝ := 1 / (2 * Q.arm) + 1 / (4 * Q.kYaw)
noncomputable def μ : ℝ := Real.arcsin (ρ P δ F / d)

end Budget

open Budget in
/-- **The master inequality** (sufficient side), for the overhead formation at standoff
`d` with planner `F`. -/
structure MasterIneq (P : TargetParams) (Q : QuadParams) (C : CameraParams) (δ : ℝ)
    (F : FIR) (d : ℝ) : Prop where
  δ_pos : 0 < δ
  /-- The step is fine enough for the Euler drag model (`Model.lean`, `speedEnv`). -/
  fine : δ * Q.drag * Q.speedEnv ≤ 1 / 2
  d_pos : 0 < d
  εV_lt : εV P δ F < P.vMin
  Zlo_pos : 0 < Zlo P Q δ F
  Hlo_pos : 0 < Hlo P Q δ F
  tilt : Θhi P Q δ F ≤ Q.tiltMax
  D1_lt : 2 * D1 P Q δ F < 1
  speed : Vb P δ F ≤ Q.speedEnv
  rate : Ωmax P Q δ F ≤ Q.rateMax
  mix_lo : τreq P Q δ F * mixK Q ≤ Q.mass * Zlo P Q δ F / 4
  mix_hi : Q.mass * Fhi P Q δ F / 4 + τreq P Q δ F * mixK Q ≤ Q.fMotor
  hinge_rate : C.hingeLo = C.hingeHi ∨ π / 2 * D3 P Q δ F ≤ δ * C.hingeRate
  ρ_lt : ρ P δ F < d
  μ_le : μ P δ F d ≤ C.halfFov
  hinge_lo : C.hingeLo ≤ Θlo P Q δ F - π / 2 + C.halfFov - μ P δ F d
  hinge_hi : Θhi P Q δ F - π / 2 - C.halfFov + μ P δ F d ≤ C.hingeHi
  range : d + ρ P δ F ≤ C.detectRange P.size

end VisionTracking

import VisionTracking.Budget2
import VisionTracking.RateSharp
import VisionTracking.PlannerSnap

/-!
# The master budget, version 3: camera on top, drone underneath, targets up to 55 m/s

Speed-dependent: every quantity takes the target's current speed `s` and is valid over the
three steps that one control step looks at (speeds within `s ± 2δ Amax`). The design:

* the drone flies the filtered target path offset by `d` straight *down*;
* the thrust axis is `n = T/‖T‖`;
* the yaw is locked to the target's lateral direction: `b₂ = nrm (-ℓ + ⟪ℓ,n⟫ n)` with
  `ℓ = up × ĥ` and `ĥ` the planned horizontal heading, and `b₁ = b₂ × n` points backwards;
* the hinge points the camera straight up within the plane `span(b₁, n)`, clamped to the
  hinge range.

`MasterIneq3` requires the budget at every speed of the band.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

namespace Budget3

variable (P : TargetParams) (Q : QuadParams) (C : CameraParams) (δ : ℝ) (F : FIR) (d s : ℝ)

noncomputable def εD : ℝ := F.G1 * δ * P.jerk
noncomputable def εV : ℝ := F.G2 * δ ^ 2 * P.jerk
noncomputable def ρ : ℝ := F.G3 * δ ^ 3 * P.jerk
/-- Speed window covering three steps. -/
noncomputable def sHi : ℝ := min P.vMax (s + 2 * δ * P.Amax)
noncomputable def sLo : ℝ := max P.vMin (s - 2 * δ * P.Amax)
noncomputable def A : ℝ := P.aTan + sHi P δ s ^ 2 / P.turnRadius
noncomputable def εT : ℝ := εD P δ F + Q.drag * (2 * sHi P δ s + εV P δ F) * εV P δ F
noncomputable def Zlo : ℝ :=
  Q.g - P.aVert - Q.drag * sHi P δ s ^ 2 * Real.sin P.climbMax - εT P Q δ F s
noncomputable def Zhi : ℝ :=
  Q.g + P.aVert + Q.drag * sHi P δ s ^ 2 * Real.sin P.climbMax + εT P Q δ F s
noncomputable def Fw : ℝ :=
  Q.drag * sLo P δ s ^ 2 - P.aTan - Q.g * Real.sin P.climbMax - εT P Q δ F s
noncomputable def Tlo : ℝ := max (Zlo P Q δ F s) (Fw P Q δ F s)
noncomputable def Thi : ℝ := Q.g + A P δ s + Q.drag * sHi P δ s ^ 2 + εT P Q δ F s
noncomputable def Hhi : ℝ := A P δ s + Q.drag * sHi P δ s ^ 2 + εT P Q δ F s
noncomputable def vh : ℝ := sLo P δ s * Real.cos P.climbMax - εV P δ F
noncomputable def Lat : ℝ :=
  sHi P δ s ^ 2 / P.turnRadius + εD P δ F + A P δ s * (εV P δ F / vh P δ F s)
noncomputable def sb : ℝ := Lat P δ F s / Tlo P Q δ F s
noncomputable def M : ℝ := √(1 - sb P Q δ F s ^ 2)
noncomputable def dT : ℝ :=
  δ * (F.H0 * P.jerk + 2 * Q.drag * (sHi P δ s + εV P δ F) * (A P δ s + εD P δ F))
noncomputable def d2T : ℝ := F.H0 * δ ^ 2 * P.snap +
  Q.drag * (2 * (sHi P δ s + εV P δ F) * F.H0 * δ ^ 2 * P.jerk
    + 4 * δ ^ 2 * (A P δ s + εD P δ F) ^ 2)
noncomputable def dn : ℝ := dT P Q δ F s / Tlo P Q δ F s
noncomputable def xn : ℝ := d2T P Q δ F s / Tlo P Q δ F s + 2 * dT P Q δ F s ^ 2 / Tlo P Q δ F s ^ 2
noncomputable def d2n : ℝ :=
  2 * d2T P Q δ F s / Tlo P Q δ F s + 6 * dT P Q δ F s ^ 2 / Tlo P Q δ F s ^ 2
noncomputable def dl : ℝ := δ * (A P δ s + εD P δ F) / vh P δ F s
noncomputable def d2l : ℝ := 2 * (δ ^ 2 * F.H0 * P.jerk) / vh P δ F s + 6 * dl P δ F s ^ 2
/-- Crude bound on the step of each frame vector (used only to show consecutive frames are
close). -/
noncomputable def dbc : ℝ :=
  (2 * dl P δ F s + 2 * dn P Q δ F s) / M P Q δ F s + dn P Q δ F s
noncomputable def θa : ℝ :=
  √(dn P Q δ F s ^ 2 + ((dl P δ F s + sb P Q δ F s * dn P Q δ F s) / M P Q δ F s) ^ 2)
noncomputable def Gψ : ℝ := 1 / √(1 - θa P Q δ F s ^ 2)
/-- Sharp bound on the step of each frame vector: the rotation angle. -/
noncomputable def db : ℝ := Gψ P Q δ F s * θa P Q δ F s
noncomputable def rp2 : ℝ :=
  latRpSharp (sb P Q δ F s) (dn P Q δ F s) (dl P δ F s) (xn P Q δ F s) (db P Q δ F s)
noncomputable def yaw2 : ℝ :=
  latYawSharp (sb P Q δ F s) (dn P Q δ F s) (dl P δ F s) (xn P Q δ F s) (d2l P δ F s)
    (db P Q δ F s)
noncomputable def da : ℝ := √(rp2 P Q δ F s ^ 2 + yaw2 P Q δ F s ^ 2)
noncomputable def Ωb : ℝ := Gψ P Q δ F s * θa P Q δ F s / δ
noncomputable def dΩ : ℝ :=
  (Gψ P Q δ F s * da P Q δ F s + (Gψ P Q δ F s - 1) * θa P Q δ F s) / δ
noncomputable def dΩz : ℝ :=
  (Gψ P Q δ F s * yaw2 P Q δ F s + (Gψ P Q δ F s - 1) * θa P Q δ F s) / δ
/-- Roll and pitch: inertia and gyroscopic coupling of those axes only. -/
noncomputable def Jxy : ℝ := max Q.Jx Q.Jy
noncomputable def Jg : ℝ := max |Q.Jz - Q.Jy| |Q.Jx - Q.Jz|
noncomputable def dΩrp : ℝ :=
  (Gψ P Q δ F s * |rp2 P Q δ F s| + (Gψ P Q δ F s - 1) * θa P Q δ F s) / δ
noncomputable def τrp : ℝ := Jxy Q * dΩrp P Q δ F s / δ + Jg Q * Ωb P Q δ F s ^ 2
noncomputable def τyaw : ℝ := Q.Jz * dΩz P Q δ F s / δ + |Q.Jy - Q.Jx| * Ωb P Q δ F s ^ 2
/-- Forward thrust lower bound along the planned heading. -/
noncomputable def Nlo : ℝ :=
  Q.drag * sLo P δ s ^ 2 * Real.cos P.climbMax - A P δ s
    - Thi P Q δ F s * (εV P δ F / vh P δ F s) - εT P Q δ F s
noncomputable def φlo : ℝ :=
  Real.arctan (if 0 ≤ Nlo P Q δ F s then Nlo P Q δ F s / Zhi P Q δ F s
    else Nlo P Q δ F s / (Zlo P Q δ F s * M P Q δ F s))
noncomputable def φhi : ℝ := Real.arctan (Hhi P Q δ F s / (Zlo P Q δ F s * M P Q δ F s))
noncomputable def miss : ℝ :=
  max 0 (max ((π / 2 - φlo P Q δ F s) - C.hingeHi) (C.hingeLo - (π / 2 - φhi P Q δ F s)))
noncomputable def camOff : ℝ := Real.arccos (M P Q δ F s * Real.cos (miss P Q C δ F s))
noncomputable def μ : ℝ := Real.arcsin (ρ P δ F / d)
/-! ### Collective with the rotor-disc normal force -/
/-- Speed window of the planned velocity. -/
noncomputable def sLp : ℝ := sLo P δ s - εV P δ F
noncomputable def sHp : ℝ := sHi P δ s + εV P δ F
/-- Lower bound on `⟪vP, thr⟫`: the power of the planned thrust. -/
noncomputable def VTlo : ℝ :=
  Q.drag * sLp P δ F s ^ 3 - sHp P δ F s * (A P δ s + εD P δ F)
    - Q.g * (sHi P δ s * Real.sin P.climbMax + εV P δ F)
/-- Bounds on the collective `‖thr‖ + k_n ‖vP‖ ⟪vP, nP⟫`. -/
noncomputable def Clo : ℝ :=
  Tlo P Q δ F s + Q.normalDrag * min (sLp P δ F s * VTlo P Q δ F s / Thi P Q δ F s)
    (sHp P δ F s * VTlo P Q δ F s / Tlo P Q δ F s)
noncomputable def Chi : ℝ := Thi P Q δ F s + Q.normalDrag * sHp P δ F s ^ 2
noncomputable def hingeStep : ℝ := π / 2 * (db P Q δ F s + dn P Q δ F s) / M P Q δ F s

end Budget3

open Budget3 in
/-- **The master inequality, version 3** (camera on top, drone underneath). -/
structure MasterIneq3 (P : TargetParams) (Q : QuadParams) (C : CameraParams) (δ : ℝ)
    (F : FIR) (d : ℝ) : Prop where
  δ_pos : 0 < δ
  d_pos : 0 < d
  speed : P.vMax + εV P δ F ≤ Q.speedEnv
  ρ_lt : ρ P δ F < d
  range : d + ρ P δ F ≤ C.detectRange P.size
  zlo_pos : ∀ s ∈ Set.Icc P.vMin P.vMax, 0 < Zlo P Q δ F s
  vh_pos : ∀ s ∈ Set.Icc P.vMin P.vMax, 0 < vh P δ F s
  sb_lt : ∀ s ∈ Set.Icc P.vMin P.vMax, sb P Q δ F s < 1
  near : ∀ s ∈ Set.Icc P.vMin P.vMax, dbc P Q δ F s ≤ 1
  θ_lt : ∀ s ∈ Set.Icc P.vMin P.vMax, θa P Q δ F s < 1
  tilt : ∀ s ∈ Set.Icc P.vMin P.vMax,
    Real.arctan (Hhi P Q δ F s / Zlo P Q δ F s) ≤ Q.tiltMax
  rate : ∀ s ∈ Set.Icc P.vMin P.vMax, Ωb P Q δ F s ≤ Q.rateMax
  mix_lo : ∀ s ∈ Set.Icc P.vMin P.vMax,
    τrp P Q δ F s / (2 * Q.arm) + τyaw P Q δ F s / (4 * Q.kYaw) ≤ Q.mass * Clo P Q δ F s / 4
  mix_hi : ∀ s ∈ Set.Icc P.vMin P.vMax,
    Q.mass * Chi P Q δ F s / 4 + τrp P Q δ F s / (2 * Q.arm) + τyaw P Q δ F s / (4 * Q.kYaw)
      ≤ Q.fMotor
  miss_le : ∀ s ∈ Set.Icc P.vMin P.vMax, miss P Q C δ F s ≤ π / 2
  see : ∀ s ∈ Set.Icc P.vMin P.vMax, camOff P Q C δ F s + μ P δ F d ≤ C.halfFov
  hinge : ∀ s ∈ Set.Icc P.vMin P.vMax, hingeStep P Q δ F s ≤ δ * C.hingeRate

end VisionTracking

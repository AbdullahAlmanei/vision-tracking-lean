import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith

/-!
# The discrete-time pursuit-with-camera model

This file fixes the model that every result in the project is stated against.
It is mirrored, definition by definition, by `blueprint/src/chapters/model.tex`.

* Time is discrete with control (= camera frame) period `δ > 0`.
* Positions follow the Euler update `x (k+1) = x k + δ v k`.
* The **target** is a fixed-wing aircraft: speed in `[vMin, vMax]`, turn radius at
  least `turnRadius` in every direction, bounded along-track acceleration, bounded
  jerk, and climb/dive angle at most `climbMax`.
* The **drone** is a rigid-body quadrotor in "+" layout. Its state is position,
  velocity, an orthonormal right-handed body frame `(b₁, b₂, b₃)` (so roll, pitch and
  yaw are all represented), body angular rates `Ω`, the four motor thrusts and the
  camera hinge angle. Collective thrust acts along `b₃`; the motors' thrust
  differences produce roll and pitch torques through the arm length, and their
  reaction torques produce yaw. Rates evolve by Euler's rigid-body equation and the
  frame is advanced by an exact rotation (Rodrigues' formula).
* The **camera** sits on a one-axis pitch hinge about `b₂`: its boresight is
  `cos η · b₁ + sin η · b₃` with `η ∈ [hingeLo, hingeHi]`. A fixed camera is the
  case `hingeLo = hingeHi`.
* The target is **visible** in a frame when it is within detection range (its
  bounding box spans at least `minPx` pixels) and its centre lies in the
  inscribed field-of-view cone.
-/

open InnerProductGeometry
open scoped RealInnerProductSpace

namespace VisionTracking

/-- Physical space. Coordinates: `0, 1` horizontal, `2` vertical (up). -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The world "up" unit vector `e₃`. -/
noncomputable def up : E3 := EuclideanSpace.single 2 1

/-- The horizontal unit vector at heading `ψ`. -/
noncomputable def heading (ψ : ℝ) : E3 := !₂[Real.cos ψ, Real.sin ψ, 0]

/-- Euler position update with step `δ`: `x (k+1) = x k + δ v k`. With this
convention the velocity is recoverable from consecutive positions, which is what a
position-only observer needs. -/
def StepsWith (δ : ℝ) (x v : ℕ → E3) : Prop :=
  ∀ k, x (k + 1) = x k + δ • v k

/-! ## Target -/

/-- Parameters of the fixed-wing target. -/
structure TargetParams where
  /-- Minimum airspeed (the target cannot hover). -/
  vMin : ℝ
  /-- Maximum airspeed. -/
  vMax : ℝ
  /-- Minimum turn radius, in any direction. -/
  turnRadius : ℝ
  /-- Maximum along-track acceleration. -/
  aTan : ℝ
  /-- Maximum jerk: the acceleration changes by at most `δ · jerk` per step (a
  fixed-wing must roll to redirect its lift). -/
  jerk : ℝ
  /-- Maximum climb or dive angle. -/
  climbMax : ℝ
  /-- Maximum vertical acceleration (pull-up / push-over), typically much smaller than
  the turning acceleration. -/
  aVert : ℝ
  /-- Maximum snap: the jerk changes by at most `δ · snap` per step (control-surface
  rates are limited). -/
  snap : ℝ
  /-- Detection size: over all viewing directions, the minimum of the longer side
  of the target's projected bounding box. -/
  size : ℝ
  vMin_pos : 0 < vMin
  vMin_le_vMax : vMin ≤ vMax
  turnRadius_pos : 0 < turnRadius
  aTan_nonneg : 0 ≤ aTan
  jerk_nonneg : 0 ≤ jerk
  climbMax_nonneg : 0 ≤ climbMax
  climbMax_lt : climbMax < Real.pi / 2
  aVert_nonneg : 0 ≤ aVert
  snap_nonneg : 0 ≤ snap
  size_pos : 0 < size

/-- An admissible target trajectory. The velocity change over one step is split
into its component along the current velocity (bounded by `aTan`) and its
component normal to it (bounded by the curvature limit `‖v‖² / turnRadius`). -/
structure TargetTraj (P : TargetParams) (δ : ℝ) where
  p : ℕ → E3
  v : ℕ → E3
  steps : StepsWith δ p v
  speed_ge : ∀ k, P.vMin ≤ ‖v k‖
  speed_le : ∀ k, ‖v k‖ ≤ P.vMax
  tangential : ∀ k, abs ⟪v (k + 1) - v k, v k⟫ ≤ δ * P.aTan * ‖v k‖
  normal : ∀ k,
    ‖(v (k + 1) - v k) - (⟪v (k + 1) - v k, v k⟫ / ‖v k‖ ^ 2) • v k‖
      ≤ δ * ‖v k‖ ^ 2 / P.turnRadius
  jerk_le : ∀ k, ‖(v (k + 2) - v (k + 1)) - (v (k + 1) - v k)‖ ≤ δ ^ 2 * P.jerk
  climb_le : ∀ k, |⟪v k, up⟫| ≤ ‖v k‖ * Real.sin P.climbMax
  vert_le : ∀ k, |⟪v (k + 1) - v k, up⟫| ≤ δ * P.aVert
  snap_le : ∀ k, ‖v (k + 3) - 3 • v (k + 2) + 3 • v (k + 1) - v k‖ ≤ δ ^ 3 * P.snap

/-! ## Camera -/

/-- Parameters of the camera and its pitch hinge. -/
structure CameraParams where
  /-- Half-angle `α` of the field-of-view cone inscribed in the image rectangle. -/
  halfFov : ℝ
  /-- Full horizontal field of view `Φ` (radians), spread over `widthPx` pixels. -/
  fovH : ℝ
  /-- Horizontal resolution `W` in pixels. -/
  widthPx : ℝ
  /-- Pixels the bounding box's longer side must span for a detection (8). -/
  minPx : ℝ
  /-- Hinge range: `η = 0` looks along `b₁`, `η = π/2` along the thrust axis `b₃`,
  `η = -π/2` against it. -/
  hingeLo : ℝ
  hingeHi : ℝ
  /-- Maximum hinge rate (irrelevant when `hingeLo = hingeHi`). -/
  hingeRate : ℝ
  halfFov_pos : 0 < halfFov
  halfFov_lt : halfFov < Real.pi / 2
  fovH_pos : 0 < fovH
  widthPx_pos : 0 < widthPx
  minPx_pos : 0 < minPx
  minPx_lt : minPx * fovH < Real.pi * widthPx
  hingeLo_le : hingeLo ≤ hingeHi
  hingeLo_ge : -(Real.pi / 2) ≤ hingeLo
  hingeHi_le : hingeHi ≤ Real.pi / 2
  hingeRate_nonneg : 0 ≤ hingeRate

/-- Detection range: the largest distance at which a target of size `s` subtends
`minPx` pixels, `s / (2 tan(n Φ / 2W))` (≈ `s W / (n Φ)`). -/
noncomputable def CameraParams.detectRange (C : CameraParams) (s : ℝ) : ℝ :=
  s / (2 * Real.tan (C.minPx * C.fovH / (2 * C.widthPx)))

/-- The body forward axis `b₁`: the heading `ψ` projected onto the rotor plane
`b₃^⊥` and normalised. Well defined whenever `b₃` is not horizontal. -/
noncomputable def bodyForward (b₃ : E3) (ψ : ℝ) : E3 :=
  let w := heading ψ - ⟪heading ψ, b₃⟫ • b₃
  ‖w‖⁻¹ • w

/-- Camera boresight for thrust axis `b₃`, yaw `ψ` and hinge angle `η`. -/
noncomputable def camAxis (b₃ : E3) (ψ η : ℝ) : E3 :=
  Real.cos η • bodyForward b₃ ψ + Real.sin η • b₃

/-! ## Rigid-body quadrotor -/

/-- The cross product on `E3`. -/
noncomputable def cross (a b : E3) : E3 := WithLp.toLp 2 (crossProduct a.ofLp b.ofLp)

/-- Rodrigues rotation: rotate `v` by the angle `‖ω‖` about the axis `ω`. -/
noncomputable def rotate (ω v : E3) : E3 :=
  Real.cos ‖ω‖ • v + Real.sin ‖ω‖ • cross (‖ω‖⁻¹ • ω) v +
    ((1 - Real.cos ‖ω‖) * ⟪‖ω‖⁻¹ • ω, v⟫) • (‖ω‖⁻¹ • ω)

/-- Parameters of a rigid-body quadrotor in "+" layout: motor 0 on `+b₁`, motor 1 on
`+b₂`, motor 2 on `-b₁`, motor 3 on `-b₂`, with alternating spin directions. -/
structure QuadParams where
  /-- Gravitational acceleration. -/
  g : ℝ
  /-- Mass. -/
  mass : ℝ
  /-- Principal moments of inertia about `b₁, b₂, b₃`. -/
  Jx : ℝ
  Jy : ℝ
  Jz : ℝ
  /-- Arm length (rotor axis to centre of mass). -/
  arm : ℝ
  /-- Maximum thrust of one motor. -/
  fMotor : ℝ
  /-- Yaw reaction torque per unit motor thrust. -/
  kYaw : ℝ
  /-- Quadratic drag coefficient per unit mass: drag acceleration `c_D ‖v‖ v`. -/
  drag : ℝ
  /-- Flight-envelope limit on the tilt of `b₃` from vertical. -/
  tiltMax : ℝ
  /-- Flight-controller limit on the body rate `‖Ω‖`. -/
  rateMax : ℝ
  /-- Validity envelope of the drag model: speeds the model is used at. Results
  assume the step is fine enough that `δ c_D speedEnv ≤ 1/2`. -/
  speedEnv : ℝ
  g_pos : 0 < g
  mass_pos : 0 < mass
  Jx_pos : 0 < Jx
  Jy_pos : 0 < Jy
  Jz_pos : 0 < Jz
  arm_pos : 0 < arm
  kYaw_pos : 0 < kYaw
  /-- The quad can hover with margin. -/
  hover : mass * g < 4 * fMotor
  drag_pos : 0 < drag
  tiltMax_pos : 0 < tiltMax
  tiltMax_lt : tiltMax < Real.pi / 2
  rateMax_pos : 0 < rateMax
  speedEnv_pos : 0 < speedEnv

/-- Collective thrust of the four motors. -/
def totalThrust (f : Fin 4 → ℝ) : ℝ := f 0 + f 1 + f 2 + f 3

/-- Body-frame torque of the "+" layout: roll from motors 1/3, pitch from motors
2/0, yaw from the alternating reaction torques. -/
noncomputable def QuadParams.torque (Q : QuadParams) (f : Fin 4 → ℝ) : E3 :=
  !₂[Q.arm * (f 1 - f 3), Q.arm * (f 2 - f 0), Q.kYaw * (f 0 - f 1 + f 2 - f 3)]

/-- Angular momentum `J Ω` in body coordinates. -/
noncomputable def QuadParams.inertia (Q : QuadParams) (Ω : E3) : E3 :=
  !₂[Q.Jx * Ω.ofLp 0, Q.Jy * Ω.ofLp 1, Q.Jz * Ω.ofLp 2]

/-- `J⁻¹ τ` in body coordinates. -/
noncomputable def QuadParams.inertiaInv (Q : QuadParams) (τ : E3) : E3 :=
  !₂[τ.ofLp 0 / Q.Jx, τ.ofLp 1 / Q.Jy, τ.ofLp 2 / Q.Jz]

/-- The world-frame angular velocity of body rates `Ω` in the frame `(b₁, b₂, b₃)`. -/
noncomputable def worldRate (b₁ b₂ b₃ Ω : E3) : E3 :=
  Ω.ofLp 0 • b₁ + Ω.ofLp 1 • b₂ + Ω.ofLp 2 • b₃

/-- Camera boresight on a pitch hinge about `b₂`. -/
noncomputable def frameCam (b₁ b₃ : E3) (η : ℝ) : E3 :=
  Real.cos η • b₁ + Real.sin η • b₃

/-- An admissible quadrotor trajectory: full rigid-body dynamics with four bounded
motors, the flight envelope, and the camera hinge. -/
structure QuadTraj (Q : QuadParams) (C : CameraParams) (δ : ℝ) where
  x : ℕ → E3
  v : ℕ → E3
  b₁ : ℕ → E3
  b₂ : ℕ → E3
  b₃ : ℕ → E3
  /-- Body angular rates (components along `b₁, b₂, b₃`). -/
  Ω : ℕ → E3
  /-- Motor thrusts. -/
  f : ℕ → Fin 4 → ℝ
  /-- Hinge angle. -/
  η : ℕ → ℝ
  steps : StepsWith δ x v
  translational : ∀ k, v (k + 1) = v k + δ •
    ((totalThrust (f k) / Q.mass) • b₃ k - Q.g • up - (Q.drag * ‖v k‖) • v k)
  rotational : ∀ k, Ω (k + 1) =
    Ω k + δ • Q.inertiaInv (Q.torque (f k) - cross (Ω k) (Q.inertia (Ω k)))
  attitude : ∀ k,
    b₁ (k + 1) = rotate (δ • worldRate (b₁ k) (b₂ k) (b₃ k) (Ω k)) (b₁ k) ∧
    b₂ (k + 1) = rotate (δ • worldRate (b₁ k) (b₂ k) (b₃ k) (Ω k)) (b₂ k) ∧
    b₃ (k + 1) = rotate (δ • worldRate (b₁ k) (b₂ k) (b₃ k) (Ω k)) (b₃ k)
  b₁_unit : ∀ k, ‖b₁ k‖ = 1
  b₂_unit : ∀ k, ‖b₂ k‖ = 1
  b₁₂_orth : ∀ k, ⟪b₁ k, b₂ k⟫ = 0
  b₃_cross : ∀ k, b₃ k = cross (b₁ k) (b₂ k)
  motor_nonneg : ∀ k i, 0 ≤ f k i
  motor_le : ∀ k i, f k i ≤ Q.fMotor
  tilt_le : ∀ k, angle (b₃ k) up ≤ Q.tiltMax
  rate_le : ∀ k, ‖Ω k‖ ≤ Q.rateMax
  speed_le : ∀ k, ‖v k‖ ≤ Q.speedEnv
  hinge_ge : ∀ k, C.hingeLo ≤ η k
  hinge_le : ∀ k, η k ≤ C.hingeHi
  hinge_rate : ∀ k, abs (η (k + 1) - η k) ≤ δ * C.hingeRate

/-- The camera boresight of a quadrotor trajectory at step `k`. -/
noncomputable def QuadTraj.cam {Q : QuadParams} {C : CameraParams} {δ : ℝ}
    (d : QuadTraj Q C δ) (k : ℕ) : E3 :=
  frameCam (d.b₁ k) (d.b₃ k) (d.η k)

/-! ## Visibility -/

/-- The target at `p` is visible from a camera at `x` with boresight `c`. -/
def Visible (C : CameraParams) (s : ℝ) (x c p : E3) : Prop :=
  ‖p - x‖ ≤ C.detectRange s ∧ angle c (p - x) ≤ C.halfFov

/-- The drone keeps the target in view in every frame. -/
def KeepsInView (C : CameraParams) (s : ℝ) {Q : QuadParams} {δ : ℝ}
    {P : TargetParams} (d : QuadTraj Q C δ) (T : TargetTraj P δ) : Prop :=
  ∀ k, Visible C s (d.x k) (d.cam k) (T.p k)

/-! ## Strategies -/

/-- The drone's state at step `j`, as a tuple (for stating causality). -/
def QuadTraj.state {Q : QuadParams} {C : CameraParams} {δ : ℝ} (d : QuadTraj Q C δ)
    (j : ℕ) : E3 × E3 × E3 × E3 × E3 × E3 × ℝ :=
  (d.x j, d.v j, d.b₁ j, d.b₂ j, d.b₃ j, d.Ω j, d.η j)

/-- The target starts at position `p₀` with velocity `v₀` and acceleration `a₀`. -/
def TargetTraj.StartsAt {P : TargetParams} {δ : ℝ} (T : TargetTraj P δ)
    (p₀ v₀ a₀ : E3) : Prop :=
  T.p 0 = p₀ ∧ T.v 0 = v₀ ∧ T.v 1 = v₀ + δ • a₀

/-- The target starts in steady flight: its acceleration is constant over the first two
steps (zero initial jerk). -/
def TargetTraj.StartsSteady {P : TargetParams} {δ : ℝ} (T : TargetTraj P δ)
    (p₀ v₀ a₀ : E3) : Prop :=
  T.StartsAt p₀ v₀ a₀ ∧ T.v 2 = T.v 1 + δ • a₀

/-- A full-information strategy for targets with a known start `(p₀, v₀, a₀)`: the motor
commands at step `k`, and hence the state at step `k + 1`, depend on the target only
through steps `0, …, k`. -/
structure Strategy (P : TargetParams) (Q : QuadParams) (C : CameraParams) (δ : ℝ)
    (p₀ v₀ a₀ : E3) where
  play : (T : TargetTraj P δ) → T.StartsAt p₀ v₀ a₀ → QuadTraj Q C δ
  causal : ∀ (T T' : TargetTraj P δ) (hT : T.StartsAt p₀ v₀ a₀) (hT' : T'.StartsAt p₀ v₀ a₀)
    (k : ℕ), (∀ j ≤ k, T.p j = T'.p j ∧ T.v j = T'.v j) →
    (∀ j ≤ k + 1, (play T hT).state j = (play T' hT').state j) ∧
      ∀ j ≤ k, (play T hT).f j = (play T' hT').f j

/-- A position-only strategy: it sees the target only through its positions (which
bearing plus apparent size of a target of known size determine). -/
structure PosStrategy (P : TargetParams) (Q : QuadParams) (C : CameraParams) (δ : ℝ)
    (p₀ v₀ a₀ : E3) extends Strategy P Q C δ p₀ v₀ a₀ where
  pos_causal : ∀ (T T' : TargetTraj P δ) (hT : T.StartsAt p₀ v₀ a₀)
    (hT' : T'.StartsAt p₀ v₀ a₀) (k : ℕ), (∀ j ≤ k, T.p j = T'.p j) →
    (∀ j ≤ k + 1, (play T hT).state j = (play T' hT').state j) ∧
      ∀ j ≤ k, (play T hT).f j = (play T' hT').f j

/-- **Maintainable**: some position-only strategy keeps every admissible target with
the given start in view in every frame. -/
def Maintainable (P : TargetParams) (Q : QuadParams) (C : CameraParams) (δ : ℝ)
    (p₀ v₀ a₀ : E3) : Prop :=
  ∃ σ : PosStrategy P Q C δ p₀ v₀ a₀, ∀ (T : TargetTraj P δ) (hT : T.StartsAt p₀ v₀ a₀),
    KeepsInView C P.size (σ.play T hT) T

/-- Full-information version (used for impossibility results, which are then the
strongest form). -/
def MaintainableFullInfo (P : TargetParams) (Q : QuadParams) (C : CameraParams) (δ : ℝ)
    (p₀ v₀ a₀ : E3) : Prop :=
  ∃ σ : Strategy P Q C δ p₀ v₀ a₀, ∀ (T : TargetTraj P δ) (hT : T.StartsAt p₀ v₀ a₀),
    KeepsInView C P.size (σ.play T hT) T

theorem Maintainable.fullInfo {P : TargetParams} {Q : QuadParams} {C : CameraParams}
    {δ : ℝ} {p₀ v₀ a₀ : E3} (h : Maintainable P Q C δ p₀ v₀ a₀) :
    MaintainableFullInfo P Q C δ p₀ v₀ a₀ := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ.toStrategy, hσ⟩

end VisionTracking

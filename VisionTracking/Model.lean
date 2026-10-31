import Mathlib

/-!
# The discrete-time pursuit-with-camera model

This file fixes the model that every result in the project is stated against.
It is mirrored, definition by definition, by `blueprint/src/chapters/model.tex`.

* Time is discrete with control (= camera frame) period `δ > 0`; step `k` is time `k δ`.
* Positions follow the trapezoidal update `x (k+1) = x k + (δ/2)(v k + v (k+1))`,
  which is exact for an acceleration held constant over each step.
* The **target** is a fixed-wing aircraft: speed in a band `[vMin, vMax]`,
  turn radius at least `turnRadius` (a curvature bound in every direction, so climbs
  and dives obey it too), and bounded along-track acceleration.
* The **drone** is a quadrotor: its acceleration is `f b₃ − g e₃ − c_D ‖v‖ v`,
  with thrust `f ∈ [0, fMax]` along the body axis `b₃`. Tilt, tilt rate, yaw rate,
  hinge angle and hinge rate are all bounded.
* The **camera** sits on a one-axis pitch hinge: its boresight is
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

/-- Trapezoidal position update with step `δ`: exact for piecewise-constant
acceleration. -/
def StepsWith (δ : ℝ) (x v : ℕ → E3) : Prop :=
  ∀ k, x (k + 1) = x k + (δ / 2) • (v k + v (k + 1))

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
  /-- Detection size: over all viewing directions, the minimum of the longer side
  of the target's projected bounding box. -/
  size : ℝ
  vMin_pos : 0 < vMin
  vMin_le_vMax : vMin ≤ vMax
  turnRadius_pos : 0 < turnRadius
  aTan_nonneg : 0 ≤ aTan
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

/-! ## Drone -/

/-- Parameters of the quadrotor. Accelerations are per unit mass. -/
structure DroneParams where
  /-- Gravitational acceleration. -/
  g : ℝ
  /-- Maximum thrust per unit mass. -/
  fMax : ℝ
  /-- Quadratic drag coefficient per unit mass: drag acceleration `c_D ‖v‖ v`. -/
  drag : ℝ
  /-- Speed cap (flight-controller limit; at most the drag-limited speed). -/
  vMax : ℝ
  /-- Maximum tilt of the thrust axis from vertical. -/
  tiltMax : ℝ
  /-- Maximum rate of change of the thrust axis direction. -/
  tiltRate : ℝ
  /-- Maximum yaw rate. -/
  yawRate : ℝ
  g_pos : 0 < g
  fMax_gt_g : g < fMax
  drag_nonneg : 0 ≤ drag
  vMax_pos : 0 < vMax
  tiltMax_pos : 0 < tiltMax
  tiltMax_lt : tiltMax < Real.pi / 2
  tiltRate_pos : 0 < tiltRate
  yawRate_pos : 0 < yawRate

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

/-- An admissible drone trajectory: dynamics plus every actuator limit. -/
structure DroneTraj (D : DroneParams) (C : CameraParams) (δ : ℝ) where
  x : ℕ → E3
  v : ℕ → E3
  /-- Thrust axis (unit). -/
  b₃ : ℕ → E3
  /-- Thrust per unit mass. -/
  f : ℕ → ℝ
  /-- Yaw (unwrapped). -/
  ψ : ℕ → ℝ
  /-- Hinge angle. -/
  η : ℕ → ℝ
  steps : StepsWith δ x v
  dynamics : ∀ k, v (k + 1) =
    v k + δ • (f k • b₃ k - D.g • up - (D.drag * ‖v k‖) • v k)
  speed_le : ∀ k, ‖v k‖ ≤ D.vMax
  b₃_unit : ∀ k, ‖b₃ k‖ = 1
  thrust_nonneg : ∀ k, 0 ≤ f k
  thrust_le : ∀ k, f k ≤ D.fMax
  tilt_le : ∀ k, angle (b₃ k) up ≤ D.tiltMax
  tilt_rate : ∀ k, angle (b₃ (k + 1)) (b₃ k) ≤ δ * D.tiltRate
  yaw_rate : ∀ k, abs (ψ (k + 1) - ψ k) ≤ δ * D.yawRate
  hinge_ge : ∀ k, C.hingeLo ≤ η k
  hinge_le : ∀ k, η k ≤ C.hingeHi
  hinge_rate : ∀ k, abs (η (k + 1) - η k) ≤ δ * C.hingeRate

/-- The camera boresight of a drone trajectory at step `k`. -/
noncomputable def DroneTraj.cam {D : DroneParams} {C : CameraParams} {δ : ℝ}
    (d : DroneTraj D C δ) (k : ℕ) : E3 :=
  camAxis (d.b₃ k) (d.ψ k) (d.η k)

/-! ## Visibility -/

/-- The target at `p` is visible from a camera at `x` with boresight `c`. -/
def Visible (C : CameraParams) (s : ℝ) (x c p : E3) : Prop :=
  ‖p - x‖ ≤ C.detectRange s ∧ angle c (p - x) ≤ C.halfFov

/-- The drone keeps the target in view in every frame. -/
def KeepsInView (C : CameraParams) (s : ℝ) {D : DroneParams} {δ : ℝ}
    {P : TargetParams} (d : DroneTraj D C δ) (T : TargetTraj P δ) : Prop :=
  ∀ k, Visible C s (d.x k) (d.cam k) (T.p k)

/-! ## Strategies -/

/-- A full-information pursuit strategy: the drone trajectory may depend on the
target trajectory, but only causally (its state at step `k` depends on the target
only up to step `k`). Observation-limited strategies (bearing and apparent size
only) are a subclass, so impossibility results proved here are the strongest form. -/
structure Strategy (P : TargetParams) (D : DroneParams) (C : CameraParams) (δ : ℝ) where
  play : TargetTraj P δ → DroneTraj D C δ
  causal : ∀ (T T' : TargetTraj P δ) (k : ℕ),
    (∀ j ≤ k, T.p j = T'.p j ∧ T.v j = T'.v j) →
    ∀ j ≤ k, (play T).x j = (play T').x j ∧ (play T).v j = (play T').v j ∧
      (play T).b₃ j = (play T').b₃ j ∧ (play T).ψ j = (play T').ψ j ∧
      (play T).η j = (play T').η j

/-- Tracking is maintainable from target start `(p₀, v₀)`: some strategy keeps
every admissible target with that start in view forever. -/
def Maintainable (P : TargetParams) (D : DroneParams) (C : CameraParams) (δ : ℝ)
    (p₀ v₀ : E3) : Prop :=
  ∃ σ : Strategy P D C δ, ∀ T : TargetTraj P δ, T.p 0 = p₀ → T.v 0 = v₀ →
    KeepsInView C P.size (σ.play T) T

end VisionTracking

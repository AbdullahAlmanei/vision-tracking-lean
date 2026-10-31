# vision-tracking-lean

A Lean 4 + Blueprint project on the limits of camera-constrained quadrotor
pursuit. A quadrotor carries one camera on a one-axis pitch hinge and must keep
an airborne (fixed-wing) target in view in every camera frame, using only
bearing and apparent size. Every drone, camera and target quantity is a
parameter. The goal ("P3") is one master inequality that decides whether
tracking can be maintained: sufficient as stated, necessary up to an explicit
gap that vanishes as the control period shrinks.

See the blueprint (`blueprint/src/`) for the model, the proved results and the
roadmap.

## Status

| Piece | Status |
|---|---|
| Discrete-time model (`VisionTracking/Model.lean`) | defined |
| Speed impossibility: `D.vMax < P.vMax` ⇒ not maintainable (`VisionTracking/SpeedBound.lean`) | proved, `sorry`-free |
| Pointing reduction: camera can see `u` ⇔ rotor-plane elevation of `u` ∈ [η_lo − α, η_hi + α] (`VisionTracking/Pointing.lean`) | proved, `sorry`-free |
| Overhead geometry: hinge range needed for a tilt band; fixed mount works ⇔ band width ≤ 2α (`VisionTracking/Overhead.lean`) | proved, `sorry`-free |
| Tilt band from target motion, formation hold, converse bounds, master inequality | stated in the blueprint roadmap |

## Building

```
lake build
leanblueprint web          # needs plastex / leanblueprint in PATH
leanblueprint checkdecls
```

Toolchain and Mathlib are pinned to the same revisions as `two-control-lean`.

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

Every statement is about a full rigid-body quadrotor: a right-handed orthonormal
body frame (roll, pitch, yaw), body rates driven by Euler's equation, four bounded
motors in "+" layout producing thrust and torques, Rodrigues attitude updates,
quadratic drag, and a camera on a one-axis pitch hinge.

| Result | File | Status |
|---|---|---|
| Directional speed limits from motors, tilt envelope and drag (dive limit √(g/c_D), level and climb limits); a faster target along that direction escapes every strategy | `DirectionalSpeed.lean` | proved |
| Pointing reduction: the camera sees `u` iff the rotor-plane elevation of `u` is in `[η_lo − α, η_hi + α]`; holds in every quad state | `Pointing.lean`, `Frame.lean` | proved |
| Overhead geometry: hinge range needed for a tilt band; a fixed mount works iff the band is at most `2α` wide | `Overhead.lean` | proved |
| Steady flight forces the tilt `arctan(c_D v²/g)`; steady-chase window `η_lo − α ≤ θ(v) + el ≤ η_hi + α`; trackable speed depends on the altitude offset | `SteadyChase.lean` | proved |
| Steady formation exists iff the window holds (explicit four-motor construction) | `SteadyFormation.lean` | proved |
| Motor allocation (explicit inverse mixer); Rodrigues preserves frames and turns vectors by at most `‖ω‖` | `Motors.lean`, `Rotation.lean` | proved |
| Axis-angle between frames | `Plan.lean` | stated, `sorry` |
| Manoeuvring-target sufficiency (torque-limited smoothing), master inequality | blueprint roadmap | planned |

The single `sorry` is `exists_rotate_frame` in `Plan.lean`. Everything else depends
only on `propext`, `Classical.choice` and `Quot.sound`.

## Building

```
lake build
leanblueprint web          # needs plastex / leanblueprint in PATH
leanblueprint checkdecls
```

Toolchain and Mathlib are pinned to the same revisions as `two-control-lean`.

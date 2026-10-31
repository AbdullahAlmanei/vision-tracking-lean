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
| **Master inequality, sufficient side**: under `MasterIneq` (explicit budget), a position-only strategy flying the overhead formation as a valid rigid-body quad keeps every target with the given start in view | `Master.lean`, `OverheadPlan.lean`, `Budget.lean` | proved |
| **Necessary side (partial)**: maintainability forces `vMax ≤ dirSpeed u` in every admissible direction; the steady-chase window in steady flight. Thrust/tilt/hinge/mixer conditions have no proved necessary counterpart yet | `Master.lean`, `DirectionalSpeed.lean`, `SteadyChase.lean` | proved |
| Planner error terms vanish as `δ → 0` (but for a fixed filter the torque budget grows like `1/δ`) | `Master.lean` | proved |
| **Master inequality v2 (yaw-free down camera)**: sharp planner constants, vertical manoeuvre limit, parallel-transported frame; `master_sufficient2`. Satisfiable (by `scripts/budget_v2.py`, an exact mirror of `Budget2.lean`) for targets up to 25–30 m/s with jerk ≤ 2 m/s³ | `Master2.lean`, `DownPlan.lean`, `Budget2.lean`, `PlannerSharp.lean`, `SharpNorm.lean`, `Transport.lean`, `RotPlan.lean` | proved |
| **Caveat (v1)**: with current constants `MasterIneq` is not satisfiable for the reference target (`scripts/budget_v1.py`); needs a fixed-time-window filter family, sharper constants and a yaw-free camera variant | blueprint roadmap | open |
| Steady formation iff window (explicit four-motor construction) | `SteadyFormation.lean` | proved |
| Lifting kinematic plans to rigid-body trajectories; axis-angle; body-rate and torque bounds from frame differences | `Lifting.lean`, `AxisAngle.lean`, `FrameRate.lean`, `RateBound.lean` | proved |
| FIR formation planner: error `H₃δ³j`, smoothness `TV·δj`, causality | `Planner.lean` | proved |
| Pointing reduction, overhead hinge range, fixed mount | `Pointing.lean`, `Overhead.lean` | proved |
| Smoothing family `h^(N)`, weaving-drone bound, paper numbers | — | planned |

There are no `sorry`s. Every headline theorem depends only on `propext`,
`Classical.choice` and `Quot.sound` (checked by `scripts/axcheck.sh`).

## Building

```
lake build
leanblueprint web          # needs plastex / leanblueprint in PATH
leanblueprint checkdecls
```

Toolchain and Mathlib are pinned to the same revisions as `two-control-lean`.

# P3: the necessary side, and the gap to `MasterIneq3`

Date: 2026-11-01. Information model: **full information**, decided by the user. Necessity
results say that no drone trajectory keeps the target in view, even one planned with
knowledge of the target's whole future. That is stronger than ruling out every strategy.

## Goal

Two inequalities on the same parameters: the camera and hinge, the quad (thrust, drag,
inertia, arm, tilt), the frame rate, and the target (speed band, turn radius, jerk, snap,
climb, vertical acceleration).

- `MasterIneq3 ⇒ MaintainableSteady`: proved (`master_sufficient3`).
- `MaintainableSteady from every steady start ⇒ NecIneq3`: the necessity theorem
  (`master_necessary3`). Its contrapositive is: if `NecIneq3` fails, then some admissible,
  steadily starting target escapes every drone trajectory.
- **The gap**: for each condition of `MasterIneq3`, its necessary counterpart in `NecIneq3`,
  stated explicitly and evaluated numerically (`scripts/gap_v3.py`).

The target class must match on both sides. Necessity uses targets that start in steady
flight (`StartsSteady`), the class `master_sufficient3` covers.

## What is already known

| Sufficient condition (`MasterIneq3`) | Necessary counterpart | Status |
|---|---|---|
| speed, plus Zlo > 0 (dives) | directional speed limit `vMax ≤ dirSpeed u` in every admissible direction u, including dives and climbs (motors, tilt envelope, drag) | proved for one start (`not_maintainable_of_dirSpeed_lt`); needs the steady-class and no-trajectory form |
| mix_hi (thrust in turns) | sustained-turn thrust: staying within range D of a target circling at radius R and speed v needs `maxAcc ≥ √(g² + (c v_eff²)²)` with `v_eff = v (1 - D/R)^{3/2} / (1 + D/R)` (angular momentum averaged over a revolution) | to do (N1) |
| see / camOff / hinge (camera geometry) | yaw-free look-down tilt bound `tilt_ge_of_visible` | proved, but not binding for the top camera: the visible cone around b₃ spans about 0–120°, so the upper hemisphere is always reachable |
| mix_lo, rate (torque, body rates) | none expected universally | see "Torque" below |

### Torque: why its necessary counterpart is weak

A target maneuver at frequency f with jerk J moves the target by about J/(2πf)³. With a
standoff of 100 m, the drone does not have to follow that motion at all: it can let the
relative position drift inside the view cone. So no universal torque lower bound of the
kind `mix_lo` encodes is expected. The binding sufficient condition comes from the *design
choice* of copying the target's acceleration exactly. Closing that part of the gap is
therefore a sufficiency task (Phase C), not a necessity task.

## Work items

**N0. Directional speed wall, steady class, no-trajectory form.**
- `no_traj_keeps_of_dirSpeed_lt`: if `dirSpeed u < vMax`, no `QuadTraj` keeps
  `straightTarget u` in view.
- Corollaries: `¬ MaintainableSteady p₀ (vMax • u) 0`, and the `NecIneq3` speed component.

**N1. Sustained-turn thrust.**
- A circling target (discrete rotation of the velocity), admissible when
  `v³/R² ≤ jerk`, `v⁴/R³ ≤ snap`, and `δ v³/(2R²) ≤ aTan`.
- Averaging the angular momentum about the centre over N steps gives
  `(1/N) Σ r ⟪T, θ̂⟫ ≈ c (1/N) Σ r ‖v‖ v_θ`.
- Jensen and the bound r ∈ [R-D, R+D] give the lower bound on mean thrust. The bound on max
  thrust follows from mean ≤ max.

**N2. `NecIneq3` and `master_necessary3`.**
- `NecIneq3` is the conjunction of the N0 directions, the N1 turn, and the fine-step
  condition.
- Also a bracket theorem `p3_bracket`: `MasterIneq3 ⇒ MaintainableSteady` and
  `MaintainableSteady (all steady starts) ⇒ NecIneq3`.

**N3. `scripts/gap_v3.py`.**
- For the reference quad and target, report the largest target speed allowed by each side,
  the turn thrust margin, and which `MasterIneq3` condition binds where `NecIneq3` still
  holds.
- Expected result: necessity allows targets of roughly 80+ m/s (motor/drag wall), while
  sufficiency stops at 55 m/s for jerk ≤ 3. The gap is dominated by torque.

**C (follow-up, sufficiency). Loose following.** A strategy that tracks a low-pass-filtered
formation and spends part of the field of view on relative drift, instead of copying the
acceleration. This targets the torque gap directly. It gets its own plan once the gap
numbers are in.

## Order

N0 → N2 (with N0 only) → N3 → N1 → N2 updated → C.

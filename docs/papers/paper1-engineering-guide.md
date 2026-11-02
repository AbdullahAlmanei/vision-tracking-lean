# Buy Headroom, Not Cleverness

**An engineering guide to quadrotor pursuit of fast fixed-wing aircraft**

*Draft, 2026-11-02. Every bound quoted as "proved" or "certified" is machine-checked in
Lean 4 (repository `AbdullahAlmanei/vision-tracking-lean`, no `sorry`, standard axioms
only). Every number is reproducible with the scripts named in the appendix.*

## Abstract

A quadrotor has to keep a fast radio-controlled fixed-wing aircraft (3.5 m long, 2.5 m span,
up to 55 m/s, turning down to a 350 m radius) inside the image of one camera in every
frame. We give conditions that are proved sufficient for this, and conditions that are
proved necessary for any strategy, even one that knows the target's future. We then sweep
the design parameters through those bounds.

The results reduce to three design rules:
1. **Top speed is set by thrust and air.** Thrust-to-weight is the strongest lever. The
   proved speed wall scales as (F_max² / (k_n·c))^¼.
2. **Agility is set by yaw authority when total thrust is low.** The worst case is a
   35 m/s dive, not a 55 m/s dash. Thrust-to-weight does not help there; yaw authority and
   low inertia do.
3. **The camera is solved by geometry.** Fly underneath, with a rear-facing top camera on a
   30–70° hinge, or a fixed mount with a 120° lens.

Strategies we tested as alternatives to plain copying either lost or needed physically
impossible torque: looser formations, smoothing planners, capped trackers, winged frames
and weaving. For the baseline 1.5 kg vehicle the certified envelope reaches 52–53 m/s,
against a proved physical wall of 57.7 m/s.

---

## 1. The answer on one page

**Baseline vehicle:**
- 1.5 kg, thrust-to-weight 6, plus layout, 18 cm arm, yaw coefficient 0.02;
- inertia (0.012, 0.012, 0.02) kg·m², parasitic drag c = 0.008 m⁻¹;
- rotor-disc normal-force coefficient k_n = 0.01 m⁻¹ (about 0.02 m² of effective normal
  area);
- rear-facing top camera on a 30–70° hinge, 120° field of view.

**Baseline target:**
- 20 m/s up to v_max, turn radius 350 m;
- along-track acceleration 2 m/s², vertical acceleration 1.5 m/s²;
- snap 15 m/s⁴, jerk 1–5 m/s³, climbs and dives up to ±5° or ±10°.

| Question | Answer for the baseline |
|---|---|
| Fastest target any strategy could follow (proved wall) | **57.7 m/s** |
| Fastest target our formation is proved to follow, ±5° dives, jerk ≤ 5 | **52.1 m/s** |
| Same, ±10° dives, jerk ≤ 3 | **52.1 m/s** |
| Same, ±10° dives, jerk 5 | **33.4 m/s** (yaw-limited, see §5) |
| …with yaw coefficient 0.03 or 30% less inertia | **52.1 m/s** |
| Recommended package (§8): thrust/weight 7, k_n 0.005, yaw 0.03, inertia −30% | wall 73.9; certified 68.1 (±5°) and 58.4 (±10°) at jerk 5 |
| Binding constraint at top speed | top motor saturating (thrust plus steering) |
| Binding constraint in dives | yaw torque when total thrust is low |
| Is the camera ever binding? | No, with a 120° lens or a 30–70° hinge |

**Spend in this order:**
1. **Thrust-to-weight.** About +5 m/s of wall and certified speed per unit of
   thrust-to-weight.
2. **Rotor-disc and frame normal area (k_n).** Halving it buys about 10 m/s.
3. **Yaw authority, and low yaw inertia.** This lifts the ±10°, jerk-5 dive case from 33
   to 52 m/s.
4. **Camera:** a hinge, or a lens of at least 120°.

Do not spend on a longer arm, a cleaner airframe (it hurts dives), wings, or a cleverer
planner.

## 2. How to read the numbers

**Two kinds of bound:**
- **Proved necessary (the wall).** If the target's top speed exceeds it, a straight, level
  target escapes *every* drone trajectory, even one planned with full knowledge of the
  target's future. This is `NecPower` / `master_necessary_power` (rotor-disc model) and
  `NecIneq3` / `master_necessary3` (isotropic model).
- **Proved sufficient (certified).** If `MasterIneq3` holds, a concrete position-only
  strategy keeps every admissible target that starts in steady flight in view in every
  frame. That is `master_sufficient3`. The certified v_max is the largest value for which
  the inequality holds, found by bisection over the exact mirror of the Lean budget
  (`scripts/budget_v3.py`).

**What the model includes:**
- a full rigid-body quadrotor in discrete time (δ = 1/240 s): four bounded motors, mixer,
  Euler's equation, exact rotations, tilt, body-rate and speed limits;
- parasitic drag c‖v‖v, and a rotor-disc normal force −k_n‖v‖⟪v, b₃⟫ b₃ with centre of
  pressure at the centre of mass;
- a camera on a one-axis hinge with a rate limit, and visibility meaning within detection
  range and inside the field of view.

**What the model leaves out:**
- rotor thrust that depends on airspeed;
- aerodynamic moments;
- wind;
- the ground;
- sensor noise.

Read every number as "under this model". Section 9 lists what to measure to make them
yours.

## 3. Geometry: approach from below, look back and up

### 3.1 Why underneath

Fast flight tilts the quadrotor hard: about 50° of pitch at 35 m/s and about 70–80° at
55 m/s. That tilt decides where a body-mounted camera can point.

- **Belly camera, looking down from above.** It is capped near 30 m/s in our earlier
  version: at speed the thrust axis tilts so far that the target leaves the field of view.
- **Looking down from above is also a losing position on its own.** A drone that sits
  higher than D·sin e*(v) above the target (D = detection range, e* = the depression
  angle steady flight allows) must pitch beyond its drag balance to look down. It is then
  pushed forward, overtakes, and loses the target. `QuadTraj.forced_loss_time` gives an
  explicit time.
  - In a prototype with a 382 m range and a 90° lens: about 17 s at 20 m/s and 300 m above;
    about 53 s at 30 m/s.
  - Above 40 m/s the drag balance itself provides the downward look.
- **Underneath, with a top camera.** Pitching nose-down for speed rotates a rear-facing
  top camera *up and over*. Speed helps this camera.

### 3.2 Rear-facing, not forward-facing

On a nose-down airframe a forward-facing top camera points at elevation η − p, where p is
the pitch. At speed that is at or below 0: it cannot look up. A rear-facing camera points
at p + η measured from the rear horizon, so it reaches straight up at speed. **Mount the
camera on the rear face of a cone-shaped head and hinge it about the pitch axis.**

### 3.3 Hinge or wide lens

With the yaw locked to the target's sideways direction, the camera's off-target angle is
the bank angle plus the hinge's miss. Bank stays at or below 38° and the offset at or below
40° across the envelope. Certified v_max, isotropic model, ±5° dives, jerk 3:

| Camera | 120° lens | 90° lens |
|---|---|---|
| Hinge 30–70° | 69.9 m/s | 69.9 m/s |
| Hinge 20–80° | 69.9 | 69.9 |
| Fixed at 50° | 69.9 | **50.1** |
| Fixed at 60° | — | **34.6** |

**Rule:** with a ≥120° lens a fixed mount near 50° is enough. With a 90° lens use a
hinge of at least 30–70°. Pitch sweeps about 80° across the 20–55 m/s band, and only the
hinge or the extra field of view absorbs it.

### 3.4 Offset and ground clearance

The formation offset (100 m below in our runs) barely matters for the bounds; 60–150 m
behave alike. It does set the ground clearance: the target must fly at least the offset
plus a safety margin above ground. Plan for 60–100 m.

## 4. Top speed: thrust and air

### 4.1 The physics

The air pushes on the rotor plane with acceleration −k_n‖v‖⟪v, b₃⟫ b₃. At speed the rotor
disc faces the wind (about 68° of tilt at 55 m/s), so this term is first-order, as large
as the thrust needed against parasitic drag.

The power the motors can put into the flight path is therefore capped at
min(F_max‖v‖, F_max²/(4k_n‖v‖)). Parasitic drag takes c‖v‖³. Energy balance, together
with the fact that the drone must stay within camera range of the target, gives the wall
(`no_traj_keeps_of_power`). Its leading-order scaling is

  **V_wall ≈ (F_max² / (4·k_n·c))^¼.**

### 4.2 Sweeps (proved wall / certified v_max, ±5° dives, jerk ≤ 5)

| Lever | Values | Wall (m/s) | Certified (m/s) |
|---|---|---|---|
| Thrust/weight | 4 / 5 / 6 / 7 / 8 | 47.1 / 52.6 / 57.7 / 62.3 / 66.7 | 37.6 / 46.2 / 52.1 / 57.3 / 61.9 |
| k_n (m⁻¹) | 0 / 0.005 / 0.01 / 0.02 | 84.5 / 68.4 / 57.7 / 48.7 | 69.5 / 61.6 / 52.1 / 40.8 |
| Drag c (m⁻¹) | 0.006 / 0.008 / 0.010 | 62.0 / 57.7 / 54.5 | 39.3 / 52.1 / 50.1 |

The scaling law holds closely across the sweeps:
- doubling F_max multiplies the wall by 1.42 (√2 predicted);
- quadrupling k_n multiplies it by 0.71 (4^−¼ = 0.707 predicted);
- c from 0.006 to 0.010 multiplies it by 0.88 (0.88 predicted).

The certified envelope tracks the wall at about 90%.

### 4.3 How tight the wall is

- **The 57.7 m/s wall is physical, not slack.** Steady straight, level flight at full
  collective reaches 57.3 m/s. The 0.4 m/s difference is the energy gain of the 240 Hz
  Euler step.
- **Weaving does not beat steady flight on a real quadrotor.** A point mass that banks
  left and right fast can beat steady flight: over-thrusting sideways tilts the disc off
  the wind and cuts its drag (47.8 vs 47.0 m/s at k_n = 0.02). On a rigid body those flips
  need motor thrusts of −34 to +78 N against a 22 N limit, just when the collective is
  already at maximum. Every weave within the limits was slower than steady flight
  (`scripts/explore/weave.py`).

### 4.4 Rules

- **Thrust-to-weight first.** It is the only lever that raises both the wall and the
  certified envelope by about 5 m/s per unit.
- **Minimise the area the rotor plane presents to the wind**: small discs relative to
  thrust, and a thin frame in the disc plane. k_n is worth measuring (§9).
- **Do not chase parasitic drag.** Lower c raises the wall weakly (c^−¼) and costs agility
  in dives (§5.3).
- **Keep a motor-thrust reserve at top speed.** The top motor saturates first: total thrust
  for speed plus differential thrust for steering. The certified envelope ends where that
  reserve runs out.

## 5. Agility: the 35 m/s dive

### 5.1 Why the middle speed is the worst

A quadrotor steers by tilting, and tilts with differential motor thrust. The weakest motor
cannot go below zero, so torque authority scales with *total* thrust.

In a dive, gravity and drag both point along the path, so the motors need little total
thrust. At 35 m/s in a 10° dive the minimum collective falls to about 7 m/s², below hover.
At the same speed, a change in the target's acceleration (jerk) swings the thrust direction
fastest, because the collective is small.

| 10° dive, base quad, jerk 5 | 20 m/s | 35 m/s | 55 m/s |
|---|---|---|---|
| Torque available per motor | 2.8 N | **2.4 N** | 7.6 N |
| Torque needed per motor | 1.5 N | **6.1 N** | 1.5 N |

At 55 m/s drag rescues the drone: about 24 m/s² of drag means a large collective and small
attitude swings.

### 5.2 Sweeps (certified v_max, ±10° dives, jerk 5)

| Lever | Values | Certified (m/s) |
|---|---|---|
| Yaw coefficient | 0.015 / 0.02 / 0.03 | 30.9 / 33.4 / **52.1** |
| Inertia scale | 0.7 / 1.0 / 1.4 | **52.1** / 33.4 / 30.1 |
| Arm length | 0.15 / 0.18 / 0.22 m | 33.2 / 33.4 / 33.5 |
| Thrust/weight | 4 → 8 | 33.4 at every value |

**Yaw torque binds, not roll or pitch.** The frame is locked to the target's sideways
direction, so a change in the thrust axis forces a yaw acceleration about the thrust axis
in proportion to the bank.

The remedies, in order:
1. a larger yaw reaction coefficient (propellers and motors with more reaction torque per
   newton, or canted motors);
2. lower yaw inertia (mass close to the centre);
3. a longer arm, which does nothing here because it helps roll and pitch only.

Extra thrust does not help either, because the problem is low *minimum* collective, not
low maximum.

### 5.3 The drag paradox

A cleaner airframe dives worse. At c = 0.006 the ±5° jerk-5 envelope drops from 52.1 to
39.3 m/s, because less drag means even less collective in a dive. Drag is the quadrotor's
air brake, and in pursuit the air brake is what keeps torque authority alive.

### 5.4 Wings make it worse

We prototyped a winged quadrotor: cambered arms giving lift along the camera direction,
and symmetric sections on the other axis.
- Lift unloads the motors. In a 35 m/s dive the minimum motor thrust falls to about 0, and
  the available torque falls to 0.01–0.28 N against a need of 0.52 N.
- The sensitivity of bank angle to sideways acceleration stays at about 1/g (5.9° per
  m/s²) for every airframe.

Wings would need control surfaces, and then the vehicle is no longer a quadrotor. **Do not
add lifting surfaces to a pursuit quadrotor.**

## 6. Strategy: copy exactly, from below

The certified strategy:
- **Planner:** a sparse 3-tap filter, exact for constant acceleration, that sees target
  positions with a 4-frame delay at 240 Hz.
- **Formation:** the drone flies the filtered target path offset straight down.
- **Attitude:** the thrust axis follows the planned acceleration, and the yaw is locked to
  the target's sideways direction.
- **Camera:** the hinge points straight up, clamped to its range.

We tested five alternatives. None improved on it.

| Alternative | What happened |
|---|---|
| Smoothing or lag-compensating linear planners | Extrapolating through a 4-frame delay forces filter gain Σ\|h\| ≳ 2, so planned jerk and snap never drop below the target's own |
| Capped (jerk-limited) nonlinear tracker | Against adversarial targets: lags of 39–325 m and 13–35 m/s; the target reverses just as the tracker catches up |
| Loose yaw, averaged formation, looser offsets | Torque saved is paid back in bank, thrust margin or lag |
| Weaving to reduce rotor-disc drag | Needs −34 to +78 N motors (§4.3) |
| Winged frame | Motors go idle in dives (§5.4) |

There is also a negative result on the proof side: no *torque* requirement of practical
size can be forced on the drone. With 570 m of detection range and a 120° lens, a drone may
respond over 7–30 s, which forces only 0.002–0.007 rad/s of body rate. The agility limits
come from the tight formation, not from physics. They could only be relaxed by a formation
that spends range and field of view as slack. We did not find one that pays off.

**Rule:** invest in hardware headroom and a clean, high-rate planner (240 Hz, small fixed
delay). Do not invest in clever trajectory shaping.

## 7. Rules of engagement

1. **Take position below and behind**, at 60–100 m, before the target reaches top speed.
2. **Expect the hardest moment at mid speed in a dive**, not at top speed. If the target
   dives at 30–40 m/s while rolling into a turn, that is where the margin goes.
3. **Targets that escape any quadrotor:**
   - sustained level flight above the wall (57.7 m/s for the baseline);
   - in the isotropic model, sinking straight down faster than the drone's own terminal
     fall speed √(g/c) (35 m/s at c = 0.008).
   No strategy recovers either.
4. **Never trail from above** at more than D·sin e*(v) of height. You will be forced past
   the target.
5. **Planner rate is a design input.** The proved budgets use 120–480 Hz with a 4-frame
   delay. Slower loops scale the frame-to-frame terms up.

## 8. Design checklist

| # | Item | Target for a 55 m/s fixed-wing | Why |
|---|---|---|---|
| 1 | Thrust-to-weight | ≥ 7 (≥ 6 with low k_n) | Wall and certified speed, about +5 m/s per unit |
| 2 | Rotor-plane normal area | k_n ≤ 0.005 m⁻¹ (≈ 0.01 m² per 1.5 kg) | Wall ∝ k_n^−¼; k_n 0.01 → 0.005 gives about +10 m/s |
| 3 | Yaw authority | yaw coefficient ≥ 0.03 m, or canted motors | ±10° dive cases go from 33 to 52 m/s |
| 4 | Yaw inertia | ≤ 0.014 kg·m² at 1.5 kg | Same lever as item 3 |
| 5 | Camera | top, rear-facing, hinge 30–70°, or fixed at about 50° with ≥ 120° lens | Camera never binds |
| 6 | Planner | 240 Hz, 4-frame delay, quadratic-exact 3-tap filter | Certified configuration |
| 7 | Motor reserve at top speed | ≥ 1–2 m/s² of collective kept for steering | Top-motor saturation ends the envelope |
| 8 | Parasitic drag | do not minimise below c ≈ 0.008 m⁻¹ | Drag keeps collective, and torque, alive in dives |
| 9 | Lifting surfaces | none | They idle the motors in dives |
| 10 | Tilt limit | ≥ 85° | Binds above about 59 m/s in 10° dives |

**The recommended package, verified.** Thrust-to-weight 7, k_n = 0.005, yaw coefficient
0.03 and 30% less inertia give:

| | ±5° dives | ±10° dives |
|---|---|---|
| Proved wall | 73.9 m/s | 73.9 m/s |
| Certified, jerk ≤ 3 | 68.2 | 58.6 |
| Certified, jerk ≤ 5 | 68.1 | 58.4 |

So a 55 m/s target is covered with margin in every case.

**Levers interact.** Without the inertia cut the ±10°/jerk-5 case drops back to 35.5 m/s.
Lowering k_n also lowers the collective in dives: the drag paradox of §5.3 applies to the
rotor disc too. Always re-run the sweep for the full package, not lever by lever.

Above about 59 m/s in 10° dives the 85° tilt limit binds. A higher tilt limit is the next
lever for steep, fast dives.

## 9. What to measure before trusting these numbers

| Quantity | How | Why it matters |
|---|---|---|
| k_n, c | Wind tunnel or coast-down at several pitch angles; fit drag along and normal to the rotor plane | Sets the wall to the ¼ power |
| Motor thrust vs airspeed and inflow angle | Thrust stand in a tunnel | The model keeps f_max constant; edgewise flow at 50 m/s changes it |
| Yaw reaction coefficient | Torque stand | Decides the dive envelope |
| Inertia | Bifilar pendulum | Same |
| Target jerk and snap | Flight logs of the target class | The certified envelope is quoted per jerk |

## Appendix: reproduce

- Lean: `lake build`, then `scripts/axcheck.sh master_sufficient3 p3_bracket_power`.
- Sweeps: `python3 scripts/paper_sweeps.py` (writes `scripts/paper_sweeps.json`).
- Bracket tables: `python3 scripts/gap_v3.py` and `python3 scripts/gap_v3.py kn`.
- Weaving study: `python3 scripts/explore/weave.py`.
- Power-wall dual: `python3 scripts/explore/power_dual.py`.

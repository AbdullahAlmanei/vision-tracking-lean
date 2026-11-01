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

## Outcomes (2026-11-01)

**C, linear smoothing: ruled out.**
- With a 4-frame lag, a causal position-only filter must extrapolate. Lag-compensating
  FIRs (velocity-exact or better) therefore need gain Σ|h| ≥ about 2.
- The resulting jerk- and snap-type bounds (about 28–170 m/s³) never beat the target's own
  limits (jerk 5, snap 15).
- Copying the acceleration is near-optimal among linear planners. Beating it needs a
  nonlinear, rate-limited tracker, which is a research item.

**C-lite, analysis tightening: per-axis roll/pitch torque.**
- Roll and pitch motors now pay only for their own axis's rate change and inertia, plus the
  gyroscopic coupling.
- Result: the quad with yaw coefficient 0.03 and a 22 cm arm now holds `MasterIneq3` at
  jerk 5 up to about 64 m/s with 5° dives.
- A further yaw tightening (orthogonality of the lateral and pitch parts of Δn) was
  estimated at about 25% less yaw torque. That is not enough to flip any case, so it was
  not done.

**N1, sustained-turn thrust: vacuous here.**
- The detection range (about 570 m) exceeds the turn radius (350 m).
- A drone hovering near the turn centre keeps a circling target in view, so no thrust
  necessity follows from turns in this regime.
- N1 matters only when the detection range is below the turn radius.

**P3 status.**
- `p3_bracket` is proved.
- The necessary side allows about 85 m/s (motor/drag wall). The sufficient side allows
  about 64 m/s for jerk ≤ 5 with the tuned quad (5° dives), and ≤ 3 with the base quad.
- The remaining gap is torque at low collective thrust. It is not a physical wall: no
  universal torque lower bound of comparable size exists at a 100 m standoff.

## Nonlinear tracker exploration (2026-11-01): negative

Prototypes: `scripts/explore/tracker_saturated.py` and `scripts/explore/tracker_cascade.py`.
Each caps the planned jerk and snap below the target's and is tested against randomised
adversarial targets (accel ≤ A, jerk ≤ J, snap ≤ S).

- **Saturated third-order loop:** diverges (integrator windup).
- **Cascade** (acceleration feedforward with jerk and snap limits, slow saturated
  position/velocity correction): stable, but against A = 5.5, J = 5, S = 15 the worst lags
  are:
  - 325 m and 35 m/s with caps (2.5, 3);
  - 139 m and 24 m/s with caps (4, 6);
  - 39 m and 13 m/s with caps (6, 10).

The target can reverse its acceleration just as the tracker catches up, so the lags add up.
Keeping the error at the formation scale therefore needs planned jerk and snap close to the
target's own. A 10–40 m/s velocity lag also invalidates the drag part of the thrust budget
at 55 m/s. Conclusion: a rate-limited tracker does not buy enough to justify a nonlinear
invariant-set proof.

The remaining P3 gap (torque at low collective thrust) comes from two sides:

- **The tight formation.** The design stays exactly 100 m below the target, with tracking
  error of a few metres.
- **The weak necessary side.** The detection range is about 570 m and the half-FOV is 60°,
  so universal necessity arguments leave the drone a lot of slack.

Possible next steps:

1. **Tighten necessity.** A game-style lower bound in which flipping targets force
   thrust-direction rates, using the full visibility geometry.
2. **Accept the bracket.** Write up P3 with its explicit gap and the design rules it
   implies (yaw coefficient and arm length set the jerk ceiling).

## Sharper necessity (game-style torque bound): lemma chain and evaluation (2026-11-01)

The chain:

- **L1, window averaging.** If ‖x_drone − p_target‖ ≤ E, the triangle-weighted mean of
  (drone accel − target accel) over m steps is at most 4E/(mδ)². This follows from the
  exact identity for x_{k+m} − 2x_k + x_{k−m}.
- **L2, thrust must change.** A target reversing its lateral acceleration ±A forces the
  windowed mean of (thrust − drag) to change by at least 2A − 8E/τ² − (drag change).
- **L3, attitude must change.** Thrust vectors confined to a cone of half-angle θ about b
  change sideways by at most 2·T·sin θ, so the attitude must sweep
  Θ ≈ asin((2A − …)/(2T)).
- **L4, rates.** Sweeping Θ within Λ = 2τ + flip forces rate ≥ Θ/Λ (from
  `angle_b₃_step_le`), and angular acceleration ≥ 4Θ/Λ² if the motion starts and ends at
  rest.
- **Assembly.** An admissible, steadily starting reversing target escapes every trajectory
  unless rateMax ≥ Θ/Λ.

Evaluated at the reference parameters, optimising the window τ: the forced rate is
0.002–0.007 rad/s and the forced angular acceleration is about 10⁻³ rad/s². This holds
even when the drone must stay within 30 m of its formation point. Our sufficient design
uses about 1 rad/s.

The reason is structural. With hundreds of metres of slack (570 m range, 60° half-FOV,
hinge), a drone may respond to target maneuvers over 7–30 s windows. A tight formation
responds within about 1 s.

**Verdict.** In this regime no torque or rate necessity of practical size exists. The
agility (jerk) limits of `MasterIneq3` are a property of tight-formation designs, not of
physics. The chain is correct and formalizable, but it would yield a practically vacuous
theorem here. It becomes meaningful only when the allowed slack E is a few metres (very
narrow FOV or very short detection range).

## Looser formations (2026-11-01): three designs explored, none beats the tight formation

Prototypes, evaluated against the same speed-dependent budget: `scripts/explore/`.

1. **Loose yaw** (`loose_yaw.py`). Same position plan; the yaw follows the lateral lock
   through a first-order lag with gain k_ψ.
   - Yaw torque at the binding speed does not drop: about 0.2 N·m, as with the lateral
     lock.
   - The bound on the change of the body-rate vector has a floor of order (rate)², about
     2–5 rad/s² per term. It comes from bounding each piece of a rotation separately.
   - Above about 38° pitch, yaw error costs camera field of view.
2. **Averaged (lagged) formation** (`averaged_formation.py`). A positive smoothing kernel
   with no lag compensation, and thrust bounded directly as an average of admissible target
   states.
   - For windows of 2–4 s, the target's heading turns by tens of degrees inside the window,
     which breaks the forward and lateral thrust bounds (bank fails).
   - 4A/τ drops below the target's jerk only for windows longer than about 4 s.
   - The best case (0.5 s) is worse than the tight formation.
3. **Jerk/snap-capped nonlinear tracker** (`tracker_cascade.py`, earlier).
   - At about 35 m/s (A ≈ 5.5), caps (4, 6) keep lags near 140 m and 24 m/s, which fits
     the slack.
   - Combined with thrust bounds taken directly from the drone's own plan, this is the only
     design with a plausible gain at the binding point (slow dives, low thrust).
   - It needs an invariant-set proof for a saturated third-order tracking loop against
     adversarial targets.

**What binds is partly physics.** Following a fast dive with drag leaves low total thrust
(about 7 m/s² at 35 m/s in a 10° dive). Torque authority scales with thrust, and the
thrust-direction rate needed to follow lateral jerk J promptly is about J/T. The slack in
range and field of view only helps a tracker that follows *slowly*, which design 3
captures and designs 1–2 do not.

## Capped-tracker numerical study (2026-11-01): negative

**Files** (in `scripts/explore/`):
- `capped_tracker_study.py`: one-axis cascade tracker; adversary searched over switching
  times and jerk set-points.
- `capped_table.json`: worst lags.
- `capped_budget.py` and `capped_budget_vec.py`: payoff in the version 3 budget,
  speed-scheduled.

**Worst lags** (target jerk 5, snap 15):

| Caps (jerk/snap) | A = 5.5 | A = 10.6 |
|---|---|---|
| (5, 10) | 11.5 m, 3.8 m/s | 20.5 m, 5.9 m/s |
| (4, 6) | 26 m | 147 m |
| (3, 5) | 69 m | 563 m |

The acceleration lag is 2.5–10 m/s², and the planned acceleration exceeds the target's by
up to the correction authority (2 m/s²). Against jerk 10, snap 30 the lags are 2–4× larger.

**Payoff: worse than the tight formation at every speed.**
- Caps per axis combine to vector caps √2–√3 larger, which removes any gain.
- With vector caps, the saving on snap (about 17 → 10) is outweighed by three costs:
  - the acceleration lag and overshoot inflate the lateral thrust, hence the bank, the
    camera offset and the torque;
  - the correction authority lowers the vertical thrust margin at the low-thrust binding
    point;
  - the velocity lag shifts the drag terms.

**Verdict.** Within this proof architecture, the tight formation is the best of the five
designs explored:
- linear smoothing;
- per-axis torque tightening (adopted);
- loose yaw;
- the averaged formation;
- the capped tracker.

The remaining gap comes from two sources:
- the low-thrust physics of following fast dives (torque authority scales with thrust);
- squared-rate floor terms in the bounds on the change of the body-rate vector. Bounding
  each piece of a rotation separately loses the cancellation that makes a steady rotation
  need no torque.

The second source is the one remaining analysis lever: a bound on Δa that stays exact for
steady rotations.

## Aerodynamic forces on the frame (2026-11-01, raised by the user)

The model has rotor thrust along b₃ and isotropic quadratic drag, so the frame is
aerodynamically "rods". At 35–55 m/s the dynamic pressure is 750–1850 Pa, so frame and
arm aerodynamics are first-order.

**Flat-frame or arm normal force.** Model: −k_n‖v‖⟨v, b₃⟩b₃, with the centre of pressure
at the centre of mass. The force acts along b₃, so the thrust direction and all the
attitude and camera geometry are unchanged; only the motor collective changes, by
k_n‖v‖²·sin(pitch − flight-path angle). Prototype (budget_v3 with collective
adjustment):

| k_n | Steady top speed (±10°) | `MasterIneq3` at 55 m/s |
|---|---|---|
| 0 | ≈ 69 m/s | jerk ≤ 3–5 |
| 0.01 | ≈ 56 m/s | fails (mix_hi) |
| 0.02 | ≈ 46 m/s | fails (mix_hi) |

A frame pitched 70° into a 55 m/s wind is an air brake, so the motors saturate. The low
collective in dives does improve, but the top-speed loss dominates.

**Lift needs a wing at incidence.** A real lift/glide benefit needs a lifting surface whose
chord stays near the wind direction at cruise, at a design incidence angle i_w relative to
the rotor plane: the quad-plane or tail-sitter regime. Then:
- lift (⊥ v) carries weight and part of the turn force;
- the motors mainly cancel drag;
- the aerodynamic force is no longer along b₃, so attitude and lift couple implicitly.

This is a qualitative model change, with i_w as a new design parameter like the hinge range.
A rough sizing: supporting the weight of 1.5 kg at C_L = 0.5 needs about 0.04 m² at 35 m/s
and about 0.016 m² at 55 m/s.

## Winged-quad prototype (2026-11-01, user's design)

**Design:** cambered lateral arms (span along b₂, chord along the camera's fore–aft axis b₁)
and symmetric streamlined fore–aft arms. Prototype: `scripts/explore/winged_quad.py`
(vertical-plane trim). It models a lift polar to stall, a flat plate past stall,
cross-flow drag on the symmetric arms, and body drag. Wing area 0.018 m², AR 7.2,
C_L0 = 0.3, 12° stall.

**As specified (no incidence): an air brake.**
- The quad pitches nose-down to fly fast, so the wing's angle of attack is negative:
  −18° at 35 m/s and −38° at 55 m/s, past stall.
- Motor thrust at 55 m/s rises to 39 m/s² (the rods model needs 26), eating motor margin.
- In slow dives the wing lifts and *lowers* motor thrust (7.6 m/s²), which reduces torque
  headroom.

**With nose-up incidence of 15–25° (arm twist / wing at incidence): useful.**
- At 45–55 m/s the wing flies near zero angle of attack, motor thrust is about
  22–24 m/s², and pitch is 23–30° (rods: 68°).
- Pitch change per unit of vertical acceleration falls from about 2.1–2.7° to 0.4–0.6°
  per m/s², because the lift slope provides force authority.
- Costs:
  - low motor thrust in slow dives (about 6 m/s² at 35 m/s);
  - stall at about 20 m/s in dives;
  - turns still need banking, like the rods model.

**Lower drag (the main effect of streamlining) breaks the version 3 geometry.**
- With c = 0.0026 the necessary speed wall rises to about 148 m/s (c = 0.005: about
  107 m/s).
- But `MasterIneq3` fails everywhere, even at 45 m/s and with a 90° hinge:
  - the thrust is no longer drag-inflated, so the bank needed in turns approaches an
    airplane's (≥ 50° at 45 m/s);
  - the low pitch puts the backward camera out of its hinge range;
  - low collective thrust shrinks the torque headroom.
- The version 3 design implicitly relied on high drag: big thrust gives a small bank, and a
  steep pitch lets the camera look up.

**Implication.** A winged or streamlined quad needs its own formation and camera design:
- lift carries the maneuver forces (bank-to-turn, like the target);
- a camera mount that handles bank (roll hinge or 2-axis gimbal) and low pitch (hinge to
  about 90°);
- a budget whose force balance includes lift. The thrust direction is then no longer the
  total-force direction, which is a new model in Lean.

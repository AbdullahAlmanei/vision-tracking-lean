# Certified Pursuit

**Machine-checked necessary and sufficient conditions for a rigid-body quadrotor to keep a
fast fixed-wing aircraft in view**

*Draft, 2026-11-02. Lean 4 development: `AbdullahAlmanei/vision-tracking-lean`
(43 files, about 10,000 lines, 522 theorems; no `sorry`, standard axioms only). Blueprint:
https://abdullahalmanei.github.io/vision-tracking-lean/blueprint/*

## Abstract

We formalize a visual pursuit problem end to end:
- **Drone:** a quadrotor modelled as a full rigid body in discrete time, with four bounded
  motors, a mixer, Euler's rotational equation, exact rotations, tilt, rate and speed
  envelopes, parasitic drag, and a rotor-disc normal force.
- **Camera:** one camera on a rate-limited hinge.
- **Task:** keep a fixed-wing target with bounded speed, curvature, jerk, snap and climb
  inside the camera's field of view in every frame.

We prove:
1. an explicit **sufficient** inequality: a causal, position-only strategy with a 4-frame
   delay keeps every admissible target that starts in steady flight in view;
2. explicit **necessary** inequalities: a directional speed wall, and an energy-based
   power wall for the rotor-disc model. When they fail, a straight, level target escapes
   every drone trajectory, even one planned with the target's whole future.

For a 1.5 kg reference vehicle the bracket is 52 m/s (sufficient) against 57.7 m/s
(necessary).

We also show two tightness results:
- the power wall is within 0.4 m/s of exact steady force balance;
- its residual relaxation is reached by a point-mass *weaving* trajectory that a rigid body
  cannot fly, which marks exactly where a sharper certificate must use rotational limits.

## 1. Introduction

Visual pursuit of fast aircraft by multirotors is usually designed in simulation and
validated in flight. Neither answers the design question "can *any* strategy succeed with
this airframe, and does *ours* succeed for *every* admissible target?" We answer both, in a
proof assistant, for a model rich enough that the answer is an engineering number.

**Contributions.**
1. **A rigid-body pursuit model in Lean 4** (`Model.lean`): a discrete-time quadrotor
   (translational Euler, rotational Euler with inertia tensor, attitude by exact rotation
   vectors, four motors in [0, f_max] mapped by a plus mixer), a target class, a camera
   hinge, and causal strategies.
2. **A lifting theorem** (`Lifting.lean`, `QuadTraj.ofPlan`). A kinematic plan (positions
   and frames) whose required collective, torques, tilt, rate and hinge fit the limits *is*
   a valid rigid-body trajectory. This reduces sufficiency to inequalities on planned
   kinematics.
3. **`master_sufficient3`.** An explicit, speed-dependent inequality `MasterIneq3` under
   which a 4-frame-delayed FIR planner, an underneath formation, a lateral-locked frame and
   a clamped hinge keep the target in view.
4. **`master_necessary3` and `master_necessary_power`.** Necessity against full-information
   strategies, by a single escaping target, for the isotropic and the rotor-disc model.
5. **Sharp bounds that move the bracket by 10–30 m/s:**
   - an exact formula for the change of body rate (`RateExact`, `RateSharp`);
   - a sharp thrust-magnitude bound (`Under.thr_norm_le_Nhi`);
   - a speed-dependent discretisation term in the power wall.
6. **A tightness analysis** connecting the energy certificate to steady force balance and
   to a weaving relaxation.

## 2. Model

**Time and state.** Step δ > 0. The drone state is position x, velocity v, an orthonormal
frame (b₁, b₂, b₃ = b₁ × b₂), body rate Ω, motor thrusts f ∈ [0, f_max]⁴, and a hinge
angle η.

**Translational dynamics:**

  v_{k+1} = v_k + δ·[ (Σf/m − k_n‖v‖⟪v, b₃⟫) b₃ − g e₃ − c‖v‖v ].

**Rotational dynamics:** Ω_{k+1} = Ω_k + δ J⁻¹(τ(f) − Ω × JΩ). The attitude updates by the
rotation `rotate(δ·worldRate(Ω))`, written with Rodrigues' formula.

**Envelope:** tilt ≤ θ_max, ‖Ω‖ ≤ ω_max, ‖v‖ ≤ v_env, and the hinge range and rate.

**Target.** Positions and velocities with:
- a speed band [v_min, v_max];
- along-track and normal acceleration bounds (turn radius R);
- jerk and snap bounds on the second and third differences of velocity;
- climb angle and vertical acceleration bounds.

`StartsSteady` fixes the initial position, velocity and acceleration.

**Visibility:** ‖p − x‖ ≤ D (detection range, from pixel size) and
angle(cam, p − x) ≤ α. `KeepsInView` means visible in every frame.

**Strategies.** A `SteadyStrategy` maps target trajectories to drone trajectories causally:
the drone state up to k + 1 and the motors up to k depend only on target positions up to
k. Necessity is proved against *any* trajectory, which is stronger than any strategy class.

## 3. Results

**Theorem 1 (sufficiency, `master_sufficient3`).** If `MasterIneq3 P Q C δ F d` holds and
the planner filter F has a 4-frame lag, then every steadily starting target is
maintainable.

`MasterIneq3` is a finite list of scalar conditions for every target speed s in the band:
- positive vertical thrust, and lateral-to-total thrust ratio below 1;
- consecutive frames close;
- tilt, rate and hinge-rate limits;
- the low and high motor conditions, on per-axis roll/pitch torque and on yaw torque;
- camera offset plus planner position error within α.

**Theorem 2 (directional wall, `master_necessary3`, k_n = 0).** If every steadily starting
target is maintainable, then v_max ≤ dirSpeed(u) for every admissible direction u, where
dirSpeed is the drone's drag-limited speed along u under its tilt envelope.

**Theorem 3 (power wall, `master_necessary_power`, k_n > 0).** If every steadily starting
target is maintainable, then β·v_max ≤ α for every line with

  α − βs ≥ min(F_max s, F_max²/(4k_n s)) − c s³ + δ·B(s)²/2

on [0, v_env].

**Theorem 4 (brackets, `p3_bracket`, `p3_bracket_power`).** Theorems 1–3 combine:
`MasterIneq3` ⇒ maintainable ⇒ `NecIneq3` (or `NecPower`).

## 4. Proof architecture

### 4.1 Sufficiency

1. **Planner.** A causal FIR on past positions with a 4-frame delay. Its velocity,
   acceleration and position errors are bounded by filter constants times δ^j·jerk. A
   separate snap bound covers the planned acceleration's second difference (`PlannerSnap`).
2. **Speed-dependent budget.** Every per-step bound is evaluated in a speed window
   [sLo(s), sHi(s)] that covers three steps (`Under.window`). That is what makes the
   inequality satisfiable over a 20–55 m/s band.
3. **Frame.** Thrust direction n = nrm(thr), with thr = planned acceleration + g e₃ +
   drag. The lateral-locked frame is b₂ = nrm(−ℓ + ⟪ℓ, n⟫n) and b₁ = b₂ × n
   (`LateralFrame`), defined at every pitch whenever |⟪ℓ, n⟫| < 1.
4. **Body rate.** The rate is δ⁻¹ψ(a), with a the antisymmetric part of the frame step
   (`BodyRate`). Two results remove the earlier bound's floor:
   - `RateExact`: a rotation fixes its axis, so Δrate is exactly the change of rotation
     vector read in the new frame.
   - `RateSharp`: for frames b, c, e, Δa is the second difference of the frame read in c,
     plus the products ⟪Δ′cᵢ, Δ′cⱼ⟫ + ⟪Δcᵢ, Δcⱼ⟫. Those products are bounded by
     tilt × twist through Parseval in the earlier frame (`step_prod`, `twist_le`).

   This took the base vehicle from 34 to 64 m/s on ±5° dives at jerk 5.
5. **Torque and mixer.** Torque = J·ΔΩ/δ + Ω × JΩ, bounded per axis. `MixerOK` is
   discharged from `mix_lo` and `mix_hi`.
6. **Collective with the rotor disc.** Collective = ‖thr‖ + k_n‖v‖⟪v, n⟫.
   - Lower bound: from the planned thrust's power ⟪vP, thr⟫ ≥ VTlo, through a
     min-of-ratios lemma.
   - Upper bound: from ‖thr‖² = c²‖v‖⁴ + 2c‖v‖⟪v, a + g e₃⟫ + ‖a + g e₃‖², where the turn
     acceleration drops out because it is normal to v (`thr_norm_le_Nhi`). This took the
     rotor-disc envelope from 46 to 52 m/s.
7. **Hinge and visibility.** A clamped arctan law. The camera's off-target angle is at most
   bank ⊕ clamp miss ⊕ planner error (`Hinge`, `UnderTraj.traj_keeps`).
8. **Causality.** Plans, frames, rates and motors agree on agreeing target prefixes
   (`Under.traj_causal`).

### 4.2 Necessity

- **Escaping target** (`straightTarget_escapes_of_displacement`). A straight target at
  v_max escapes any drone whose displacement along u is at most kδV + K with V < v_max.
- **Directional wall** (`dir_excess_step`). The excess of ⟪v, u⟫ over V contracts by
  1 − 2δcV each step.
- **Power wall** (`PowerWall`).
  - Per-step power: F y − k_n‖v‖y² ≤ min(F_max‖v‖, F_max²/(4k_n‖v‖)) with y = ⟪v, b₃⟫.
  - Mechanical energy ½‖v‖² + g z changes by at most
    δ(availPower − c‖v‖³) + δ²B(‖v‖)²/2 per step.
  - A drone that keeps a level target in view has |Δz| ≤ 2D.
  - So the line hypothesis bounds its displacement along u.

## 5. Tightness

| Configuration | Necessary | Sufficient (jerk 5) |
|---|---|---|
| Isotropic drag, ±5° dives | 84.5 m/s | 69.5 m/s |
| k_n = 0.01, ±5° dives | 57.7 m/s | 52.1 m/s |
| k_n = 0.01, ±10° dives, yaw coefficient 0.03 | 57.7 m/s | 52.1 m/s |

**Power wall against force balance.** With the time step taken to zero, the energy
certificate gives 57.36 m/s at k_n = 0.01, against 57.3 m/s for exact steady straight,
level flight.

We searched a Lagrangian dual: energy plus constant-vector multipliers, which encode
average force balance and telescope for free. The optimal multiplier is zero
(`scripts/explore/power_dual.py`).

At k_n = 0.02 the certificate (48.2 m/s) exceeds steady flight (47.0 m/s). The relaxation
is *attained* by a point mass that over-thrusts and weaves: the sideways force does no work
but tilts the rotor disc off the wind. The point mass reaches 47.8 m/s. So no certificate
that uses only translational constraints can do better than about 48.2 m/s.

In the full rigid-body model the weave needs motor thrusts of −34 to +78 N (limit 22 N),
and every feasible weave is slower than steady flight (`scripts/explore/weave.py`). The
remaining gap therefore lies exactly in the rotational constraints. Closing it needs a
certificate that couples heading maintenance, roll acceleration and motor headroom.

**Sufficiency gap.** What remains is design conservatism plus genuine headroom:
- the formation copies the target exactly, including momentary thrust peaks at top speed;
- the top motor needs reserve for steering;
- smaller bound slack: k_n‖v‖² in place of k_n‖v‖⟪v, n⟫, planner errors, the speed
  window.

## 6. Proof engineering

- **Scale.** About 10,000 lines in 43 files, built in about 5 minutes. Statements are
  checked against standard axioms by `scripts/axcheck.sh` in CI. A leanblueprint site maps
  every result to its declarations.
- **Budgets as structures.** `MasterIneq*` is a `Prop` structure of scalar conditions,
  mirrored term by term in Python (`budget_v3.py`). Numeric exploration and proof stay in
  lock-step: every proof refinement was prototyped numerically first, and abandoned if it
  did not pay.
- **Tactic lessons.**
  - Generalize or abstract terms before `linarith`, since it treats syntactically different
    products as distinct atoms.
  - Rewrite `k+1+1` to `k+2` *before* unfolding plan definitions, to avoid `whnf`
    timeouts.
  - Prefer explicit `calc` and `mul_le_mul` chains over `nlinarith` on large contexts.
  - Keep `set` abbreviations consistent with hypotheses created later.
- **Model changes as refactors.** Adding the rotor-disc force touched every consumer of the
  translational equation. Older results now carry an explicit `Q.normalDrag = 0`
  hypothesis rather than silently changing meaning.

## 7. Limitations and future work

- **Model scope:** constant motor thrust in airspeed, no aerodynamic moments, no wind, no
  ground, no sensor noise.
- **Target class:** targets start in steady flight. Turning necessity is vacuous at our
  ranges: a drone hovering near the turn centre sees a circling target.
- **Open:** a rotational certificate for the weaving gap. Also position-only strategies with
  slack formations that trade range and field of view for agility. The torque-forcing
  results show that physics forces almost nothing there.

## Reproducibility

`lake build`; `scripts/axcheck.sh master_sufficient3 p3_bracket p3_bracket_power`;
`python3 scripts/gap_v3.py [kn]`; `python3 scripts/paper_sweeps.py`.

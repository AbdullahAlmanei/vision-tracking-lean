# P3 Master Inequality Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove, in Lean on the full rigid-body quadrotor, a master inequality that decides whether a camera-carrying quad can keep a manoeuvring fixed-wing target in view. It must be sufficient as stated and necessary up to an explicit gap.

**Architecture:** Three layers. (1) *Necessity*: limits no strategy beats (directional speed, pointing at every state, steady window). (2) *Lifting*: any kinematic plan (positions, frames, hinge) satisfying explicit rate, torque and mixer budgets is a valid `QuadTraj`. (3) *Planner*: a causal, position-only FIR formation planner whose tracking error and smoothness are bounded by filter constants. The master theorem plugs (3) into (2) for the overhead formation and pairs it with (1).

**Tech Stack:** Lean 4 `v4.30.0-rc1`, Mathlib (rev pinned in `lake-manifest.json`), leanblueprint + plastex (borrowed from `../two-ctrl-root/two-control-lean/.venv/bin`), sympy for polynomial certificates.

**Spec:** `blueprint/src/chapters/roadmap.tex` plus the decisions agreed with the user in conversation and recorded in "Where we are" below. The blueprint is the maintained spec: every task updates it.

---

## Where we are (2026-10-31, commit `c262d40`)

The model is in `VisionTracking/Model.lean`.
- **Target:** Euler kinematics; speed in `[vMin, vMax]`; turn radius `R`; along-track acceleration `aTan`; jerk `j` (acceleration changes by at most `δ j` per step); climb angle `γ`.
- **Quadrotor (`QuadTraj`):** orthonormal right-handed frame `b₃ = b₁ × b₂`; body rates `Ω` driven by Euler's equation; 4 motors in "+" layout with thrusts in `[0, fMotor]`; Rodrigues attitude update; drag `c_D ‖v‖ v`; tilt envelope; rate limit; speed envelope `speedEnv` with `δ c_D speedEnv ≤ 1/2` assumed.
- **Camera:** pitch hinge about `b₂`; boresight `cos η b₁ + sin η b₃`.
- **Strategies:** causal; `PosStrategy` sees target positions only. `Maintainable p₀ v₀ a₀` quantifies over targets with a known start.

| Proved (axioms = `propext, Classical.choice, Quot.sound`) | File |
|---|---|
| Directional speed limit `dirSpeed u`; directional escape `not_maintainable_of_dirSpeed_lt` | `DirectionalSpeed.lean` |
| Pointing reduction `exists_visible_iff`; every-state bound `QuadTraj.elevation_mem_of_sees` | `Pointing.lean`, `Frame.lean` |
| Overhead tilt-band hinge condition `overhead_band_iff`; fixed mount `fixed_overhead_iff` | `Overhead.lean` |
| Forced tilt `b₃_eq_steadyAxis`; window `steady_chase_window`; speed forms | `SteadyChase.lean` |
| Steady formation iff window `steady_formation_iff` | `SteadyFormation.lean` |
| Inverse mixer `exists_motors_of_wrench`; Rodrigues `inner_rotate`, `rotate_cross`, `angle_rotate_le` | `Motors.lean`, `Rotation.lean` |
| **Open:** `exists_rotate_frame` (sorry) | `Plan.lean` |

## Where we're going

`master_sufficient` (Task 9) and `master_necessary` (Task 10), stated over the `MasterBudget` quantities (Task 6). The gap between them is named explicitly:
- planner lag `ρ = H₃ δ³ j`;
- the thrust and tilt error margins;
- the overhead-only geometry of the sufficient side versus the steady window of the necessary side.

Task 11 then optimises constants and produces the paper's numbers.

## Global Constraints

- Every theorem is about `QuadTraj` / `TargetTraj` from `Model.lean`. No reduced or point-mass drone in any headline statement.
- No artificial caps. Every hypothesis is either a physical parameter inequality or a time-step fineness condition (`δ c_D speedEnv ≤ 1/2`-style).
- `lake build` finishes with no errors and no warnings, except `declaration uses sorry` in `VisionTracking/Plan.lean` only.
- Each proved headline theorem: `#print axioms` lists exactly `[propext, Classical.choice, Quot.sound]`.
- Blueprint: every new declaration gets a `\lean{}` node; `\leanok` only when sorry-free. `leanblueprint web` and `lake exe checkdecls blueprint/lean_decls` pass before every push.
- Notation: `⟪x, y⟫` (no `_ℝ`); `λ` is reserved, so use `el`. Avoid `set` when you later rewrite by the unfolded term (use `generalize`).
- Commit messages end with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. Push to `origin master` only after the blueprint check passes.

## Review Focus

1. **Small-step regime**: statements must not silently need `δ → 0`. Every use of fineness appears as an explicit hypothesis. Test: each headline theorem's hypotheses are listed in its blueprint node.
2. **Tilt near zero (yaw ill-conditioned)**: the downhill frame is undefined at tilt 0. Every theorem using it carries `0 < Θlo` (in `MasterBudget`: `Hinf > 0`). Test in Task 7.
3. **Vertical climb/dive edge**: `γ < π/2` keeps the horizontal speed positive. `Hinf` must use `cos γ`. Test in Task 6: `Hinf` is monotone decreasing in `γ` (a numeric `norm_num` sanity instance).
4. **Initial transient**: the planner needs history before step 0. The virtual history uses constant acceleration `a₀`, so the jerk bound also holds across the boundary. Test in Task 4: the extended sequence satisfies `jerk_le` for all integer indices.
5. **Motor saturation at peak thrust**: the mixer needs `F/4 ± torque terms ∈ [0, fMotor]`, not just `F ≤ 4 fMotor`. Test in Task 9: the master hypothesis includes the torque-augmented mixer bound.

---

### Task 1: Axis-angle for nearby frames

**Files:**
- Create: `VisionTracking/AxisAngle.lean`
- Modify: `VisionTracking/Plan.lean` (delete `exists_rotate_frame`), `VisionTracking.lean` (import), `blueprint/src/chapters/roadmap.tex` → move the node to `chapters/steady.tex` §Lifting
- Scratch: `/tmp/claude-1000/vt/axis.py` (sympy)

**Interfaces:**
- Consumes: `rotate`, `rodr`, `inner_rodr`, `rodr_cross`, `cross_ofLp_*`, `inner_eq_coords` (Rotation/Frame).
- Produces:
  - `frameTrace (a₁ a₂ c₁ c₂ : E3) : ℝ := ⟪a₁,c₁⟫ + ⟪a₂,c₂⟫ + ⟪cross a₁ a₂, cross c₁ c₂⟫`
  - `exists_rotate_frame (orthonormality hyps) (hnear : -1 < frameTrace a₁ a₂ c₁ c₂) : ∃ ω, ‖ω‖ = Real.arccos ((frameTrace a₁ a₂ c₁ c₂ - 1) / 2) ∧ rotate ω a₁ = c₁ ∧ rotate ω a₂ = c₂ ∧ rotate ω (cross a₁ a₂) = cross c₁ c₂`
  - `norm_rotVec_le (each angle(aᵢ,cᵢ) ≤ ε, ε ≤ π/2) : Real.arccos ((frameTrace … - 1)/2) ≤ 2 * ε`

- [ ] **Step 1:** In `AxisAngle.lean`, state both theorems with `sorry`. Run `lake build VisionTracking.AxisAngle`; the `#print axioms` check in `scratch/ax.lean` shows `sorryAx`.
- [ ] **Step 2:** sympy certificate. Write `cᵢ = Σⱼ Mᵢⱼ aⱼ` with `M` orthogonal and `det = 1`. With `σ := ½ Σᵢ aᵢ × cᵢ` and `cosθ := (tr − 1)/2`, certify modulo the orthogonality ideal: `(1 + cosθ)(cᵢ − cosθ·aᵢ − σ × aᵢ) = ⟪σ, aᵢ⟫ σ` and `‖σ‖² = 1 − cos²θ`. Print `reduced(…)` quotients exactly as in `rod.py` / `gen.py`.
- [ ] **Step 3:** Prove `exists_rotate_frame`. If `σ = 0`, then `tr = 3`, `ω = 0`, and `rotate_zero`. Otherwise `ω := arccos(cosθ) • (‖σ‖⁻¹ • σ)`, and `sin(arccos c) = √(1−c²) = ‖σ‖`; finish each component with `linear_combination` using the Step 2 quotients.
- [ ] **Step 4:** Prove `norm_rotVec_le`. `tr ≥ 3 cos ε` gives `1 − cos θ ≤ (3/2)(1 − cos ε)`; with `(2/π²)x² ≤ 1 − cos x ≤ x²/2` this yields `θ ≤ (π/2)√(3/2) ε ≤ 2ε`.
- [ ] **Step 5:** `lake build` is clean; axioms check is clean for both; blueprint web + checkdecls pass. Commit "Prove axis-angle for nearby frames".

### Task 2: Lifting a kinematic plan to a `QuadTraj`

**Files:**
- Create: `VisionTracking/Lifting.lean`
- Modify: `VisionTracking.lean`, `blueprint/src/chapters/steady.tex`

**Interfaces:**
- Consumes: Task 1 `exists_rotate_frame`; `exists_motors_of_wrench`, `QuadParams.mix`; `inner_rotate`, `rotate_cross`.
- Produces:
  - `structure KinPlan (Q C δ)` with fields `x v b₁ b₂ : ℕ → E3`, `η : ℕ → ℝ`, `steps : StepsWith δ x v`, frame orthonormality for `b₁ b₂`, and `near : ∀ k, -1 < frameTrace (b₁ k) (b₂ k) (b₁ (k+1)) (b₂ (k+1))`.
  - `KinPlan.thrust k : E3 := δ⁻¹ • (v (k+1) - v k) + Q.g • up + (Q.drag * ‖v k‖) • v k`
  - `KinPlan.rate k : E3`: body coordinates `(⟪ω,b₁⟫, ⟪ω,b₂⟫, ⟪ω,b₃⟫)/δ` of the Task 1 rotation vector `ω` from frame `k` to frame `k+1` (chosen with `Classical.choose`)
  - `KinPlan.torque k : E3 := Q.inertia (δ⁻¹ • (rate (k+1) - rate k)) + cross (rate k) (Q.inertia (rate k))`
  - `QuadTraj.ofPlan (π : KinPlan Q C δ) (hdir : ∀ k, thrust k = ‖thrust k‖ • b₃ k) (hmix : ∀ k, mixer bounds h1–h4 of exists_motors_of_wrench with F = Q.mass * ‖thrust k‖, τ = torque k) (htilt …) (hrate : ∀ k, ‖rate k‖ ≤ Q.rateMax) (hspeed …) (hhinge range/rate …) : QuadTraj Q C δ`
  - `ofPlan_x`, `ofPlan_b₁`, `ofPlan_b₃`, `ofPlan_η`: `rfl` lemmas.

- [ ] **Step 1:** State `ofPlan` with `sorry` fields. Test: `example : (QuadTraj.ofPlan π …).x = π.x := rfl` compiles.
- [ ] **Step 2:** Fill `translational` from `hdir`, and `rotational` from the definition of `torque` (`inertiaInv ∘ inertia = id` lemma: prove `inertiaInv_inertia` by `ext; fin_cases; field_simp`). Fill `attitude` from Task 1 (`worldRate` of the body coordinates reassembles `ω`: prove `worldRate_coords` from frame orthonormality). Motors come from `exists_motors_of_wrench` via `Classical.choose`.
- [ ] **Step 3:** The build is clean and `ofPlan` is sorry-free (axioms check). Blueprint node `thm:lifting`. Commit "Lift kinematic plans to rigid-body trajectories".

### Task 3: Normalization and downhill-frame regularity

**Files:**
- Create: `VisionTracking/Regularity.lean`

**Interfaces:**
- Produces:
  - `norm_normalize_sub_le (a b : E3) (hm : 0 < m) (ha : m ≤ ‖a‖) : ‖‖a‖⁻¹•a - ‖b‖⁻¹•b‖ ≤ 2 * ‖a - b‖ / m`
  - `norm_normalize_second_le (a b c) (hm) (norms ≥ m) (hstep : ‖b-a‖ ≤ m/2 ∧ ‖c-b‖ ≤ m/2) : ‖n c - 2•n b + n a‖ ≤ 2*‖c - 2•b + a‖/m + 12*(‖b-a‖^2 + ‖c-b‖^2)/m^2` where `n x = ‖x‖⁻¹•x`
  - `downhill (b₃ : E3) : E3 := (‖-up + ⟪b₃,up⟫•b₃‖)⁻¹ • (-up + ⟪b₃,up⟫•b₃)`, the unit `b₁` aligned with straight down in the rotor plane.
  - `downhill_unit`, `downhill_orth`, `downhill_aligned` (`⟪downhill b₃, -up⟫ = √(1 - ⟪b₃,-up⟫²)`) for `0 < angle b₃ up < π/2`
  - first and second difference bounds for `downhill` with constants `2/sin Θlo` and `12/sin² Θlo` (same shape as the normalization lemmas, with `m = sin Θlo`)

- [ ] **Step 1:** State all with `sorry`. Where `12` comes from: `‖D²n(x)‖ ≤ 3/‖x‖²`, and on segments staying above `m/2` that is `≤ 12/m²`. The second-order Taylor remainder contributes `½·12/m²·(‖u‖² + ‖w‖²)`, which is `≤ 12(…)/m²` with room to spare. Record this derivation in the docstring. If the Lean proof needs a larger constant, change it here and in Task 6 only.
- [ ] **Step 2:** Prove the first-difference bound algebraically (the classical `‖â − b̂‖ ≤ 2‖a−b‖/‖a‖`).
- [ ] **Step 3:** Prove the second-difference bound via Mathlib's `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` applied to `Dn` along the segments (or a direct algebraic expansion if shorter).
- [ ] **Step 4:** Prove the `downhill` facts. `downhill` equals the `b₁` from `exists_aligned` with `u = -up`, so reuse its algebra.
- [ ] **Step 5:** Clean build and axioms check; blueprint node `lem:regularity`. Commit.

### Task 4: FIR formation planner — generic bounds

**Files:**
- Create: `VisionTracking/Planner.lean`

**Interfaces:**
- Consumes: `TargetTraj`, `TargetTraj.StartsAt`.
- Produces:
  - `TargetTraj.ext (T) (a₀) : ℤ → E3`: positions for `n ≥ 0`, and a constant-acceleration `a₀` virtual history for `n < 0`. Lemma `ext_third_diff_le : ‖ext (n+3) - 3•ext (n+2) + 3•ext (n+1) - ext n‖ ≤ δ^3 * P.jerk` for all `n : ℤ` (given `StartsAt p₀ v₀ a₀`).
  - `structure FIR` with `h : ℕ → ℝ`, `M : ℕ` (support `⊆ [2, M]`), `sum_h : Σ h = 1`, `mom1 : Σ i*h i = 0`, `mom2 : Σ i^2*h i = 0`.
  - constants `FIR.H0 = Σ|hᵢ|`, `H1 = Σ|hᵢ| i`, `H2 = Σ|hᵢ| i(i+1)/2`, `H3 = Σ|hᵢ| i(i-1)(i-2)/6`, `TV = Σᵢ |hᵢ - hᵢ₋₁|` (over `0..M+1`)
  - `planPos F T a₀ off k := Σᵢ hᵢ • ext (k - i) + off`, and `planVel k := δ⁻¹ • (planPos (k+1) - planPos k)`
  - bounds, all for every `k : ℕ`:
    - `planPos_err : ‖planPos k - (T.p k + off)‖ ≤ H3 * δ^3 * j`
    - `planVel_err : ‖planVel k - T.v k‖ ≤ H2 * δ^2 * j`
    - `planAcc_err : ‖planAcc k - targetAcc k‖ ≤ H1 * δ * j`
    - `planAcc_step : ‖planAcc (k+1) - planAcc k‖ ≤ H0 * δ * j`
    - `planAcc_second : ‖planAcc (k+2) - 2•planAcc (k+1) + planAcc k‖ ≤ TV * δ * j`
    - `planPos_causal`: `planPos (k+2)` depends only on `T.p 0..k`

- [ ] **Step 1:** State everything with `sorry`. Test instance: `FIR.extrap3 : FIR` with `h 2 = 6, h 3 = -8, h 4 = 3` (moments check by `norm_num`); `example : FIR.extrap3.H3 = 4 := by norm_num [...]`.
- [ ] **Step 2:** Prove `ext_third_diff_le` (the boundary uses `StartsAt` and `jerk_le`).
- [ ] **Step 3:** Prove `planPos_err`. With the backward quadratic `Q` through `ext k, ext (k-1), ext (k-2)`, moment exactness gives `Σ hᵢ Q(k−i) = ext k`, and `|ext(k−i) − Q(k−i)| ≤ C(i,3)·max‖∇³‖`.
- [ ] **Step 4:** Prove the velocity, acceleration, step and second bounds. The acceleration is `Σ hᵢ A_{k−i}` (linearity); the second bound uses summation by parts.
- [ ] **Step 5:** Clean build and axioms check; blueprint chapter `planner.tex` with `def:fir`, `thm:fir-bounds`. Commit.

### Task 5: The smoothing family `FIR.smooth N`

**Files:**
- Modify: `VisionTracking/Planner.lean`

**Interfaces:**
- Produces: `FIR.smooth (N : ℕ) (hN : Odd N) : FIR`. With `L = (3N+1)/2` and `c = (N²−1)/(24N²)`, weights `(6−c, −8+2c, 3−c)/N` sit on lag blocks `[L, L+N)`, `[L+N, L+2N)`, `[L+2N, L+3N)`. Bounds: `smooth_H0 ≤ 17`, `smooth_H1 ≤ 17*(5N)`, `smooth_H2 ≤ 17*(5N)^2`, `smooth_H3 ≤ 17*(5N)^3/6`, `smooth_TV ≤ 34/N`. Also `smooth_one : FIR.smooth 1 _ = FIR.extrap3` (pointwise `h`).

- [ ] **Step 1:** State with `sorry`; `norm_num` test that the moments vanish for `N = 3` and `N = 5`.
- [ ] **Step 2:** Prove the moments for general odd `N` (block sums via `Finset.sum_range_id_mul_two`-style closed forms). Prove the five bounds.
- [ ] **Step 3:** Clean build and axioms check; blueprint `thm:smooth-family`. Commit.

### Task 6: `MasterBudget`

**Files:**
- Create: `VisionTracking/Budget.lean`

**Interfaces:**
- Produces: `structure MasterBudget (P Q C δ F d)`, every field a `noncomputable def` in terms of the parameters:
  - target and planner terms: `Amax = aTan + vMax²/R`; `εD = H1 δ j`; `εV = H2 δ² j`; `ρ = H3 δ³ j`;
  - `Fsup = g + Amax + εD + c_D (vMax+εV)²`;
  - `Zinf = g − Amax − εD − c_D (vMax+εV)(vMax sin γ + εV)`; `Zsup` symmetric;
  - `Hsup = Amax + εD + c_D(vMax+εV)²`;
  - `Hinf = min_{v∈{vMin,vMax}} (c_D cos γ − sin γ/R) v² − aTan cos γ − εD − c_D(2vMax+εV)εV`;
  - `Θhi = arctan(Hsup/Zinf)`; `Θlo = arctan(Hinf/Zsup)`;
  - `ΔTmax = δ·(H0 j + 2 c_D (vMax+εV)(Amax+εD))` (per-step thrust change) and `Δ²Tmax = δ·(TV j + 2 c_D (vMax+εV)(H0 j) + 2 c_D δ (Amax+εD)²)`;
  - `εb3 = 2ΔTmax/Zinf` (Task 3 first bound, `m = Zinf`); `εb1 = 2εb3/sin Θlo` (downhill first bound); `Ωreq = 2(εb3 + εb1)/δ` (Task 1 `norm_rotVec_le`);
  - `τreq`: Task 3 second bounds applied to `b₃` and `b₁`, divided by `δ²` and multiplied by `max(Jx,Jy,Jz)`, plus `max J·Ωreq²` (the gyroscopic term). Write it as the literal composition of those lemma constants;
  - `μ = arcsin(ρ/d)`.
  
  And `structure MasterIneq` (Props):
  - `0 < Zinf`; `0 < Hinf`; `Θhi ≤ tiltMax`;
  - `m·Fsup` plus torque terms within the mixer (Review Focus 5);
  - `Ωreq ≤ rateMax`;
  - `vMax + εV ≤ speedEnv`; `δ c_D speedEnv ≤ 1/2`;
  - `lo ≤ Θlo − π/2 + α − μ`; `hi ≥ Θhi − π/2 − α + μ`;
  - hinge rate `≥ Θ-rate`;
  - `ρ < d`; `d + ρ ≤ detectRange`.

- [ ] **Step 1:** Write the definitions (no proofs needed). Test: a `norm_num` instance with the reference numbers (target `vMax = 51.4`, `R = 350`, `γ = π/6` → use `γ` with `sin γ = 1/2` by hypothesis) shows `0 < Hinf` for `c_D = 0.0237`, `aTan = 2` (Review Focus 3).
- [ ] **Step 2:** Clean build; commit "Define the master budget".

### Task 7: Overhead formation plan and its budgets

**Files:**
- Create: `VisionTracking/OverheadPlan.lean`

**Interfaces:**
- Consumes: Tasks 2–6; `overhead_band_iff`, `angle_eq_abs_sub_of_aligned`, `elevation_neg_up`.
- Produces: `overheadPlan (F : FIR) (d : ℝ) (T) (a₀) : KinPlan Q C δ`:
  - `x = planPos` with `off = d • up`;
  - `b₃ = normalized thrust`, `b₁ = downhill b₃`, `b₂ = b₃ × b₁`;
  - `η = clamp (angle b₃ up - π/2) lo hi`.

  Lemmas, each with hypotheses only in terms of `MasterBudget` fields (Task 6):
  - `overheadPlan_thrust_bounds`: `Zinf ≤ ⟪thrust,up⟫`, `‖thrust‖ ≤ Fsup`, horizontal part in `[Hinf, Hsup]`
  - `overheadPlan_tilt_mem : angle b₃ up ∈ [Θlo, Θhi]`
  - `overheadPlan_rate_le`, `overheadPlan_torque_le`: from Task 1 `norm_rotVec_le` + Task 3 regularity + Task 4 `planAcc_step/second`
  - `overheadPlan_sees : angle (frameCam b₁ b₃ η) (T.p k - x k) ≤ α`: hinge clamp + `arcsin(ρ/d)` margin

- [ ] **Step 1:** State with `sorry`. Test: `overheadPlan_tilt_mem` yields `0 < angle b₃ up` (Review Focus 2).
- [ ] **Step 2:** Prove the thrust bounds from `TargetTraj` (lemma `targetAcc_norm_le : ‖A‖ ≤ aTan + vMax²/R`) plus the Task 4 errors.
- [ ] **Step 3:** Prove the tilt band, rate and torque bounds.
- [ ] **Step 4:** Prove `overheadPlan_sees`. The angle to `-up` is `|η − (t − π/2)|` (aligned downhill frame), and `angle(-up, ℓ) ≤ arcsin(ρ/d)` by `‖ℓ − (−d·up)‖ ≤ ρ`.
- [ ] **Step 5:** Clean build and axioms check; blueprint. Commit.

### Task 8: Weaving drones — mean forward thrust (necessity side)

**Files:**
- Create: `VisionTracking/Weaving.lean`

**Interfaces:**
- Produces: `mean_forward_thrust_ge`. For any `d : QuadTraj`, a level target at speed `v` along `w` (`levelTarget`), and `K ≥ 1`: if `‖T.p k − d.x k‖ ≤ Rr` for `k ≤ K`, then
  `Σ_{k<K} (F_k/m)·⟪b₃ k, w⟫ ≥ K·Q.drag·v·(v − 2Rr/(Kδ)) − (‖d.v 0‖ + Q.speedEnv)/δ`.
  Corollary `exists_lean_ge`: some `k < K` has `(F_k/m)⟪b₃,w⟫ ≥` that mean.

- [ ] **Step 1:** State with `sorry`.
- [ ] **Step 2:** Telescope `⟪v,w⟫` through `translational` (using `⟪up,w⟫ = 0`). Use `‖v‖⟪v,w⟫ ≥ ⟪v,w⟫·|⟪v,w⟫|` and the tangent-line bound `s|s| ≥ 2s̄s − s̄²` for `s ≥ −speedEnv`, with `s̄ = mean ≥ v − 2Rr/(Kδ)` (displacement bound from range). If the tangent bound fails for negative `s`, weaken the statement to `s ≥ 0` frames and record that in the blueprint remark.
- [ ] **Step 3:** Clean build and axioms check; blueprint remark "Weaving drones" → theorem. Commit.

### Task 9: `master_sufficient`

**Files:**
- Create: `VisionTracking/Master.lean`

**Interfaces:**
- Produces: `theorem master_sufficient (F : FIR) (d : ℝ) (h : MasterIneq P Q C δ F d) (p₀ v₀ a₀) : Maintainable P Q C δ p₀ v₀ a₀`.
  Corollary `master_sufficient_smooth (N)`: the same with `F = FIR.smooth N`, all `H`-constants replaced by the Task 5 bounds (monotonicity of `MasterIneq` in the `H`s, lemma `MasterIneq.mono`).

- [ ] **Step 1:** State with `sorry`.
- [ ] **Step 2:** Build the `PosStrategy` from `QuadTraj.ofPlan (overheadPlan F d T a₀)` (Task 7). Causality comes from `planPos_causal` plus the frame/η definitions depending on `planPos` only. Visibility comes from `overheadPlan_sees` and the range bound.
- [ ] **Step 3:** Clean build and axioms check; blueprint `thm:master-sufficient`. Commit and push.

### Task 10: `master_necessary` and the gap

**Files:**
- Modify: `VisionTracking/Master.lean`

**Interfaces:**
- Produces: `theorem master_necessary (h : MaintainableFullInfo P Q C δ p₀ (vMax • u) 0) : ∀ u admissible, P.vMax ≤ Q.dirSpeed u` (from `not_maintainable_of_dirSpeed_lt`). Also `steady_necessary`, re-exporting `steady_formation_iff (→)`, and `gap` lemmas stating each sufficient-side condition minus its necessary counterpart as an explicit expression in `εD, εV, ρ, μ`.

- [ ] **Step 1:** State; prove (assembly only).
- [ ] **Step 2:** Blueprint chapter `master.tex`: the two theorems side by side, plus a table of gap terms with their scaling in `δ`, `N`, `j`. Commit and push.

### Task 11: Constants and paper numbers

**Files:**
- Create: `scripts/numbers.py`; Modify: `blueprint/src/chapters/master.tex`

- [ ] **Step 1:** Evaluate `MasterBudget` for the reference target and two quads: (racing `c_D=0.0237, fMotor·4 = 4mg`) and (camera quad, user to supply or default `c_D = 0.05, 2.5mg`). Find the best `N` (smoothing window) minimising `ρ` subject to `τreq ≤` the mixer. Print the feasible `(d, α, hinge range)` region.
- [ ] **Step 2:** If any constant (Task 3's `12`, Task 5's `17`, `34`) makes the reference case infeasible while a direct numeric simulation says it should be fine, open a follow-up task to tighten that lemma. Do not tighten speculatively.
- [ ] **Step 3:** Commit the script and the numbers table.

---

## Out of scope for this plan

- Heading-locked (chase-from-behind) formations for manoeuvring targets. The steady case is covered by `steady_formation_iff`; manoeuvring needs a rotating offset and is the next plan.
- Noise in bearing/size measurements. The model is noiseless with known target size.
- Ground, obstacles, wind.

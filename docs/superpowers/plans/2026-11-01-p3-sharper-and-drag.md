# Sharper rate-change bound, and attitude-dependent drag

Date: 2026-11-01. Requested by the user: (1) caveat (done), (2) the rate-change bound, and
(3) an attitude-dependent drag model.

## Item 2: a bound with no rate-product floor

**Prototype payoff.** Same `Budget3` structure, with the rate-change terms replaced by their
physical form:

| Quad | 5° dives | 10° dives |
|---|---|---|
| Base | jerk 3 → 5 | jerk 1 → 3 |
| Tuned | jerk 5 → 8 | jerk 3 → 5 |

**Steps.**

1. **Exact rate change.**
   - `rotate ω ω = ω`, and ⟪rotate ω x, ω⟫ = ⟪x, ω⟫.
   - Hence `KinPlan.rate (k+1) − rate k = δ⁻¹ toF(b_{k+1})(rotVec (k+1) − rotVec k)`, and
     ‖Δrate‖ = ‖ΔrotVec‖/δ with components ⟪b_j(k+1), ΔrotVec⟫/δ.
2. **Gibbs representation of each step's rotation, as tilt then twist.**
   - Gibbs vector g = tan(θ/2)·axis.
   - Minimal tilt: g_M = (n × n′)/(1 + ⟪n, n′⟫).
   - Twist about n′: g_T = t·n′, with t = tan(τ/2) and g_T ⟂ g_M.
   - Composition (exact because g_T·g_M = 0): g = g_T + g_M + g_T × g_M.
   - rotVec = (2 arctan‖g‖/‖g‖) g.
3. **Change of g.**
   - Δg_M: the tilt curvature, n′ × Δ²n with sharp normalisation.
   - Δ(t n′) = Δt·n″ + t′Δn′, giving the twist change plus a twist × tilt term.
   - Δ(g_T × g_M): twist × tilt products.
   - Every term is physical, with no frame-step² floor.
4. **Twist of the lateral-locked frame.**
   - t from the frames: t = ⟪(M b₂) × b₂′, n′⟫/(1 + ⟪M b₂, b₂′⟫).
   - Its change is bounded by the heading curvature, sb × the tilt curvature, and products.
5. **New budget.**
   - Change `Budget3` (`rp2`, `yaw2`) and the `UnderTraj` torque lemmas to the per-axis
     form: roll/pitch from Δg_M plus twist × tilt, yaw from Δt.
   - Mirror the change in `budget_v3.py`.

## Item 3: attitude-dependent drag

**Model.**
- Isotropic parasitic drag: c_p‖v‖v.
- Rotor disc and frame normal force: −k_n‖v‖⟪v, b₃⟫ b₃, with the centre of pressure at the
  centre of mass.

**Consequences.**
- The normal force acts along b₃. So the thrust direction (and every frame, rate and camera
  bound) is the direction of a + g e₃ + c_p‖v‖v, exactly as now with c_p in place of c.
- Only the motor collective changes: F/m = ‖thr‖ + k_n‖v‖⟪v, n⟫.

**Lean changes.**
- `QuadParams` gains `kn ≥ 0`.
- `QuadTraj.translational` gains the term.
- Every lifting lemma passes the new collective to `MixerOK`.
- Budgets gain bounds on ⟪v, n⟫:
  - v1 and v2 assume `kn = 0` (stated);
  - v3 gets the full treatment.

**Necessity: power wall.**
- The power delivered along v satisfies
  ⟪v, f⟫ ≤ F y − k_n‖v‖ y² − c_p‖v‖³ − g v_z, where y = ⟪v, b₃⟫.
- Maximising over y gives ⟪v, f⟫ ≤ F²/(4 k_n ‖v‖) + g‖v‖ − c_p‖v‖³.
- So ‖v‖ cannot stay above V* = the root of c_p V⁴ − g V² = F²/(4 k_n).
- A target faster than V* escapes every trajectory.
- Prototype: V* ≈ 57 m/s at k_n = 0.01, ≈ 46 m/s at k_n = 0.02 (with c_p = 0.008).

## Order

2.1 → 2.2–2.4 → 2.5 → 3.

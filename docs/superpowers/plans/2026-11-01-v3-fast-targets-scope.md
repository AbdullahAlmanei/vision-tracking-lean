# Version 3 scope: targets up to 55 m/s (hinged camera, heading-locked yaw)

Status: scope only, not yet planned task by task. Date: 2026-11-01.

## Goal

Prove `master_sufficient3`: one inequality `MasterIneq3` under which a position-only
strategy keeps a target with speed band [vMin, vMax] = [20, 55] m/s in view in every
frame. The quadrotor is a valid rigid body throughout: frame, rates, four motors,
tilt, hinge range and hinge rate.

`scripts/budget_v3.py` must show that the inequality can be met at vMax = 55 m/s for a
realistic quadrotor.

## Why version 2 stops at about 30 m/s

At 55 m/s the drag the drone must cancel is c·v² ≈ 24 m/s², so the thrust axis tilts
about 70–80° from vertical. With the camera fixed down the thrust axis, the target leaves
the field of view once tilt + μ > α. That is a camera limit, not a thrust limit.

## Design (one design for the whole speed band, no mode switching)

- **Formation.** Unchanged: the drone flies the filtered target path offset by d straight
  up, and the line of sight is approximately −up.
- **Thrust axis.** b₃ = n = T/‖T‖, as in v2.
- **Yaw locked to the lateral axis.** Let ĥ be the planned horizontal heading, nrm(horiz vP),
  and let ℓ = up × ĥ. Then b₂ = nrm(ℓ − ⟪ℓ,n⟫n), the target's lateral direction projected
  into the rotor plane, and b₁ = b₂ × b₃.
  - The normalising denominator is √(1 − ⟪n,ℓ⟫²) = cos(bank), where
    tan(bank) ≤ lateral thrust / ‖T‖ ≤ (v²/R + εT)/‖T‖.
  - At 55 m/s, ‖T‖ is large because of drag, so the bank is small (≈ 25–30°).
  - The construction is non-singular at every pitch, including near 90°.
  - The heading denominator ‖horiz v‖ ≥ vMin·cos γ − εV is non-singular over the whole band.
  - I ruled out the "downhill" yaw of v1, which is singular at low tilt, and plain
    heading-plane yaw (b₁ = nrm(P_n ĥ)), which is singular as the pitch nears 90°.
- **Hinge.** The camera sits in the plane span(b₁, b₃), which is roughly vertical and
  contains the heading.
  - Set η to the in-plane direction of −up. This is η* = pitch − 90°, which lies in
    [−90°, 0] for forward pitch.
  - It is clamped to [hingeLo, hingeHi], to cover backward pitch when a slow target
    decelerates.
- **Visibility.** angle(cam, LOS) ≤ asin|⟪b₂,up⟫| + clampMiss + μ, with
  |⟪b₂,up⟫| ≤ |⟪n,ℓ⟫|. The requirement is bank + clampMiss + μ ≤ α.

## Rough prototype (scratch/proto_v4c.py; not the Lean budget)

Setup: the v2 quadrotor (1.5 kg, thrust/weight 6, c = 0.008), half-FOV 60°, d = 150 m,
target band 20–55 m/s, R = 350 m, and a lag-4 least-squares planner.

| Target | Result |
|---|---|
| jerk ≤ 1, dives ≤ 5–10°, aVert ≤ 1.5–3 | feasible; bank ≤ 26°, tilt ≤ 83°, Ω ≤ 1.2 rad/s |
| jerk 2, dive 5°, aVert 1.5 | feasible at 120 Hz with a 1.5 s planner window |
| jerk ≥ 3 | fails on mix_lo: torque exceeds the minimum collective thrust at the slow, diving end |
| dives ≥ 10° with aVert 3 | fails on tilt: at 55 m/s, drag in a dive eats the vertical thrust |

The camera is no longer the binding constraint. Two things are:

1. **Torque at realistic jerk.** An RC aircraft rolling into a 350 m turn at 55 m/s
   reaches 8.6 m/s² of lateral acceleration in about 1 s, so jerk is about 5–10 m/s³.
   - With only jerk bounded, the target may switch jerk sign every frame. The filtered
     thrust then has second differences of order TV·J/δ, and the torque budget pays for
     that.
   - A real aircraft cannot do this: its control surfaces are rate-limited.
2. **Fast dives.** Zlo = g − aVert − c·v²·sin γ − εT shrinks quickly at 55 m/s. This one
   is physics: copying a fast dive requires an almost horizontal thrust.

## Work items, in order

1. **Model: target snap limit.** Add `snap` (the second difference of acceleration,
   ≤ δ³·snap) to TargetParams and TargetTraj, the same way aVert was added.
   - Re-prove the second difference of the planned acceleration as ≤ (filter constant)·δ²·snap
     instead of TV·δ·J.
   - This is the main lever on mix_lo.
   - Decision for the user: the snap value to assume for the RC aircraft; about
     10–20 m/s⁴ is a guess.
2. **Speed-dependent budget.** A single worst case over the band is too loose, because the
   bank bound needs the large ‖T‖ of high speed. So MasterIneq3 quantifies over the local
   speed s ∈ [vMin − εV, vMax + εV]: ∀ s, cond(s), which is a one-dimensional check.
   - Per-step bounds are evaluated at s = ‖T.v k‖, with explicit slack for the speed
     drift over 2–3 steps (≤ 3δ(Amax + εD)).
3. **Heading lemmas** (Heading.lean):
   - horizontal speed ≥ vMin·cos γ, from climb_le;
   - the step and the cross-second-difference of ĥ and ℓ, via SharpNorm.
4. **Lateral-locked frame** (LateralFrame.lean):
   - b₂ = nrm(ℓ − ⟪ℓ,n⟫n), with denominator ≥ cos(bank_max);
   - frame-difference bounds;
   - lifting through the v1 `KinPlan` / `frameRotVec` route, since the frame is defined
     explicitly rather than by transport. The v1 rate bounds in terms of frame
     differences need to be re-checked for sharpness.
5. **Hinge** (Hinge.lean):
   - η = clamp(atan2(⟪−up,b₃⟫, ⟪−up,b₁⟫));
   - hinge-rate bound through the Lipschitz constant of atan2 and the frame differences;
   - the clamp-miss bound.
6. **Visibility:** angle(cam, LOS) ≤ asin(Lat/‖T‖) + clampMiss + μ.
7. **Budget3, MasterIneq3, master_sufficient3**, plus causality with lag 4 (the same
   pattern as Master2).
8. **scripts/budget_v3.py**, an exact mirror of Budget3. Report feasible regions at
   55 m/s against jerk, snap, dive angle and the quadrotor's inertia, arm and drag.
9. **Necessity (closes part of the P3 gap).** steady_turn_necessary: for a target in a
   steady level turn at speed v and radius R, any strategy holding a fixed formation must
   satisfy a bank/FOV condition. This extends `steady_formation_iff` from straight flight
   to turns, and pairs with the bank term in item 6.
10. Blueprint chapter, README, and an ledger entry.

## Out of scope (recorded caveats)

- Rotor thrust that depends on airspeed. At 55 m/s edgewise flow changes the motor
  thrust, while the model keeps fMotor constant. A natural v4 refinement is a derate
  fMotor(v).
- Formations other than overhead, such as trailing behind and above.
- Weaving drones, and the deferred minors M1, M3 and M4.

## Risks

- Item 2 (speed-dependent conditions) is the largest structural change; every bound
  gains a speed argument.
- Item 4: the v1 axis-angle rate bounds were loose (a factor of 2). If they are too loose,
  write the frame change as a composition: minimal rotation of n, then a rotation about
  n_{k+1}. That needs a composition lemma for `rotate`.
- If the snap limit does not rescue mix_lo at jerk 5–10, the remaining levers are design
  rules: lower inertia, a longer arm, and a lower minimum collective thrust (gentler
  dives).

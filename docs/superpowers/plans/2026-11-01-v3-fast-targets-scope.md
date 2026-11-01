# Version 3 scope: targets up to 55 m/s, approached from below (top camera, 30–70° up)

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

## Design: camera on top, drone underneath (user's choice, 2026-11-01)

**The vehicle.** The airframe has a cone-shaped head. The camera sits on one face near
the tip and looks *up*: its boresight is 30–70° above the rotor plane. In the existing
model this is `frameCam b₁ b₃ η = cos η·b₁ + sin η·b₃` with
`hingeLo = 30°, hingeHi = 70°`, a pitch hinge about b₂. A fixed camera is the case
`hingeLo = hingeHi`. **No model change is needed.**

**The formation.** The drone flies the filtered target path offset by d straight *down*,
so the line of sight is approximately +up. This is the overhead plan with the offset
`d • up` replaced by `-d • up`, so the v2 planner and causality proofs carry over.

**The camera faces backwards relative to travel.** This is forced by the physics.
- Let p be the drone's forward pitch, which is needed to fly fast: about 70–80° at
  55 m/s.
- If the camera face points *forward*, its elevation is η − p, which is ≤ 0 at speed. It
  can never look up.
- If it points *backward*, its angle measured from the rear horizon is p + η. Pitching
  nose-down for speed rotates the camera up and over:
  - at 20 m/s (p ≈ 5–20°) it looks back and up;
  - at 55 m/s (p ≈ 70°) it looks straight up, at η ≈ 20–30°.
- So speed helps this camera, the opposite of the belly camera.

**Yaw locked to the lateral axis.** Let ĥ = nrm(horiz vP) and ℓ = up × ĥ. Then
b₂ = nrm(−ℓ − ⟪−ℓ,n⟫n) and b₁ = b₂ × b₃, which points backwards.
- The denominator is cos(bank), where tan(bank) ≤ lateral thrust / ‖T‖.
- The construction is non-singular at every pitch and over the whole band. The
  heading denominator is ‖horiz v‖ ≥ vMin·cos γ − εV.

**Hinge.** η* = 90° − p is the in-plane hinge angle that points straight up. Set
η = clamp(η*, 30°, 70°), with clampMiss = dist(η*, [30°, 70°]).

**Visibility.** angle(cam, LOS) ≤ bank + clampMiss + μ, where bank comes from
|⟪b₂,up⟫| ≤ |⟪n,ℓ⟫|. The requirement is bank + clampMiss + μ ≤ α.

## Rough prototype (scratch/proto_under.py; not the Lean budget)

Setup: the v2 quadrotor, target band 20–55 m/s, R = 350 m, d ∈ {60, 100, 150} m (d barely
matters), and a lag-4 least-squares planner.

| Camera | Target | Result |
|---|---|---|
| hinge 30–70°, half-FOV 45° | jerk ≤ 2, dives ≤ 5° | feasible; pitch 1–79°, bank ≤ 29°, hinge miss ≤ 19° |
| hinge 30–70°, half-FOV 60° | jerk 1, dives ≤ 10° | feasible |
| hinge 30–70°, half-FOV 60° | jerk 2, dives 10° | fails on mix_lo (torque) |
| fixed at 50° or 60° | any | fails: pitch sweeps about 80° across 20–55 m/s, so the miss is 40–50° |

So the hinge is needed. A fixed top camera would need a speed-scheduled formation
instead: the drone sits ahead and below at low speed and slides to behind and below at
high speed. That offset follows the heading and costs about d·ω_T² of extra acceleration.
It is listed as an alternative, not planned.

The binding constraints are now torque at realistic jerk (5–10 m/s³ for a 55 m/s roll-in)
and fast dives. The camera is not binding.

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
   - η = clamp(atan2(⟪up,b₃⟫, ⟪up,b₁⟫), 30°, 70°);
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
   to turns, and pairs with the bank term in item 6. Also prove the "forward-facing top
   camera cannot see up at speed" lemma, which says the backward-facing camera is forced.
10. Blueprint chapter, README, and an ledger entry.

## Out of scope (recorded caveats)

- Rotor thrust that depends on airspeed. At 55 m/s edgewise flow changes the motor
  thrust, while the model keeps fMotor constant. A natural v4 refinement is a derate
  fMotor(v).
- Ground clearance: there is no ground plane in the model (M4). Flying under the target
  needs target altitude ≥ d + margin, which favours d ≈ 60–100 m.
- Speed-scheduled formations for a fixed top camera.
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

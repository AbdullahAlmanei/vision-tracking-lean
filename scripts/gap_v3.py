#!/usr/bin/env python3
"""The P3 gap for version 3: largest target top speed allowed by the necessary side
(NecIneq3: directional speed wall, Necessity3.lean) versus the sufficient side
(MasterIneq3, mirrored exactly by budget_v3.py)."""
import math
from budget_v3 import BASE, CAM, target, search

def dir_speed(Q, elev):
    """dirSpeed u for a unit direction at elevation `elev` (DirectionalSpeed.lean)."""
    maxAcc = 4 * Q['fMotor'] / Q['mass']
    ang_up = math.pi / 2 - elev
    reach = math.cos(max(0.0, ang_up - Q['tiltMax']))
    push = maxAcc * max(0.0, reach) - Q['g'] * math.sin(elev)
    return math.sqrt(max(0.0, push) / Q['drag'])

def nec_vmax(Q, climb):
    """NecIneq3: vMax <= dirSpeed u for every direction within the climb envelope."""
    n = 200
    return min(dir_speed(Q, -climb + 2 * climb * i / n) for i in range(n + 1))

def suf_vmax(Q, climb_deg, jerk):
    """Largest vMax (with vMin = 20) for which MasterIneq3 holds, by bisection."""
    def ok(v):
        P = dict(target(jerk, climb_deg), vMax=v)
        return search(P, Q, CAM) is not None
    lo, hi = 20.5, 120.0
    if not ok(lo): return None
    for _ in range(14):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if ok(mid) else (lo, mid)
    return lo

def avail_power(Q, s):
    """QuadParams.availPower (PowerWall.lean)."""
    F = 4 * Q['fMotor'] / Q['mass']
    return 0.0 if s <= 0 else min(F * s, F * F / (4 * Q['kn'] * s))

def power_vmax(Q, dt, n=4000):
    """NecPower (PowerWall.lean): the best line alpha - beta s above availPower - c s^3 on
    [0, speedEnv] caps vMax at (alpha + dt B^2 / 2) / beta."""
    S = Q['speedEnv']; c = Q['drag']; F = 4 * Q['fMotor'] / Q['mass']
    B = F + Q['kn'] * S ** 2 + Q['g'] + c * S ** 2
    ss = [S * i / n for i in range(n + 1)]
    hs = [avail_power(Q, x) - c * x ** 3 for x in ss]
    best = float('inf')
    for k in range(1, 3001):
        beta = k * 0.1
        alpha = max(h + beta * x for h, x in zip(hs, ss))
        best = min(best, (alpha + dt * B * B / 2) / beta)
    return best

if __name__ == '__main__' and len(__import__('sys').argv) > 1 and __import__('sys').argv[1] == 'kn':
    print('Rotor-disc normal force: power wall (NecPower) vs sufficient MasterIneq3, dt = 1/240')
    for kn in [0.005, 0.01, 0.02]:
        for qn, Q0 in {'base': BASE, 'kYaw .03, arm .22': dict(BASE, kYaw=0.03, arm=0.22)}.items():
            Q = dict(Q0, kn=kn)
            nec = power_vmax(Q, 1 / 240)
            for climb in [5, 10]:
                row = [f"k_n {kn:.3f} {qn:18s} {climb:2d} deg: necessary <= {nec:5.1f}"]
                for J in [1, 3, 5]:
                    s = suf_vmax(Q, climb, J)
                    row.append(f"jerk {J}: {s:5.1f}" if s else f"jerk {J}:  none")
                print("  " + " | ".join(row), flush=True)
    raise SystemExit

if __name__ == '__main__':
    quads = {'base': BASE, 'kYaw .03, arm .22': dict(BASE, kYaw=0.03, arm=0.22)}
    print('Largest target top speed (m/s): necessary wall vs sufficient MasterIneq3')
    for qn, Q in quads.items():
        for climb in [5, 10]:
            nec = nec_vmax(Q, math.radians(climb))
            row = [f"{qn:18s} climb/dive {climb:2d} deg: necessary <= {nec:5.1f}"]
            for J in [1, 2, 3, 5]:
                s = suf_vmax(Q, climb, J)
                row.append(f"jerk {J}: {s:5.1f}" if s else f"jerk {J}:  none")
            print("  " + " | ".join(row))

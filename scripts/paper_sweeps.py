#!/usr/bin/env python3
"""Design-lever sweeps for the engineering guide (docs/papers/).

Baseline: 1.5 kg quadrotor, thrust/weight 6, c = 0.008, k_n = 0.01, J = (0.012, 0.012, 0.02),
arm 0.18 m, yaw coefficient 0.02, camera hinge 30-70 deg, half-FOV 60 deg; target band 20 m/s
to vMax, R = 350 m, snap 15, aVert 1.5. For each lever value: the proved necessary wall
(NecPower, PowerWall.lean; dirSpeed for k_n = 0) and the largest vMax certified by
MasterIneq3 (budget_v3.py, exact mirror) at jerk 1/3/5 for +-5 and +-10 deg dives."""
import json, math, sys
from multiprocessing import Pool
from budget_v3 import BASE, CAM, target, search
from gap_v3 import power_vmax, nec_vmax

BASEQ = dict(BASE, kn=0.01)

def suf(Q, C, climb, J):
    ok = lambda v: search(dict(target(J, climb), vMax=v), Q, C) is not None
    lo, hi = 20.5, 120.0
    if not ok(lo): return None
    for _ in range(11):
        m = (lo + hi) / 2
        lo, hi = (m, hi) if ok(m) else (lo, m)
    return round(lo, 1)

def nec(Q):
    if Q['kn'] == 0: return round(min(nec_vmax(Q, math.radians(5)), nec_vmax(Q, math.radians(10))), 1)
    return round(power_vmax(Q, 1 / 240, n=1500), 1)

def cell(args):
    lever, val, Q, C, climb, J = args
    return (lever, val, climb, J, suf(Q, C, climb, J))

def levers():
    L = []
    W = BASEQ['mass'] * BASEQ['g']
    for tw in [4, 5, 6, 7, 8]: L.append(('thrust/weight', tw, dict(BASEQ, fMotor=tw * W / 4), CAM))
    for kn in [0.0, 0.005, 0.01, 0.02]: L.append(('k_n', kn, dict(BASEQ, kn=kn), CAM))
    for c in [0.006, 0.008, 0.010]: L.append(('drag c', c, dict(BASEQ, drag=c), CAM))
    for s in [0.7, 1.0, 1.4]:
        L.append(('inertia scale', s, dict(BASEQ, Jx=0.012 * s, Jy=0.012 * s, Jz=0.02 * s), CAM))
    for a in [0.15, 0.18, 0.22]: L.append(('arm (m)', a, dict(BASEQ, arm=a), CAM))
    for k in [0.015, 0.02, 0.03]: L.append(('yaw coeff', k, dict(BASEQ, kYaw=k), CAM))
    for lo, hi in [(30, 70), (20, 80), (40, 60), (50, 50)]:
        L.append(('hinge (deg)', f"{lo}-{hi}", BASEQ, dict(CAM, hingeLo=math.radians(lo), hingeHi=math.radians(hi))))
    for f in [45, 60]: L.append(('half-FOV (deg)', f, BASEQ, dict(CAM, halfFov=math.radians(f))))
    return L

if __name__ == '__main__':
    L = levers()
    jobs = [(n, v, Q, C, cl, J) for (n, v, Q, C) in L for cl in [5, 10] for J in [1, 3, 5]]
    with Pool() as p:
        res = p.map(cell, jobs)
        necs = p.map(nec, [Q for (_, _, Q, _) in L])
    out = []
    for (n, v, Q, C), nv in zip(L, necs):
        row = dict(lever=n, value=v, necessary=nv)
        for (ln, lv, cl, J, s) in res:
            if ln == n and lv == v: row[f"d{cl}_j{J}"] = s
        out.append(row)
        print(row, flush=True)
    json.dump(out, open('paper_sweeps.json', 'w'), indent=1)

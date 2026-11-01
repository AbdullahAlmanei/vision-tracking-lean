#!/usr/bin/env python3
"""Numerical mirror of VisionTracking/Budget3.lean (MasterIneq3: camera on top, drone underneath,
lateral-locked yaw, speed-dependent budget). Every quantity follows the Lean definition exactly.

The planner is the sparse three-tap quadratic-exact filter with taps at lags 4, (4+N)/2 and N
(minimal sum |h_i| for its window), which satisfies the FIR fields and the lag-4 hypothesis.
"""
import math
import numpy as np

def tap3(L, N):
    m = (L + N) // 2
    idx = np.array([L, m, N], float)
    w = np.linalg.solve(np.vstack([idx ** 0, idx, idx ** 2]), np.array([1.0, 0.0, 0.0]))
    h = np.zeros(N + 1); h[L], h[m], h[N] = w
    return h

def fir_consts(h):
    M = len(h) - 1
    def tail(g): return np.array([g[m + 1:M + 1].sum() for m in range(M + 1)])
    T1 = tail(h); T2 = tail(T1); T3 = tail(T2)
    return dict(G1=abs(T1).sum(), G2=abs(T2).sum(), G3=abs(T3).sum(), H0=abs(h).sum())

def at_speed(P, Q, C, dt, F, d, s):
    """Budget3 quantities at speed s; returns (dict of conditions, dict of values)."""
    g, c = Q['g'], Q['drag']
    J, S, R = P['jerk'], P['snap'], P['R']
    sg, cg = math.sin(P['climb']), math.cos(P['climb'])
    Amax = P['aTan'] + P['vMax'] ** 2 / R
    eD = F['G1'] * dt * J; eV = F['G2'] * dt ** 2 * J; rho = F['G3'] * dt ** 3 * J
    sHi = min(P['vMax'], s + 2 * dt * Amax); sLo = max(P['vMin'], s - 2 * dt * Amax)
    A = P['aTan'] + sHi ** 2 / R
    eT = eD + c * (2 * sHi + eV) * eV
    Zlo = g - P['aVert'] - c * sHi ** 2 * sg - eT
    Zhi = g + P['aVert'] + c * sHi ** 2 * sg + eT
    Fw = c * sLo ** 2 - P['aTan'] - g * sg - eT
    Tlo = max(Zlo, Fw); Thi = g + A + c * sHi ** 2 + eT; Hhi = A + c * sHi ** 2 + eT
    vh = sLo * cg - eV
    ok = dict(zlo_pos=Zlo > 0, vh_pos=vh > 0)
    if not all(ok.values()): return ok, {}
    Lat = sHi ** 2 / R + eD + A * (eV / vh)
    sb = Lat / Tlo
    ok['sb_lt'] = sb < 1
    if not ok['sb_lt']: return ok, {}
    M = math.sqrt(1 - sb ** 2)
    dT = dt * (F['H0'] * J + 2 * c * (sHi + eV) * (A + eD))
    d2T = F['H0'] * dt ** 2 * S + c * (2 * (sHi + eV) * F['H0'] * dt ** 2 * J + 4 * dt ** 2 * (A + eD) ** 2)
    dn = dT / Tlo; xn = d2T / Tlo + 2 * dT ** 2 / Tlo ** 2; d2n = 2 * d2T / Tlo + 6 * dT ** 2 / Tlo ** 2
    dl = dt * (A + eD) / vh; d2l = 2 * (dt ** 2 * F['H0'] * J) / vh + 6 * dl ** 2
    dbc = (2 * dl + 2 * dn) / M + dn
    th = math.sqrt(dn ** 2 + ((dl + sb * dn) / M) ** 2)
    ok['near'] = dbc <= 1; ok['theta_lt'] = th < 1
    if th >= 1: return ok, {}
    G = 1 / math.sqrt(1 - th ** 2)
    db = G * th
    tw = (dl + sb * dn) / M                                      # latTw
    core = (d2l + sb * xn + 2 * (dl + dn) * dn) / M + 2 * (sb * (dl + dn) / M ** 3) * (dl + sb * dn)
    rp2 = xn + math.sqrt(2) * dn * (tw + db ** 2 + dn * db / 2)    # latRpSharp
    yaw2 = core + dn ** 2 / 2 + db ** 2 * (tw + db ** 2 / 2)       # latYawSharp
    da = math.sqrt(rp2 ** 2 + yaw2 ** 2)
    Om = G * th / dt; dOm = (G * da + (G - 1) * th) / dt; dOmz = (G * yaw2 + (G - 1) * th) / dt
    Jxy = max(Q['Jx'], Q['Jy']); Jg = max(abs(Q['Jz'] - Q['Jy']), abs(Q['Jx'] - Q['Jz']))
    dOmrp = (G * abs(rp2) + (G - 1) * th) / dt
    trp = Jxy * dOmrp / dt + Jg * Om ** 2
    tyaw = Q['Jz'] * dOmz / dt + abs(Q['Jy'] - Q['Jx']) * Om ** 2
    Nlo = c * sLo ** 2 * cg - A - Thi * (eV / vh) - eT
    plo = math.atan(Nlo / Zhi if Nlo >= 0 else Nlo / (Zlo * M))
    phi = math.atan(Hhi / (Zlo * M))
    miss = max(0, max((math.pi / 2 - plo) - C['hingeHi'], C['hingeLo'] - (math.pi / 2 - phi)))
    camOff = math.acos(M * math.cos(miss)) if miss <= math.pi / 2 else float('inf')
    mu = math.asin(rho / d) if rho < d else float('inf')
    hstep = math.pi / 2 * (db + dn) / M
    need = trp / (2 * Q['arm']) + tyaw / (4 * Q['kYaw'])
    # collective with the rotor-disc normal force (Budget3.sLp/sHp/VTlo/Clo/Chi)
    kn = Q.get('kn', 0.0); sLp = sLo - eV; sHp = sHi + eV
    VTlo = c * sLp ** 3 - sHp * (A + eD) - g * (sHi * sg + eV)
    Clo = Tlo + kn * min(sLp * VTlo / Thi, sHp * VTlo / Tlo)
    Chi = Thi + kn * sHp ** 2
    ok.update(tilt=math.atan(Hhi / Zlo) <= Q['tiltMax'], rate=Om <= Q['rateMax'],
              mix_lo=need <= Q['mass'] * Clo / 4, mix_hi=Q['mass'] * Chi / 4 + need <= Q['fMotor'],
              miss_le=miss <= math.pi / 2, see=camOff + mu <= C['halfFov'], hinge=hstep <= dt * C['hingeRate'])
    return ok, dict(bank=math.degrees(math.asin(sb)), miss=math.degrees(miss), camOff=math.degrees(camOff),
                    Om=Om, angacc=dOm / dt, tau_rp=trp, tau_yaw=tyaw, need=need, avail=Q['mass'] * Tlo / 4,
                    hinge_rate=hstep / dt)

def master_ineq3(P, Q, C, dt, F, d, ns=60):
    eV = F['G2'] * dt ** 2 * P['jerk']; rho = F['G3'] * dt ** 3 * P['jerk']
    detect = P['size'] / (2 * math.tan(C['minPx'] * C['fovH'] / (2 * C['widthPx'])))
    fails = set(); worst = {}
    if P['vMax'] + eV > Q['speedEnv']: fails.add('speed')
    if rho >= d: fails.add('rho_lt')
    if d + rho > detect: fails.add('range')
    for i in range(ns + 1):
        s = P['vMin'] + (P['vMax'] - P['vMin']) * i / ns
        ok, vals = at_speed(P, Q, C, dt, F, d, s)
        fails |= {k for k, v in ok.items() if not v}
        for k, v in vals.items(): worst[k] = max(worst.get(k, -1e9), v) if k != 'avail' else min(worst.get(k, 1e9), v)
    return fails, worst

BASE = dict(g=9.81, mass=1.5, Jx=0.012, Jy=0.012, Jz=0.02, arm=0.18, fMotor=6 * 1.5 * 9.81 / 4,
            kYaw=0.02, drag=0.008, kn=0.0, tiltMax=math.radians(85), rateMax=20.0, speedEnv=90.0)
CAM = dict(halfFov=math.radians(60), fovH=math.radians(120), widthPx=3840, minPx=8,
           hingeLo=math.radians(30), hingeHi=math.radians(70), hingeRate=8.0)

def target(jerk, climb_deg, aVert=1.5, snap=15.0):
    return dict(vMin=20.0, vMax=55.0, R=350.0, aTan=2.0, jerk=jerk, snap=snap, aVert=aVert,
                climb=math.radians(climb_deg), size=2.5)

def search(P, Q, C, d=100.0):
    for hz in [120, 240, 480]:
        for win in [0.5, 1.0, 2.0, 3.0]:
            F = fir_consts(tap3(4, max(8, int(round(win * hz)))))
            f, W = master_ineq3(P, Q, C, 1 / hz, F, d)
            if not f: return hz, win, W
    return None

if __name__ == '__main__':
    print('Target 20-55 m/s, R = 350 m, snap 15 m/s^4, aVert 1.5; camera on top (hinge 30-70 deg up),')
    print('half-FOV 60 deg, standoff 100 m below. Quad 1.5 kg, thrust/weight 6, c_D 0.008.\n')
    quads = {'base (J .012/.012/.02, arm .18, kYaw .02)': {},
             'kYaw .03, arm .22': dict(kYaw=0.03, arm=0.22)}
    for qn, ch in quads.items():
        Q = dict(BASE, **ch)
        print(qn)
        for climb in [5, 10]:
            for J in [1, 2, 3, 5]:
                r = search(target(J, climb), Q, CAM)
                if r:
                    hz, win, W = r
                    print(f"  dive {climb:2d} deg, jerk {J}: MasterIneq3 holds at {hz} Hz / {win} s window; "
                          f"bank<={W['bank']:.0f}, cam<={W['camOff']:.0f} deg, Omega<={W['Om']:.1f}, "
                          f"motor need {W['need']:.2f} N vs {W['avail']:.2f} N, hinge<={W['hinge_rate']:.1f} rad/s")
                else:
                    F = fir_consts(tap3(4, 240)); f, W = master_ineq3(target(J, climb), Q, CAM, 1 / 240, F, 100.0)
                    print(f"  dive {climb:2d} deg, jerk {J}: fails {sorted(f)} (240 Hz / 1 s: need {W.get('need',0):.2f} vs {W.get('avail',0):.2f} N)")

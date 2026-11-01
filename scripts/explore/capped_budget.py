#!/usr/bin/env python3
"""Payoff of the capped tracker: the version-3 budget with the planned jerk/snap replaced by the
tracker's caps, and the tracker's worst lags (position E, velocity V, acceleration lag, planned
acceleration) taken from capped_table.json (adversarial study, one axis). Speed-scheduled: at
each target speed the caps are chosen from the grid. Prototype only (bounds are approximate
where noted)."""
import math, json, os, sys
here = os.path.dirname(__file__); sys.path.insert(0, os.path.join(here, '..'))
import budget_v3 as b
TAB = json.load(open(os.path.join(here, 'capped_table.json')))
AGRID = [1.5, 3.5, 5.5, 8.0, 10.6]
CAPS = [(3, 5), (4, 6), (5, 10), (6, 12)]

def lookup(J, S, A, Jc, Sc):
    Ag = next((x for x in AGRID if x >= A - 1e-9), None)
    if Ag is None: return None
    return TAB.get(f"{J},{S},{Ag},{Jc},{Sc}")

def at_speed(P, Q, C, dt, F, d, s, caps_h, caps_v):
    g, c = Q['g'], Q['drag']; J, S, R = P['jerk'], P['snap'], P['R']
    sg, cg = math.sin(P['climb']), math.cos(P['climb'])
    Amax = P['aTan'] + P['vMax'] ** 2 / R
    rho = F['G3'] * dt ** 3 * J
    sHi = min(P['vMax'], s + 2 * dt * Amax); sLo = max(P['vMin'], s - 2 * dt * Amax)
    Ah = P['aTan'] + sHi ** 2 / R
    th_ = lookup(J, S, Ah, *caps_h); tv_ = lookup(J, S, P['aVert'], *caps_v)
    if th_ is None or tv_ is None: return {'table': False}, {}
    Eh, Vh, Aph, Alh = th_['E'], th_['V'], th_['Aplan'], th_['Alag']
    Ev, Vv, Apv = tv_['E'], tv_['V'], tv_['Aplan']
    Jp = math.sqrt(2 * caps_h[0] ** 2 + caps_v[0] ** 2); Sp = math.sqrt(2 * caps_h[1] ** 2 + caps_v[1] ** 2)
    Vt = math.sqrt(2 * Vh ** 2 + Vv ** 2); Ap = math.sqrt(2 * Aph ** 2 + Apv ** 2)
    wHi = sHi + Vt; wLo = sLo - Vt
    Zlo = g - Apv - c * wHi * (sHi * sg + Vv); Zhi = g + Apv + c * wHi * (sHi * sg + Vv)
    Fw = c * wLo ** 2 * cg - P['aTan'] - Alh - P['aVert'] * sg
    Tlo = max(Zlo, Fw); Thi = g + Ap + c * wHi ** 2; Hhi = math.sqrt(2) * Aph + c * wHi ** 2
    vh = wLo * cg
    ok = dict(zlo=Zlo > 0, vh=vh > 0)
    if not all(ok.values()): return ok, {}
    Lat = sHi ** 2 / R + Alh; sb = Lat / Tlo; ok['sb'] = sb < 1
    if sb >= 1: return ok, {}
    M = math.sqrt(1 - sb * sb)
    dT = dt * (Jp + 2 * c * wHi * Ap)
    d2T = dt ** 2 * Sp + c * (2 * wHi * dt ** 2 * Jp + 4 * dt ** 2 * Ap ** 2)
    dn = dT / Tlo; xn = d2T / Tlo + 2 * dT ** 2 / Tlo ** 2; d2n = 2 * d2T / Tlo + 6 * dT ** 2 / Tlo ** 2
    dl = dt * math.sqrt(2) * Aph / vh; d2l = 2 * dt ** 2 * math.sqrt(2) * caps_h[0] / vh + 6 * dl ** 2
    dbc = (2 * dl + 2 * dn) / M + dn
    th = math.sqrt(dn ** 2 + ((dl + sb * dn) / M) ** 2); ok['near'] = dbc <= 1; ok['th'] = th < 1
    if th >= 1: return ok, {}
    G = 1 / math.sqrt(1 - th ** 2); db = G * th
    rp2 = xn + d2n * db + 2 * dn * db; yaw2 = b.lat_dyaw(sb, dn, dl, d2n, xn, d2l, db)
    Om = G * th / dt; dOmz = (G * yaw2 + (G - 1) * th) / dt; dOmrp = (G * abs(rp2) + (G - 1) * th) / dt
    Jxy = max(Q['Jx'], Q['Jy']); Jg = max(abs(Q['Jz'] - Q['Jy']), abs(Q['Jx'] - Q['Jz']))
    trp = Jxy * dOmrp / dt + Jg * Om ** 2; tyaw = Q['Jz'] * dOmz / dt + abs(Q['Jy'] - Q['Jx']) * Om ** 2
    Nlo = Fw
    plo = math.atan(Nlo / Zhi if Nlo >= 0 else Nlo / (Zlo * M)); phi = math.atan(Hhi / (Zlo * M))
    miss = max(0, max((math.pi / 2 - plo) - C['hingeHi'], C['hingeLo'] - (math.pi / 2 - phi)))
    camOff = math.acos(M * math.cos(miss)) if miss <= math.pi / 2 else 9
    E = math.sqrt(2 * Eh ** 2 + Ev ** 2) + rho
    mu = math.asin(E / d) if E < d else 9
    need = trp / (2 * Q['arm']) + tyaw / (4 * Q['kYaw'])
    detect = P['size'] / (2 * math.tan(C['minPx'] * C['fovH'] / (2 * C['widthPx'])))
    ok.update(tilt=math.atan(Hhi / Zlo) <= Q['tiltMax'], rate=Om <= Q['rateMax'],
              mix_lo=need <= Q['mass'] * Tlo / 4, mix_hi=Q['mass'] * Thi / 4 + need <= Q['fMotor'],
              see=camOff + mu <= C['halfFov'], hinge=math.pi / 2 * (db + dn) / M <= dt * C['hingeRate'],
              range=d + E <= detect)
    return ok, dict(need=need, avail=Q['mass'] * Tlo / 4, camOff=math.degrees(camOff), mu=math.degrees(mu), E=E)

def feasible(P, Q, C, dt, F, d, ns=30):
    """Speed-scheduled caps: at each speed some cap pair must work."""
    choice = []
    for i in range(ns + 1):
        s = P['vMin'] + (P['vMax'] - P['vMin']) * i / ns
        good = None
        for ch in CAPS:
            for cv in CAPS:
                ok, W = at_speed(P, Q, C, dt, F, d, s, ch, cv)
                if ok and all(ok.values()): good = (ch, cv, W); break
            if good: break
        if not good: return False, s
        choice.append((s, good[0], good[1]))
    return True, choice

if __name__ == '__main__':
    print("Capped tracker (speed-scheduled caps) vs the tight formation, target 20-55 m/s.")
    for qn, Q in [('base', b.BASE), ('tuned', dict(b.BASE, kYaw=0.03, arm=0.22))]:
        for climb in [5, 10]:
            for J, S in [(5, 15), (10, 30)]:
                P = dict(b.target(J, climb), snap=S)
                res = None
                for d in [100, 150, 250]:
                    for hz in [120, 240]:
                        for win in [0.5, 1.0]:
                            F = b.fir_consts(b.tap3(4, int(win * hz)))
                            okk, info = feasible(P, Q, b.CAM, 1 / hz, F, d)
                            if okk: res = (d, hz, win, info); break
                        if res: break
                    if res: break
                if res:
                    caps = sorted(set((c[1], c[2]) for c in res[3]))
                    print(f"  {qn:5s} dive {climb:2d} jerk {J:2d}: holds (d={res[0]} m, {res[1]} Hz); caps used {caps}")
                else:
                    print(f"  {qn:5s} dive {climb:2d} jerk {J:2d}: fails (first failing speed {info:.0f} m/s)")

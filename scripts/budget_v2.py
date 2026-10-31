#!/usr/bin/env python3
"""Numerical mirror of VisionTracking/Budget2.lean (MasterIneq2, yaw-free down camera).

Every quantity follows the Lean definition exactly. The planner is the least-squares
quadratic extrapolator with lag 4 frames over a window of W frames (W = window_s / dt),
which satisfies the FIR fields and the lag hypothesis of master_sufficient2.
"""
import math
import numpy as np

def ls_filter(L, W):
    lags = np.arange(L, L + W, dtype=float)
    X = np.vstack([np.ones(W), lags, lags ** 2]).T
    h = np.array([1.0, 0.0, 0.0]) @ np.linalg.pinv(X)
    full = np.zeros(L + W); full[L:] = h
    return full                       # indices 0..M, M = L+W-1

def fir_consts(h):
    M = len(h) - 1
    def tail(g):                      # tailSum g (M+1) m = sum_{i in Ico(m+1, M+1)} g i
        return np.array([g[m + 1:M + 1].sum() for m in range(M + 1)])
    T1 = tail(h); T2 = tail(T1); T3 = tail(T2)
    hp = np.append(h, 0.0)
    return dict(G1=abs(T1).sum(), G2=abs(T2).sum(), G3=abs(T3).sum(), H0=abs(h).sum(),
                TV=abs(hp[0]) + sum(abs(hp[i + 1] - hp[i]) for i in range(M + 1)), M=M)

def master_ineq2(P, Q, C, dt, F, d):
    g, c = Q['g'], Q['drag']
    J, vM, vm = P['jerk'], P['vMax'], P['vMin']
    Amax = P['aTan'] + vM ** 2 / P['R']
    sg = math.sin(P['climbMax'])
    eD = F['G1'] * dt * J; eV = F['G2'] * dt ** 2 * J; rho = F['G3'] * dt ** 3 * J
    Vb = vM + eV; eT = eD + c * (2 * vM + eV) * eV
    Zlo = g - P['aVert'] - c * vM ** 2 * sg - eT
    Fhi = g + Amax + c * vM ** 2 + eT
    Hhi = Amax + c * vM ** 2 + eT
    out = dict(Zlo_pos=Zlo > 0, eV_lt=eV < vm, fine=dt * c * Q['speedEnv'] <= 0.5)
    if Zlo <= 0:
        return out, {}
    Thi = math.atan(Hhi / Zlo)
    dT = dt * (F['H0'] * J + 2 * c * Vb * (Amax + eD))
    d2T = F['TV'] * dt * J + c * (2 * Vb * F['H0'] * dt ** 2 * J + 4 * dt ** 2 * (Amax + eD) ** 2)
    D3 = dT / Zlo
    out['D3_lt'] = D3 < 1
    if D3 >= 1:
        return out, dict(D3=D3)
    X = d2T / Zlo + 2 * dT ** 2 / Zlo ** 2
    sq = math.sqrt(1 - D3 ** 2)
    th = D3 / sq; dw = 3 * X / sq
    Om = th / dt; dOm = (dw + 3 * th ** 2) / dt
    Jm = max(Q['Jx'], Q['Jy'], Q['Jz'])
    trp = Jm * dOm / dt + Jm * Om ** 2
    tyaw = abs(Q['Jy'] - Q['Jx']) * Om ** 2
    mu = math.asin(rho / d) if rho < d else float('inf')
    detect = P['size'] / (2 * math.tan(C['minPx'] * C['fovH'] / (2 * C['widthPx'])))
    out.update(
        tilt=Thi <= Q['tiltMax'], speed=Vb <= Q['speedEnv'], rate=Om <= Q['rateMax'],
        mix_lo=trp / (2 * Q['arm']) + tyaw / (4 * Q['kYaw']) <= Q['mass'] * Zlo / 4,
        mix_hi=Q['mass'] * Fhi / 4 + trp / (2 * Q['arm']) + tyaw / (4 * Q['kYaw']) <= Q['fMotor'],
        rho_lt=rho < d, see=Thi + mu <= C['halfFov'], range=d + rho <= detect)
    return out, dict(Thi=math.degrees(Thi), Om=Om, angacc=dOm / dt, tau=trp, rho=rho, eD=eD,
                     Zlo=Zlo, D3=D3, detect=detect)

QUAD = dict(g=9.81, mass=1.5, Jx=0.012, Jy=0.012, Jz=0.02, arm=0.18, fMotor=6 * 1.5 * 9.81 / 4,
            kYaw=0.02, drag=0.008, tiltMax=math.radians(85), rateMax=20.0, speedEnv=90.0)
CAMERA = dict(halfFov=math.radians(60), fovH=math.radians(120), widthPx=3840, minPx=8)

def target(vMax, jerk, aVert, climb_deg=10.0):
    return dict(vMin=0.6 * vMax, vMax=vMax, R=350.0, aTan=2.0, jerk=jerk, aVert=aVert,
                climbMax=math.radians(climb_deg), size=2.5)

if __name__ == '__main__':
    print('Quad: 1.5 kg, thrust/weight 6, c_D = 0.008, J = (0.012, 0.012, 0.02), arm 0.18 m')
    print('Camera: half-FOV 60 deg, 4K across 120 deg, 8-pixel detection; standoff d = 150 m\n')
    print(f"{'vMax':>5} {'jerk':>5} {'aVert':>5} | feasible (frame rate / planner window): tilt, Ω, angular acc")
    for aV in [3.0, 1.5, 0.75]:
        for J in [5.0, 2.0, 1.0]:
            for vM in [15.0, 20.0, 25.0, 30.0]:
                P = target(vM, J, aV)
                hits = []
                for hz in [60, 120, 240]:
                    for win in [0.3, 0.5, 1.0, 1.5, 2.0]:
                        F = fir_consts(ls_filter(4, int(round(win * hz))))
                        ok, info = master_ineq2(P, QUAD, CAMERA, 1 / hz, F, 150.0)
                        if ok and all(ok.values()) and len(ok) > 4:
                            hits.append(f"{hz}Hz/{win}s: {info['Thi']:.0f}°, {info['Om']:.1f}/s, "
                                        f"{info['angacc']:.0f}/s²")
                            break
                print(f"{vM:5.1f} {J:5.1f} {aV:5.2f} | " + (hits[0] if hits else '—')
                      + (f"  (+{len(hits)-1} more rates)" if len(hits) > 1 else ''))

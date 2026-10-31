#!/usr/bin/env python3
"""Evaluate the master budget (VisionTracking/Budget.lean) numerically.

Mirrors every definition in Budget.lean exactly, for the reference fixed-wing target
and two quadrotors, over the smoothing family h^(N) (lag (3N+1)/2, odd N >= 3) and
frame rates. Prints which MasterIneq conditions hold and the binding ones.
"""
import math

def smooth_filter(N):
    """h^(N): weights (6-c, -8+2c, 3-c)/N on three consecutive blocks of length N
    starting at lag L = (3N+1)/2, with c = (N^2-1)/(24 N^2)."""
    assert N % 2 == 1
    L = (3 * N + 1) // 2
    c = (N * N - 1) / (24 * N * N)
    w = [6 - c, -8 + 2 * c, 3 - c]
    h = {}
    for b in range(3):
        for j in range(N):
            h[L + b * N + j] = w[b] / N
    M = L + 3 * N - 1
    return h, M

def fir_consts(h, M):
    hs = [h.get(i, 0.0) for i in range(M + 2)]
    s0 = sum(hs[i] for i in range(M + 1))
    s1 = sum(i * hs[i] for i in range(M + 1))
    s2 = sum(i * i * hs[i] for i in range(M + 1))
    H0 = sum(abs(hs[i]) for i in range(M + 1))
    H1 = sum(abs(hs[i]) * i for i in range(M + 1))
    H2 = sum(abs(hs[i]) * i * (i + 1) / 2 for i in range(M + 1))
    H3 = sum(abs(hs[i]) * i * (i + 1) * (i + 2) / 6 for i in range(M + 1))
    TV = abs(hs[0]) + sum(abs(hs[i + 1] - hs[i]) for i in range(M + 1))
    lag = min(i for i in range(M + 1) if hs[i] != 0)
    return dict(sum=s0, m1=s1, m2=s2, H0=H0, H1=H1, H2=H2, H3=H3, TV=TV, lag=lag)

def budget(P, Q, Cm, delta, F, d):
    g, c = Q['g'], Q['drag']
    Amax = P['aTan'] + P['vMax'] ** 2 / P['R']
    sg, cg = math.sin(P['gamma']), math.cos(P['gamma'])
    eD = F['H1'] * delta * P['jerk']
    eV = F['H2'] * delta ** 2 * P['jerk']
    rho = F['H3'] * delta ** 3 * P['jerk']
    Vb = P['vMax'] + eV
    eT = eD + c * (2 * P['vMax'] + eV) * eV
    Zlo = g - Amax - c * P['vMax'] ** 2 * sg - eT
    Zhi = g + Amax + c * P['vMax'] ** 2 * sg + eT
    Fhi = g + Amax + c * P['vMax'] ** 2 + eT
    Hhi = Amax + c * P['vMax'] ** 2 + eT
    Hstar = c * P['vMin'] ** 2 * cg - P['aTan'] - P['vMax'] ** 2 / P['R'] * sg
    Hlo = Hstar - eT
    r = {}
    r.update(eD=eD, eV=eV, rho=rho, Zlo=Zlo, Hlo=Hlo, Hstar=Hstar, Fhi=Fhi)
    if Zlo <= 0 or Hlo <= 0:
        return r
    Th_hi = math.atan(Hhi / Zlo); Th_lo = math.atan(Hlo / Zhi)
    dT = delta * (F['H0'] * P['jerk'] + 2 * c * Vb * (Amax + eD))
    d2T = F['TV'] * delta * P['jerk'] + c * (2 * Vb * F['H0'] * delta ** 2 * P['jerk']
                                              + 4 * delta ** 2 * (Amax + eD) ** 2)
    D3 = 2 * dT / Zlo
    D3p = 2 * d2T / Zlo + 6 * dT ** 2 / Zlo ** 2
    mh = Hlo / Fhi
    D1b = 4 * D3 / mh
    D1bp = (4 * D3p + 4 * D3 ** 2) / mh + 24 * D3 ** 2 / mh ** 2
    D1 = D3 + D1b
    D2 = D1bp + D3p + 2 * D3 * D1b
    r.update(Th_lo=Th_lo, Th_hi=Th_hi, dT=dT, d2T=d2T, D1=D1, D2=D2)
    if 2 * D1 >= 1:
        return r
    sq = math.sqrt(1 - (2 * D1) ** 2)
    Om = 2 * D1 / (delta * sq)
    dOm = 18 * (D2 + D1 ** 2) / (delta * sq)
    Jmax = max(Q['J'])
    tau = Jmax * dOm / delta + Jmax * Om ** 2
    mixK = 1 / (2 * Q['arm']) + 1 / (4 * Q['kYaw'])
    mu = math.asin(rho / d) if rho < d else float('inf')
    alpha = Cm['alpha']
    detect = P['size'] / (2 * math.tan(Cm['n'] * Cm['Phi'] / (2 * Cm['W'])))
    r.update(Om=Om, dOm=dOm, tau=tau, mu=mu, detect=detect,
             tilt=Th_hi <= Q['tiltMax'],
             rate=Om <= Q['rateMax'],
             mix_lo=tau * mixK <= Q['mass'] * Zlo / 4,
             mix_hi=Q['mass'] * Fhi / 4 + tau * mixK <= Q['fMotor'],
             speed=Vb <= Q['speedEnv'],
             mu_le=mu <= alpha,
             range=d + rho <= detect,
             hinge_lo_need=Th_lo - math.pi / 2 + alpha - mu,
             hinge_hi_need=Th_hi - math.pi / 2 - alpha + mu)
    return r

TARGET = dict(vMin=20.0, vMax=51.4, R=350.0, aTan=2.0, jerk=15.0,
              gamma=math.radians(30), size=2.5)
CAMERA = dict(alpha=math.radians(45), Phi=math.radians(90), W=1920, n=8)
QUADS = {
    'racing (thrust/weight 4)': dict(g=9.81, mass=1.0, J=[0.004, 0.004, 0.007], arm=0.12,
        fMotor=4 * 9.81 / 4, kYaw=0.02, drag=0.0237, tiltMax=math.radians(80),
        rateMax=20.0, speedEnv=80.0),
    'heavy-lift (thrust/weight 6, low drag)': dict(g=9.81, mass=2.0, J=[0.02, 0.02, 0.035],
        arm=0.25, fMotor=6 * 2 * 9.81 / 4, kYaw=0.02, drag=0.012, tiltMax=math.radians(80),
        rateMax=20.0, speedEnv=90.0),
}

if __name__ == '__main__':
    for name, Q in QUADS.items():
        print(f'== {name}')
        for gam in [30, 15, 0]:
            P = dict(TARGET, gamma=math.radians(gam))
            for hz in [30, 60, 120]:
                delta = 1 / hz
                best = None
                for N in range(3, 80, 2):
                    h, M = smooth_filter(N)
                    F = fir_consts(h, M)
                    r = budget(P, Q, CAMERA, delta, F, d=150.0)
                    keys = ['tilt', 'rate', 'mix_lo', 'mix_hi', 'speed', 'mu_le', 'range']
                    if 'tilt' in r:
                        ok = [k for k in keys if r[k]]
                        score = len(ok)
                        if best is None or score > best[0]:
                            best = (score, N, r, [k for k in keys if not r[k]])
                    elif best is None:
                        best = (0, N, r, ['Zlo/Hlo/D1'])
                score, N, r, fails = best
                print(f'  climb {gam:2d}°, {hz:3d} Hz: best N={N:2d} '
                      f'fails={fails} Zlo={r.get("Zlo",0):.2f} Hstar={r.get("Hstar",0):.2f} '
                      f'D1={r.get("D1",float("nan")):.3g} tau={r.get("tau",float("nan")):.3g} '
                      f'rho={r.get("rho",0):.3g}')
    h, M = smooth_filter(5); print('filter N=5 consts:', {k: round(v, 4) for k, v in fir_consts(h, M).items()})

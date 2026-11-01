#!/usr/bin/env python3
"""Winged quad, 3D quasi-steady prototype with a one-axis camera hinge.

Attitude: coordinated (zero side-slip, b2 ⟂ v). Unknowns: tilt beta of b3 toward the velocity,
bank phi about the velocity, motor thrust T. Solved so that T b3 + aero = a + g e3 (per mass).
Aero: cambered lateral arms (span b2, chord b1, nose-up incidence iw; lift polar to stall, flat
plate past stall), symmetric fore-aft arms (cross-flow drag on <v, b3>), body drag.
Camera: hinge about b2, boresight cos(eta) b1 + sin(eta) b3, b1 pointing backwards; aims at e3.
"""
import math, numpy as np
from scipy.optimize import fsolve

RHO = 1.225; G = 9.81

def unit(x): return x / np.linalg.norm(x)

def section(W, alpha):
    lin_CL = W['CL0'] + W['a'] * alpha
    lin = (lin_CL, W['CD0'] + W['k'] * lin_CL ** 2)
    CN = 1.2 * math.sin(alpha)
    plate = (CN * math.cos(alpha), W['CD0'] + CN * math.sin(alpha))
    t = min(1.0, max(0.0, (abs(alpha) - W['alpha_s']) / math.radians(5)))
    return (lin[0] * (1 - t) + plate[0] * t, lin[1] * (1 - t) + plate[1] * t)

def make(kind, iw_deg=0.0, m=1.5, Sw=0.018, Ss=0.018, CdAbody=0.006, rods_c=0.008):
    AR = 7.2
    return dict(kind=kind, m=m, iw=math.radians(iw_deg), Sw=Sw, Ss=Ss, CdAbody=CdAbody, rods_c=rods_c,
                CL0=0.3, a=2 * math.pi * AR / (AR + 2), alpha_s=math.radians(12), CD0=0.012,
                k=1 / (math.pi * AR * 0.8))

def frame(v, beta, phi):
    vh = unit(v); up = np.array([0, 0, 1.0])
    s = unit(np.cross(up, vh)); u = np.cross(vh, s)             # velocity frame (vh, left, up-ish)
    b3 = math.cos(beta) * (math.cos(phi) * u + math.sin(phi) * s) + math.sin(beta) * vh
    b2 = unit(np.cross(vh, b3))                                  # zero side-slip
    b1 = np.cross(b2, b3)                                        # points backwards (camera side)
    return b1, b2, b3

def aero(W, v, b1, b2, b3):
    sp = np.linalg.norm(v); vh = v / sp; q = 0.5 * RHO * sp * sp; m = W['m']
    if W['kind'] == 'rods':
        return -W['rods_c'] * sp * v, 0.0
    nw = math.cos(W['iw']) * b3 + math.sin(W['iw']) * b1
    vn = float(vh @ nw); alpha = -math.asin(max(-1, min(1, vn)))
    CL, CD = section(W, alpha)
    l = nw - vn * vh; l = l / np.linalg.norm(l) if np.linalg.norm(l) > 1e-9 else l
    F = q * W['Sw'] * (CL * l - CD * vh) / m
    un = float(v @ b3)
    F += -1.2 * 0.5 * RHO * un * abs(un) * W['Ss'] / m * b3
    F += -0.5 * RHO * W['CdAbody'] / m * sp * v
    return F, alpha

def trim(W, v, a, guess=(0.3, 0.0, 10.0)):
    req = a + np.array([0, 0, G])
    def eqs(x):
        beta, phi, T = x
        b1, b2, b3 = frame(v, beta, phi)
        F, _ = aero(W, v, b1, b2, b3)
        return T * b3 + F - req
    sol, info, ier, msg = fsolve(eqs, guess, full_output=True)
    if ier != 1 or np.linalg.norm(eqs(sol)) > 1e-6: return None
    beta, phi, T = sol
    b1, b2, b3 = frame(v, beta, phi)
    _, alpha = aero(W, v, b1, b2, b3)
    return dict(beta=beta, phi=phi, T=T, alpha=alpha, R=np.array([b1, b2, b3]), x=sol)

def camera(R, lo, hi):
    up = np.array([0, 0, 1.0]); u1, u2, u3 = R @ up
    eta_star = math.atan2(u3, u1)
    eta = min(hi, max(lo, eta_star)); miss = abs(eta_star - eta)
    rho = math.sqrt(u1 * u1 + u3 * u3)
    camOff = math.acos(max(-1, min(1, rho * math.cos(miss))))
    return camOff, math.degrees(math.asin(min(1, abs(u2))))

def rot_angle(R0, R1):
    M = R1 @ R0.T; c = (np.trace(M) - 1) / 2
    return math.acos(max(-1, min(1, c)))

def condition(W, s, gamma, at, alat, cam=(math.radians(30), math.radians(70))):
    """Flight at speed s, climb gamma, along-track accel at, turning accel alat (horizontal)."""
    v = s * np.array([math.cos(gamma), 0, math.sin(gamma)])
    vh = unit(v); left = unit(np.cross(np.array([0, 0, 1.0]), vh))
    a = at * vh + alat * left
    t = trim(W, v, a)
    if t is None: return None
    out = dict(T=t['T'], pitch=math.degrees(math.acos(max(-1, min(1, t['R'][2][2])))),
               bank=math.degrees(t['phi']), alpha=math.degrees(t['alpha']))
    out['camOff'], out['offplane'] = camera(t['R'], *cam)
    out['camOff'] = math.degrees(out['camOff'])
    # attitude sensitivity (rad per m/s^2) to acceleration changes in three directions
    up_perp = np.cross(vh, left)
    sens = {}
    for name, dvec in [('lat', left), ('vert', up_perp), ('long', vh)]:
        t2 = trim(W, v, a + 0.3 * dvec, guess=t['x'])
        sens[name] = rot_angle(t['R'], t2['R']) / 0.3 if t2 else float('nan')
    out['sens'] = sens
    return out

def torque_proxy(Q, cond, J, S):
    """Attitude rate ~ sens*J, angular accel ~ sens*S + (sens*J)^2 (worst direction), torque need vs
    available (motor collective)."""
    sm = max(cond['sens'].values())
    rate = sm * J; acc = sm * S + rate ** 2
    need = Q['J'] * acc / (2 * Q['arm']) + Q['Jz'] * acc / (4 * Q['kYaw'])
    avail = Q['m'] * cond['T'] / 4
    return rate, acc, need, avail

if __name__ == '__main__':
    Q = dict(m=1.5, J=0.012, Jz=0.02, arm=0.18, kYaw=0.02, Tmax=58.9)
    designs = [('rods c=0.008', make('rods')), ('winged iw=0', make('wing', 0)),
               ('winged iw=15', make('wing', 15)), ('winged iw=25', make('wing', 25))]
    J, S, R = 5.0, 15.0, 350.0
    print("Worst case over the flight envelope at each speed (climb -10..10 deg, turn up to v^2/R, along-track ±2):")
    print("  T_min/T_max motor thrust; max bank; max camera offset (deg, hinge 30-70, needs + position error <= 60);")
    print("  max attitude sensitivity (deg per m/s^2); torque proxy need/avail (N per motor) at jerk 5, snap 15")
    for name, W in designs:
        print(name)
        for s in [20, 30, 35, 45, 55]:
            Ts = []; banks = []; cams = []; sens = []; ratio = []; fails = 0
            for gamma in [-10, 0, 10]:
                for at in [-2, 0, 2]:
                    for k in [-1, 0, 1]:
                        c = condition(W, s, math.radians(gamma), at, k * s * s / R)
                        if c is None: fails += 1; continue
                        Ts.append(c['T']); banks.append(abs(c['bank'])); cams.append(c['camOff'])
                        sens.append(max(c['sens'].values()))
                        r, acc, need, avail = torque_proxy(Q, c, J, S)
                        ratio.append((need, avail))
            if not Ts: print(f"   {s} m/s: no trim"); continue
            worst = max(ratio, key=lambda x: x[0] / x[1])
            print(f"   {s} m/s: T {min(Ts):5.1f}/{max(Ts):5.1f}  bank<={max(banks):4.0f}  cam<={max(cams):4.0f}  "
                  f"sens<={math.degrees(max(sens)):4.1f}  torque {worst[0]:.2f}/{worst[1]:.2f} N" + (f"  ({fails} untrimmed)" if fails else ""))

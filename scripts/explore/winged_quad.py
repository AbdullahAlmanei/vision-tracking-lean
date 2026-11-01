#!/usr/bin/env python3
"""Winged quad prototype (vertical-plane trim).

Airframe: the arm pair spanning sideways (along b2) is a cambered airfoil whose chord lies along
the camera's fore-aft axis b1; the fore-aft arms are symmetric streamlined sections (cross-flow
drag only); plus a small body drag. Rotor thrust along b3. Pitch p tilts b3 forward from vertical.

Section model (cambered pair): C_L = CL0 + a*alpha for |alpha| <= alpha_s, drag polar
C_D = CD0 + k C_L^2; past stall a flat plate: C_N = 1.2 sin(alpha) normal to the chord plane
(blended over 5 deg). alpha is the angle of the wind to the chord plane, positive when the wind
hits the lower surface. Symmetric arms: cross-flow drag 1.2 q_n S on the wind component normal
to the rotor plane.
"""
import math

RHO = 1.225
QUAD = dict(m=1.5, g=9.81, Tmax=4 * (6 * 1.5 * 9.81 / 4) / 1.5, tiltMax=math.radians(85))

def airframe(iw=0.0, Sw=0.018, CL0=0.3, AR=7.2, alpha_s=math.radians(12), CD0=0.012, Ss=0.018, CdAbody=0.006):
    return dict(iw=iw, Sw=Sw, CL0=CL0, a=2 * math.pi * AR / (AR + 2), alpha_s=alpha_s, CD0=CD0,
                k=1 / (math.pi * AR * 0.8), Ss=Ss, CdAbody=CdAbody)

def section(A, alpha):
    """(C_L, C_D) of the cambered pair at angle of attack alpha (rad)."""
    lin_CL = A['CL0'] + A['a'] * alpha
    lin = (lin_CL, A['CD0'] + A['k'] * lin_CL ** 2)
    CN = 1.2 * math.sin(alpha)
    plate = (CN * math.cos(alpha), A['CD0'] + CN * math.sin(alpha))
    s = A['alpha_s']; w = math.radians(5)
    t = min(1.0, max(0.0, (abs(alpha) - s) / w))
    return (lin[0] * (1 - t) + plate[0] * t, lin[1] * (1 - t) + plate[1] * t)

def aero_force(A, s, gamma, p, rods_c=None):
    """Aerodynamic force per unit mass in the vertical plane (x forward, z up); returns (Fx, Fz, alpha)."""
    vx, vz = s * math.cos(gamma), s * math.sin(gamma)
    if rods_c is not None:                     # the current model: isotropic drag only
        return -rods_c * s * vx, -rods_c * s * vz, 0.0
    b3 = (math.sin(p), math.cos(p))
    vn = (vx * b3[0] + vz * b3[1]) / s            # <v_hat, b3>
    nw = (math.sin(p - A['iw']), math.cos(p - A['iw']))   # wing upper normal (chord nose-up by iw)
    vnw = (vx * nw[0] + vz * nw[1]) / s
    alpha = -math.asin(max(-1, min(1, vnw)))
    q = 0.5 * RHO * s * s
    CL, CD = section(A, alpha)
    # lift direction: perpendicular to v, toward +b3 side
    vh = (vx / s, vz / s)
    lx, lz = nw[0] - vnw * vh[0], nw[1] - vnw * vh[1]
    ln = math.hypot(lx, lz); lx, lz = (lx / ln, lz / ln) if ln > 1e-9 else (0, 0)
    m = QUAD['m']
    Fx = q * A['Sw'] * (CL * lx - CD * vh[0]) / m
    Fz = q * A['Sw'] * (CL * lz - CD * vh[1]) / m
    # symmetric arms: cross-flow on the normal wind component
    un = s * vn
    Fn = -1.2 * 0.5 * RHO * un * abs(un) * A['Ss'] / m
    Fx += Fn * b3[0]; Fz += Fn * b3[1]
    # body drag
    cb = 0.5 * RHO * A['CdAbody'] / m
    Fx -= cb * s * vx; Fz -= cb * s * vz
    return Fx, Fz, alpha

def trim(A, s, gamma, at=0.0, an=0.0, rods_c=None):
    """Pitch p and thrust T (per unit mass) flying speed s at climb gamma with along-track accel at
    and vertical-plane normal accel an. Returns (p, T, alpha) or None."""
    g = QUAD['g']
    ax = at * math.cos(gamma) - an * math.sin(gamma)
    az = at * math.sin(gamma) + an * math.cos(gamma) + g
    best = None
    for i in range(-300, 1801):
        p = math.radians(i * 0.05)
        Fx, Fz, alpha = aero_force(A, s, gamma, p, rods_c)
        rx, rz = ax - Fx, az - Fz                  # what the rotors must supply
        T = math.hypot(rx, rz)
        if T < 1e-9: continue
        err = abs(math.atan2(rx, rz) - p)          # rotor force must point along b3
        if best is None or err < best[0]: best = (err, p, T, alpha)
    err, p, T, alpha = best
    if err > math.radians(0.2): return None
    return p, T, alpha

def sensitivity(A, s, gamma, rods_c=None, da=0.5):
    """Pitch change per unit change of normal (vertical-plane) acceleration, rad per m/s^2."""
    t0 = trim(A, s, gamma, an=0.0, rods_c=rods_c); t1 = trim(A, s, gamma, an=da, rods_c=rods_c)
    if not t0 or not t1: return None
    return abs(t1[0] - t0[0]) / da

if __name__ == '__main__':
    W = airframe()
    print("Steady trim (per unit mass). Columns: pitch deg / motor thrust m/s^2 / wing AoA deg;"
          " dpitch per unit vertical accel (deg per m/s^2)")
    for label, kw in [('rods c=0.008', dict(rods_c=0.008)), ('rods c=0.0026 (same drag as winged)', dict(rods_c=0.0026)),
                      ('winged (cambered lateral arms)', {})]:
        print(label)
        for gamma_deg in [0, -10]:
            row = []
            for s in [20, 35, 45, 55]:
                t = trim(W, s, math.radians(gamma_deg), **kw)
                sv = sensitivity(W, s, math.radians(gamma_deg), **kw)
                row.append(f"{s}m/s: " + (f"{math.degrees(t[0]):5.1f}/{t[1]:5.1f}/{math.degrees(t[2]):6.1f}" if t else "no trim")
                           + (f" ({math.degrees(sv):.1f})" if sv else ""))
            print(f"   climb {gamma_deg:4d}: " + " | ".join(row))
    print(f"Motor thrust capacity: {QUAD['Tmax']:.1f} m/s^2")

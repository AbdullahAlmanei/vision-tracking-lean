#!/usr/bin/env python3
"""Weaving beats steady flight under the rotor-disc normal force.

At speed V the collective is G + k_n V <v, b3>. Pointing extra thrust sideways (no work)
tilts b3 off the airflow and lowers the normal-force drag, so a drone that banks left and
right alternately can fly faster than in steady straight flight. This script builds such a
trajectory in the exact discrete rigid-body model of `Model.lean` (Euler translation,
frames by rotation vectors, body rates and torques as in `Lifting.lean`, "+" mixer,
motors in [0, fMotor], rate and tilt limits) and measures its average forward speed.
"""
import math, numpy as np
from scipy.spatial.transform import Rotation as Rot

g = 9.81; m = 1.5; fMotor = 6 * m * g / 4; Fm = 4 * fMotor / m
J = np.diag([0.012, 0.012, 0.02]); arm = 0.18; kYaw = 0.02
c = 0.008; rateMax = 20.0; tiltMax = math.radians(85); dt = 1 / 240

def unit(x): return x / np.linalg.norm(x)

def motors(Ftot, tau, arm_=arm, k=kYaw):
    """Solve the '+' mixer exactly: sum = Ftot, torque = tau."""
    A = np.array([[1, 1, 1, 1], [0, arm_, 0, -arm_], [-arm_, 0, arm_, 0], [k, -k, k, -k]])
    return np.linalg.solve(A, np.array([Ftot, *tau]))

def bank(t, T, phi0, ramp):
    """Odd square wave of amplitude phi0 and period T with sine ramps of half-width `ramp`
    centred on each sign change (u = 0, T/2)."""
    u = t % T
    if u < ramp: return phi0 * math.sin(math.pi / 2 * u / ramp)
    if u < T / 2 - ramp: return phi0
    if u < T / 2 + ramp: return phi0 * math.sin(math.pi / 2 * (T / 2 - u) / ramp)
    if u < T - ramp: return -phi0
    return -phi0 * math.sin(math.pi / 2 * (T - u) / ramp)

def run(kn, V0, T, phi0, ramp, reserve, secs=40.0, verbose=False):
    """Fly the weave from speed V0 for `secs`; return mean forward speed over the last half
    and the worst constraint violations."""
    n = int(secs / dt)
    v = np.array([V0, 0.0, 0.0]); x = np.zeros(3); z0 = 0.0
    frames = []; Fs = []; vs = []
    for k in range(n):
        t = k * dt
        phi = bank(t, T, phi0, ramp)
        V = np.linalg.norm(v)
        # vertical feedback: hold altitude and zero climb rate on average
        az = -2.0 * (x[2] - z0) - 3.0 * v[2]
        F = Fm - reserve
        # b3 = rotation by phi about the velocity heading of (sin a, 0, cos a) in the vertical plane
        h = unit(np.array([v[0], v[1], 0.0])); lat = np.cross([0, 0, 1.0], h)
        # solve for a: G cos a cos phi = g + az + c V v_z ;  F = G + kn V <v, b3>
        def resid(a):
            b3 = math.sin(a) * h + math.cos(a) * (math.cos(phi) * np.array([0, 0, 1.0]) - math.sin(phi) * lat)
            G = (g + az + c * V * v[2]) / (math.cos(a) * math.cos(phi))
            return G + kn * V * (v @ b3) - F, b3, G
        lo, hi = 0.0, 1.5
        for _ in range(40):
            mid = (lo + hi) / 2
            r, _, _ = resid(mid)
            lo, hi = (mid, hi) if r < 0 else (lo, mid)
        _, b3, G = resid(lo)
        a = G * b3 - g * np.array([0, 0, 1.0]) - c * V * v
        # heading-locked frame
        b1 = unit(h - (h @ b3) * b3); b2 = np.cross(b3, b1)
        frames.append(np.stack([b1, b2, b3])); Fs.append(F); vs.append(v.copy())
        x = x + dt * v; v = v + dt * a
    # rates, torques, motors (Lifting.lean conventions)
    R = np.array(frames)
    om = []
    for k in range(n - 1):
        rv = Rot.from_matrix(R[k + 1].T @ R[k]).as_rotvec()       # world rotation k -> k+1
        om.append(R[k] @ rv / dt)                                  # body components
    om = np.array(om)
    worst = dict(rate=0.0, fmin=1e9, fmax=-1e9, tilt=0.0)
    for k in range(n - 2):
        tau = J @ ((om[k + 1] - om[k]) / dt) + np.cross(om[k], J @ om[k])
        f = motors(m * Fs[k], tau)
        worst['rate'] = max(worst['rate'], np.linalg.norm(om[k]))
        worst['fmin'] = min(worst['fmin'], f.min()); worst['fmax'] = max(worst['fmax'], f.max())
        worst['tilt'] = max(worst['tilt'], math.degrees(math.acos(R[k][2][2])))
    vs = np.array(vs); half = n // 2
    mean_fwd = (x[0] - 0) / secs  # overall
    fwd = np.mean(vs[half:, 0]); spd = np.mean(np.linalg.norm(vs[half:], axis=1))
    lat_amp = np.ptp(np.cumsum(vs[half:, 1]) * dt) / 2
    ok = worst['rate'] <= rateMax and worst['fmin'] >= 0 and worst['fmax'] <= fMotor and worst['tilt'] <= 85
    return fwd, ok, worst, lat_amp, vs[-1]

def steady_wall(kn):
    lo, hi = 1.0, 150.0
    for _ in range(60):
        V = (lo + hi) / 2; N = math.hypot(g, c * V * V)
        lo, hi = (V, hi) if N + kn * V * V * (c * V * V) / N <= Fm else (lo, V)
    return lo

def job(args):
    kn, sw, T, phi0, ramp, reserve = args
    fwd, ok, w, la, _ = run(kn, sw, T, phi0, ramp, reserve, secs=20.0)
    return (fwd, ok, T, math.degrees(phi0), ramp, reserve, w, la)

if __name__ == '__main__':
    from multiprocessing import Pool
    for kn in [0.02, 0.01, 0.005]:
        sw = steady_wall(kn)
        grid = [(kn, sw, T, math.radians(a), r, res) for T in [0.8, 1.4, 2.4]
                for a in [0, 30, 50, 62] for r in [0.1, 0.2] for res in [0.5, 2.0]]
        with Pool() as pool:
            out = pool.map(job, grid)
        feas = [o for o in out if o[1]]
        best = max(feas, key=lambda o: o[0]) if feas else None
        if best is None:
            print(f"k_n {kn}: steady wall {sw:.2f} | no feasible weave", flush=True); continue
        best = (best[0],) + best[2:]
        print(f"k_n {kn}: steady wall {sw:.2f} | best feasible weave mean forward speed {best[0]:.2f} "
              f"(T {best[1]} s, bank ±{best[2]:.0f} deg, ramp {best[3]} s, reserve {best[4]} m/s^2, "
              f"rate {best[5]['rate']:.1f}, motors {best[5]['fmin']:.1f}..{best[5]['fmax']:.1f}/{fMotor:.1f} N, "
              f"lateral ±{best[6]:.1f} m)", flush=True)

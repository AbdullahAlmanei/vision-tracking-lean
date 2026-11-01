#!/usr/bin/env python3
"""Numerical study of jerk/snap-capped trackers against adversarial targets (one axis).

Target: acceleration |a| <= A, jerk |j| <= J, snap |s| <= S (bang-bang snap aimed at jerk
set-points chosen by the adversary). Tracker: plans its own acceleration with jerk <= Jc and
snap <= Sc. The adversary is searched (switching times and set-points) to maximise the
tracker's worst position lag.
"""
import numpy as np, math

def target_from_plan(setpts, durs, dt, A, J, S):
    """Target accel sequence: snap bang-bang toward jerk set-points, respecting |a|<=A."""
    a = 0.0; j = 0.0; out = []
    for jt, T in zip(setpts, durs):
        n = max(1, int(T / dt))
        for _ in range(n):
            jt_eff = jt * J
            # braking: do not overshoot the acceleration bound
            stop = a + j * abs(j) / (2 * S) if S > 0 else a
            if stop > A: jt_eff = -J
            if stop < -A: jt_eff = J
            s = np.clip((jt_eff - j) / dt, -S, S)
            j = np.clip(j + dt * s, -J, J)
            a = np.clip(a + dt * j, -A, A)
            out.append(a)
    return np.array(out)

def track(acc, dt, P):
    """Cascade tracker: a_ref = a_T + sat(kp e + kv ev); jerk/snap-limited acceleration loop."""
    kp, kv, Ac, ta, tj, Jc, Sc = P['kp'], P['kv'], P['Ac'], P['ta'], P['tj'], P['Jc'], P['Sc']
    pT = vT = 0.0; x = w = al = jj = 0.0
    emax = vmax = amax = alag = 0.0
    for aT in acc:
        corr = max(-Ac, min(Ac, kp * (pT - x) + kv * (vT - w)))
        jd = max(-Jc, min(Jc, (aT + corr - al) / ta))
        s = max(-Sc, min(Sc, (jd - jj) / tj))
        jj += dt * s; x += dt * w; w += dt * al; al += dt * jj
        pT += dt * vT; vT += dt * aT
        emax = max(emax, abs(x - pT)); vmax = max(vmax, abs(w - vT))
        amax = max(amax, abs(al)); alag = max(alag, abs(al - aT))
    return emax, vmax, amax, alag

def adversary(dt, A, J, S, P, iters=300, nseg=24, seed=0):
    rng = np.random.default_rng(seed)
    best = None
    sp = rng.choice([-1.0, 1.0], nseg) * rng.uniform(0.3, 1, nseg)
    du = rng.uniform(0.3, 6.0, nseg)
    def score(sp, du):
        return track(target_from_plan(sp, du, dt, A, J, S), dt, P)
    cur = score(sp, du); best = (cur, sp.copy(), du.copy())
    for it in range(iters):
        sp2 = sp.copy(); du2 = du.copy()
        k = rng.integers(nseg)
        if rng.random() < 0.5: sp2[k] = rng.choice([-1.0, 1.0]) * rng.uniform(0.3, 1)
        else: du2[k] = np.clip(du2[k] * rng.uniform(0.5, 1.6), 0.1, 10)
        r = score(sp2, du2)
        if r[0] >= cur[0]:
            sp, du, cur = sp2, du2, r
            if r[0] > best[0][0]: best = (r, sp.copy(), du.copy())
    return best[0]

def table(A, J, S, Jc, Sc, dt=0.02, iters=150):
    best = None
    for kp, kv in [(0.02, 0.2), (0.04, 0.3), (0.08, 0.45)]:
        for ta in [0.3, 0.6]:
            P = dict(kp=kp, kv=kv, Ac=2.0, ta=ta, tj=0.2, Jc=Jc, Sc=Sc)
            r = adversary(dt, A, J, S, P, iters=iters)
            if best is None or r[0] < best[0][0]: best = (r, P)
    return best

if __name__ == '__main__':
    dt = 0.02
    for A, J, S in [(5.5, 5, 15), (5.5, 10, 30), (10.6, 5, 15)]:
        print(f"target per axis: A={A} J={J} S={S}")
        for (Jc, Sc) in [(3, 5), (4, 6), (5, 10)]:
            best = None
            for kp, kv in [(0.02, 0.2), (0.04, 0.3), (0.08, 0.45)]:
                for ta in [0.3, 0.6]:
                    P = dict(kp=kp, kv=kv, Ac=2.0, ta=ta, tj=0.2, Jc=Jc, Sc=Sc)
                    e, v = adversary(dt, A, J, S, P, iters=150)
                    if best is None or e < best[0]: best = (e, v, kp, kv, ta)
            e, v, kp, kv, ta = best
            print(f"   caps jerk {Jc} snap {Sc}: worst lag {e:7.1f} m, vel lag {v:5.1f} m/s  (best gains kp {kp} kv {kv} ta {ta})")

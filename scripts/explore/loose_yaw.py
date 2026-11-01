import math, sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '..'))
import budget_v3 as b
src=open(__import__('os').path.join(__import__('os').path.dirname(__file__), '..', 'budget_v3.py')).read()
a=src.index("    rp2 = xn + d2n * db + 2 * dn * db")
bb=src.index("    need = trp / (2 * Q['arm'])")
loose='''    rp2 = xn + d2n * db + 2 * dn * db
    Y = (dl + sb * dn) / M
    kd = KPSI * dt
    psi = Y / kd
    yaw2 = 2 * kd * Y + db * db + 2 * Y * (Y + db)
    Om = G * th / dt; dOmz = (G * yaw2 + (G - 1) * th) / dt
    Jxy = max(Q['Jx'], Q['Jy']); Jg = max(abs(Q['Jz'] - Q['Jy']), abs(Q['Jx'] - Q['Jz']))
    dOm = (G * abs(rp2) + (G - 1) * th) / dt
    trp = Jxy * dOm / dt + Jg * Om ** 2
    tyaw = Q['Jz'] * dOmz / dt + abs(Q['Jy'] - Q['Jx']) * Om ** 2
    Nlo = c * sLo ** 2 * cg - A - Thi * (eV / vh) - eT
    plo = math.atan(Nlo / Zhi if Nlo >= 0 else Nlo / (Zlo * M))
    phi = math.atan(Hhi / (Zlo * M))
    miss = max(0, max((math.pi / 2 - plo) - C['hingeHi'], C['hingeLo'] - (math.pi / 2 - phi)))
    u1 = min(1.0, Hhi / Tlo)
    off = min(1.0, sb + abs(math.sin(min(psi, math.pi / 2))) * u1)
    camOff = math.acos(math.sqrt(1 - off ** 2) * math.cos(miss)) if miss <= math.pi / 2 else float('inf')
    mu = math.asin(rho / d) if rho < d else float('inf')
    hstep = math.pi / 2 * (db + dn) / M
'''
s2=src[:a]+loose+src[bb:]
def make(kpsi):
    ns={'KPSI':kpsi}; exec(s2.split("if __name__")[0], ns); return ns
def search(ns,P,Q,C,d=100.0):
    for hz in [120,240,480]:
        for win in [0.5,1.0,2.0,3.0]:
            F=ns['fir_consts'](ns['tap3'](4,max(8,int(round(win*hz)))))
            f,W=ns['master_ineq3'](P,Q,C,1/hz,F,d)
            if not f: return (hz,win,W)
    return None

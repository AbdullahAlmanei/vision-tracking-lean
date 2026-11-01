import numpy as np, math
exec(open(__import__('os').path.join(__import__('os').path.dirname(__file__), 'tracker_saturated.py')).read().split("def run")[0])
def run2(acc, dt, Jc, Sc, kp, kv, Ac, tau_a=0.3):
    N=len(acc); p=np.zeros(N); v=np.zeros(N)
    for k in range(N-1): v[k+1]=v[k]+dt*acc[k]; p[k+1]=p[k]+dt*v[k]
    x=w=al=jj=0.0
    emax=0; jmax=0; smax=0; vmax=0
    for k in range(N):
        corr = max(-Ac,min(Ac, kp*(p[k]-x)+kv*(v[k]-w)))
        aref = acc[k] + corr
        jd = max(-Jc,min(Jc,(aref-al)/tau_a))
        s = max(-Sc,min(Sc,(jd-jj)/tau_a))
        jj+=dt*s; x+=dt*w; w+=dt*al; al+=dt*jj
        emax=max(emax,abs(x-p[k])); vmax=max(vmax,abs(w-v[k])); jmax=max(jmax,abs(jj)); smax=max(smax,abs(s))
    return emax,vmax,jmax,smax
rng=np.random.default_rng(2); dt=1/60; N=60*300
for A,J,S in [(5.5,5,15),(5.5,10,30),(10.6,10,30)]:
    seqs=[target_seq(N,dt,A,J,S,rng,'bang') for _ in range(6)]+[target_seq(N,dt,A,J,S,rng,'sine')]
    print(f"target A={A} J={J} S={S}")
    for (Jc,Sc,kp,kv,Ac) in [(2.5,3,0.05,0.4,2),(3,4,0.08,0.5,3),(4,6,0.1,0.6,3),(6,10,0.15,0.8,4)]:
        res=[run2(s,dt,Jc,Sc,kp,kv,Ac) for s in seqs]
        print(f"   cap jerk {Jc} snap {Sc} kp {kp} kv {kv} Ac {Ac}: max pos err {max(r[0] for r in res):7.1f} m, vel err {max(r[1] for r in res):5.1f}, plan jerk {max(r[2] for r in res):.2f}, plan snap {max(r[3] for r in res):.2f}")

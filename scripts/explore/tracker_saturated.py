import numpy as np, math
def target_seq(N, dt, A, J, S, rng, mode):
    a=0.0; j=0.0; out=[]
    for k in range(N):
        if mode=='bang':   # snap bang-bang aiming at random jerk targets, accel targets
            if k % int(rng.integers(20,400))==0: jt=rng.choice([-J,J]) * rng.uniform(0.5,1)
            s=np.clip((jt-j)/dt, -S, S)
        elif mode=='sine':
            f=0.5/ (A/J*4) ; s=-S*np.sign(math.sin(2*math.pi*f*k*dt))
        j=np.clip(j+dt*s,-J,J)
        # keep |a|<=A: brake jerk if near limit
        amax_reach = a + j*abs(j)/(2*S)
        if abs(amax_reach)>A: j=np.clip(j - dt*S*np.sign(amax_reach),-J,J)
        a=np.clip(a+dt*j,-A,A); out.append(a)
    return np.array(out)
def run(acc, dt, Jc, Sc, w0, zeta=0.9):
    # target kinematics from accel
    N=len(acc); p=np.zeros(N); v=np.zeros(N)
    for k in range(N-1): v[k+1]=v[k]+dt*acc[k]; p[k+1]=p[k]+dt*v[k]
    x=w=al=jj=0.0; k1=(1+2*zeta)*w0; k2=(1+2*zeta)*w0**2; k3=w0**3
    emax=0; jmax=0; smax=0
    for k in range(N):
        jd = k1*(acc[k]-al)+k2*(v[k]-w)+k3*(p[k]-x)
        jd = max(-Jc,min(Jc,jd))
        s = max(-Sc,min(Sc,(jd-jj)/(4*dt)))
        jj+=dt*s; x+=dt*w; w+=dt*al; al+=dt*jj
        emax=max(emax,abs(x-p[k])); jmax=max(jmax,abs(jj)); smax=max(smax,abs(s))
    return emax,jmax,smax
rng=np.random.default_rng(1); dt=1/120; N=120*120
for A,J,S in [(5.5,5,15),(5.5,10,30),(10.6,5,15),(10.6,10,30)]:
    seqs=[target_seq(N,dt,A,J,S,rng,'bang') for _ in range(6)]+[target_seq(N,dt,A,J,S,rng,'sine')]
    print(f"target A={A} J={J} S={S}")
    for (Jc,Sc,w0) in [(2.5,2,0.4),(3,3,0.5),(4,4,0.6),(6,6,0.8)]:
        res=[run(s,dt,Jc,Sc,w0) for s in seqs]
        e=max(r[0] for r in res); print(f"   cap jerk {Jc} snap {Sc} w0 {w0}: max pos err {e:6.1f} m, plan jerk {max(r[1] for r in res):.2f}, plan snap {max(r[2] for r in res):.2f}")

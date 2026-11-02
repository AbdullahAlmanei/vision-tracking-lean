#!/usr/bin/env python3
"""Lagrangian dual of the power wall (k_n = 0.01): energy multiplier kappa plus a constant
vector multiplier m (vertical/along-track force balance on average). The optimum has m ~ 0 and
gives 57.36 m/s with delta -> 0, matching the steady force-balance wall (57.3 m/s)."""
import numpy as np, math
from scipy.optimize import minimize
g=9.81; c=0.008; kn=0.01; Fm=6*g; S=90.0
# grids: b3 on sphere (x=along u, z=up; lateral irrelevant by symmetry -> include y anyway coarse)
th=np.linspace(0,math.pi,181); ph=np.linspace(-math.pi,math.pi,73)
TH,PH=np.meshgrid(th,ph); B=np.stack([np.sin(TH)*np.cos(PH),np.sin(TH)*np.sin(PH),np.cos(TH)],-1).reshape(-1,3)
# velocities: in x-z plane plus lateral is never helpful (assume); grid speed & elevation
Vs=np.linspace(0,S,91); el=np.linspace(-math.pi/2,math.pi/2,61)
def alpha(params):
    kap,mz,mx=params
    if kap<0: return 1e9
    m=np.array([mx,0,mz]); best=-1e18
    for V in Vs:
        for e in el:
            v=V*np.array([math.cos(e),0,math.sin(e)])
            p=B@v; w=kap*v+m; q=B@w
            E=np.maximum(Fm*q - kn*V*p*q, -kn*V*p*q).max()
            val=E - kap*c*V**3 - g*m[2] - c*V*(v@m) + v[0]
            best=max(best,val)
    return best
for x0 in [(0.02,0.0,0.0),(0.02,-0.3,0.0),(0.02,-1,0),(0.05,-2,0)]:
    r=minimize(alpha,x0,method='Nelder-Mead',options=dict(xatol=1e-4,fatol=1e-3,maxiter=400))
    print(x0, r.x, r.fun, flush=True)

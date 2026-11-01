import math, numpy as np, sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '..'))
import budget_v3 as b
def bump(L, W):
    i=np.arange(W+1); w=np.sin(math.pi*(i+0.5)/(W+1))**2; w/=w.sum()
    h=np.zeros(L+W+1); h[L:]=w; return h
def kconsts(h, dt):
    hp=np.concatenate([[0,0],h,[0,0]]); i=np.arange(len(h))
    return dict(TV=abs(np.diff(hp)).sum(), TV2=abs(np.diff(hp,2)).sum(), m1=(h*i).sum()*dt, span=len(h)*dt)
def at_speed4(P,Q,C,dt,K,d,s):
    g,c=Q['g'],Q['drag']; J,S,R=P['jerk'],P['snap'],P['R']
    sg,cg=math.sin(P['climb']),math.cos(P['climb'])
    Amax=P['aTan']+P['vMax']**2/R
    Lam=K['span']
    sHi=min(P['vMax'], s+P['aTan']*Lam+2*dt*Amax); sLo=max(P['vMin'], s-P['aTan']*Lam-2*dt*Amax)
    A=P['aTan']+sHi**2/R
    An=sHi**2/R
    psiw=min(math.pi/2, Lam*A/sLo)
    vlo=sLo*math.cos(psiw)
    Zlo=g-P['aVert']-c*sHi**2*sg; Zhi=g+P['aVert']+c*sHi**2*sg
    Fw=c*vlo**2*cg*cg-P['aTan']-P['aVert']*sg-An*math.sin(psiw)
    Tlo=max(Zlo,Fw); Thi=g+A+c*sHi**2; Hhi=A+c*sHi**2
    vh=vlo*cg
    ok=dict(zlo=Zlo>0, vh=vh>0)
    if not all(ok.values()): return ok,{}
    Lat=An+(P['aTan']+P['aVert'])*math.sin(psiw); sb=Lat/Tlo; ok['sb']=sb<1
    if sb>=1: return ok,{}
    M=math.sqrt(1-sb*sb)
    jp=min(J, K['TV']*A/dt)                       # planned jerk bound
    sp=min(S, K['TV2']*A/dt**2, K['TV']*J/dt)     # planned snap bound
    dT=dt*(jp+2*c*sHi*A)
    d2T=dt**2*sp+c*(2*sHi*dt**2*jp+4*dt**2*A**2)
    dn=dT/Tlo; xn=d2T/Tlo+2*dT**2/Tlo**2; d2n=2*d2T/Tlo+6*dT**2/Tlo**2
    dl=dt*A/vh; d2l=2*dt**2*jp/vh+6*dl**2
    dbc=(2*dl+2*dn)/M+dn
    th=math.sqrt(dn**2+((dl+sb*dn)/M)**2); ok['near']=dbc<=1; ok['th']=th<1
    if th>=1: return ok,{}
    G=1/math.sqrt(1-th**2); db=G*th
    rp2=xn+d2n*db+2*dn*db; yaw2=b.lat_dyaw(sb,dn,dl,d2n,xn,d2l,db)
    Om=G*th/dt; dOmz=(G*yaw2+(G-1)*th)/dt; dOmrp=(G*abs(rp2)+(G-1)*th)/dt
    Jxy=max(Q['Jx'],Q['Jy']); Jg=max(abs(Q['Jz']-Q['Jy']),abs(Q['Jx']-Q['Jz']))
    trp=Jxy*dOmrp/dt+Jg*Om**2; tyaw=Q['Jz']*dOmz/dt+abs(Q['Jy']-Q['Jx'])*Om**2
    Nlo=c*vlo**2*cg-P['aTan']-P['aVert']*sg-An*math.sin(psiw)
    plo=math.atan(Nlo/Zhi if Nlo>=0 else Nlo/(Zlo*M)); phi=math.atan(Hhi/(Zlo*M))
    miss=max(0,max((math.pi/2-plo)-C['hingeHi'],C['hingeLo']-(math.pi/2-phi)))
    camOff=math.acos(M*math.cos(miss)) if miss<=math.pi/2 else 9
    rho=K['m1']*sHi
    mu=math.asin(rho/d) if rho<d else 9
    need=trp/(2*Q['arm'])+tyaw/(4*Q['kYaw'])
    detect=P['size']/(2*math.tan(C['minPx']*C['fovH']/(2*C['widthPx'])))
    ok.update(tilt=math.atan(Hhi/Zlo)<=Q['tiltMax'], rate=Om<=Q['rateMax'], mix_lo=need<=Q['mass']*Tlo/4,
              mix_hi=Q['mass']*Thi/4+need<=Q['fMotor'], see=camOff+mu<=C['halfFov'],
              hinge=math.pi/2*(db+dn)/M<=dt*C['hingeRate'], range=d+rho<=detect)
    return ok,dict(need=need,avail=Q['mass']*Tlo/4,camOff=math.degrees(camOff),mu=math.degrees(mu),rho=rho,jp=jp,sp=sp)
def check4(P,Q,C,dt,K,d,ns=40):
    fails=set(); worst={}
    for i in range(ns+1):
        s=P['vMin']+(P['vMax']-P['vMin'])*i/ns
        ok,W=at_speed4(P,Q,C,dt,K,d,s); fails|={k for k,v in ok.items() if not v}
        for k,v in W.items(): worst[k]=max(worst.get(k,-1e9),v) if k!='avail' else min(worst.get(k,1e9),v)
    return fails,worst

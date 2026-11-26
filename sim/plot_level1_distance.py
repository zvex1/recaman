import sys, numpy as np, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
BLUE="#257de0"; ORANGE="#f47230"; INK="#191919"; INK2="#666666"; GRID="#e6e6e6"
plt.rcParams.update({"font.size":11,"axes.edgecolor":INK2,"axes.labelcolor":INK,"xtick.color":INK2,"ytick.color":INK2,
 "axes.spines.top":False,"axes.spines.right":False,"axes.grid":True,"grid.color":GRID,"axes.titlesize":12,"axes.titleweight":"bold"})
T=852656; src,out,top=sys.argv[1],sys.argv[2],float(sys.argv[3])
d=np.loadtxt(src,dtype=np.int64); o=np.argsort(d[:,0]); n,off=d[o,0],d[o,1]
dist=np.abs(off-T)
# sweeps: group points closer than 2% in time
brk=np.r_[True, n[1:]>n[:-1]*1.02]; gid=np.cumsum(brk)-1
best={}
for i,(g,dd) in enumerate(zip(gid,dist)):
    if g not in best or dd<dist[best[g]]: best[g]=i
bi=np.array(sorted(best.values()))
keep=n>=3e6
fig,ax=plt.subplots(figsize=(13,5.8))
ax.plot(n[keep],np.log10(dist[keep].clip(min=1)),".",ms=1.5,color=BLUE,alpha=0.6,rasterized=True,label="best level-1 offset in each zigzag (within 10⁷ of 852656)")
bk=bi[n[bi]>=3e6]
ax.plot(n[bk],np.log10(dist[bk].clip(min=1)),"o",ms=6,color=ORANGE,mec="white",mew=1,label="closest approach in each sweep")
for i in bk:
    if False: ax.annotate(f"{off[i]:,} (dist {dist[i]})",(n[i],np.log10(max(dist[i],1))),xytext=(6,12),textcoords="offset points",fontsize=8.5,color=INK,rotation=30)
ax.text(n[bk].min(),0.25,f"{int((dist[bk]==1).sum())} sweeps missed by exactly 1 (offset 852655 or 852657); none ever hit 0",fontsize=9.5,color=INK)
ax.axhline(0,color=INK2,lw=0.8,ls="--")
ax.set_xscale("log"); ax.set_xlim(2.5e6,top*1.3); ax.set_ylim(-0.4,7.6)
ax.set_xlabel("step n (log scale)"); ax.set_ylabel("log₁₀ |offset − 852656|")
ax.set_title("How close the walk's level-1 offsets come to 852656, sweep by sweep (distance 0 would produce 852655)")
ax.legend(frameon=False,fontsize=9,loc="upper right")
fig.tight_layout(); fig.savefig(out,dpi=160)
print("sweeps:",len(bk)," within 10:",int((dist[bk]<=10).sum())," within 1000:",int((dist[bk]<=1000).sum()))
for i in bk:
    if dist[i]<=1000: print(f"  n={n[i]:.4e} offset={off[i]} distance={dist[i]}")

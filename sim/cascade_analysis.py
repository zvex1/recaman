import sys, re, collections
pat = re.compile(r'Z k=(\d+) x=(\d+) lev=(\d+) h=(-?\d+) r=(\d+) (jump|full) m=(\d+) self=(\d+) fossil=(\d+) cause=(\S+) y=(\d+)')
KMIN = float(sys.argv[2])
casc = []; cur = None
for line in open(sys.argv[1]):
    if line.startswith('CASCADE start'): cur = []; casc.append(cur)
    elif line.startswith('Z') and cur is not None:
        mm = pat.match(line)
        if not mm: continue
        g = mm.groups()
        cur.append(dict(k=int(g[0]), x=int(g[1]), lev=int(g[2]), h=int(g[3]), r=int(g[4]), jump=g[5]=='jump',
                        m=int(g[6]), self=int(g[7]), foss=int(g[8]), cause=g[9], y=int(g[10])))
casc = [c for c in casc if c and c[0]['k'] >= KMIN]
def count_in(P, j, lo, hi):   # #{i < j : lo <= P - 3i <= hi}
    return sum(1 for i in range(j) if lo <= P - 3*i <= hi) if j < 10**6 else -1
cls = collections.Counter(); scan = collections.Counter(); ex = []
for c in casc:
    for i in range(len(c) - 1):
        D, Z = c[i], c[i+1]
        if D['lev'] == 0 and not D['jump'] and Z['lev'] >= 2:
            U = (D['x'] + D['k'] + 1, D['x'] + D['k'] + 1 + D['r'])
            P = Z['x'] - Z['k'] - 1
            loc = count_in(P, Z['m'], *U)
            if Z['jump'] and loc == Z['m']: cls['jump; every failed test inside the run just written'] += 1
            elif Z['jump'] and Z['foss'] == 0: cls['jump; extra failures on numbers written earlier in this cascade'] += 1
            elif Z['jump']: cls['jump; some failures on numbers older than the cascade'] += 1
            else: cls['no jump (restart zigzag ran out)'] += 1
        if Z['lev'] == 1 and D['lev'] >= 2 and Z['x'] - Z['k'] < 10**9:
            scan['jump into a hole' if Z['jump'] else 'full: ' + Z['cause']] += 1
print(f"cascades after {KMIN:.0e}: {len(casc)}")
print("restart zigzags (first zigzag after draining a run):")
for k2, v in cls.most_common(): print(f"  {v:6d}  {k2}")
print("level-1 scans just above the diagonal (height < 1e9):")
for k2, v in scan.most_common(): print(f"  {v:6d}  {k2}")
# exact rule test: in the "inside the run just written" cases, compare j with the run length
rule = collections.Counter(); off = collections.Counter()
for c in casc:
    for i in range(len(c) - 1):
        D, Z = c[i], c[i+1]
        if D['lev'] == 0 and not D['jump'] and Z['lev'] >= 2 and Z['jump']:
            U = (D['x'] + D['k'] + 1, D['x'] + D['k'] + 1 + D['r'])
            P = Z['x'] - Z['k'] - 1
            if count_in(P, Z['m'], *U) == Z['m']:
                rr = D['r']    # run eaten = r+1 holes, ell = x - r
                ell = D['x'] - D['r']
                rule[(rr % 3, Z['m'] - rr // 3)] += 1
                off[(U[1] - P)] += 1
                # transition time check: Z.k - (D.k + 2r)
print("(r mod 3, j - r div 3) for restarts explained by the run just eaten:", sorted(rule.items()))
print("top of that run minus first test:", sorted(off.items())[:10])

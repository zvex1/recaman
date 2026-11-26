// recaman_fast.cpp -- exact accelerated simulation of Recaman's sequence (OEIS A005132).
//
// a(0) = 0; a(n) = a(n-1) - n if that is positive and new, else a(n-1) + n.
//
// The walk spends almost all its time in zigzags. After landing on x at step k it alternates
//   x, x+k+1, x-1, x+k+2, x-2, ...
// as long as the numbers below x are free and the "jump tests" x-k-1-3j fail; this is the
// `zigzag` lemma in ../Recaman.lean. A whole zigzag is computed in O(log) time from the set of
// visited numbers, stored as disjoint, merged intervals. The result is exact.
//
// Usage: recaman_fast N [--records] [--quiet]
//   N          number of steps (up to ~1e18; values must stay below 2^64)
//   --records  print every time the smallest missing number gets filled, with the cascade of
//              zigzags that led to it
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <map>
#include <vector>
#include <chrono>

typedef unsigned long long u64;
typedef unsigned __int128 u128;

static std::map<u64, u64> V;  // visited numbers as intervals lo -> hi (inclusive)

static inline std::map<u64, u64>::iterator findInterval(u64 y) {
  auto it = V.upper_bound(y);
  if (it == V.begin()) return V.end();
  --it;
  return (it->second >= y) ? it : V.end();
}
static inline bool visited(u64 y) { return findInterval(y) != V.end(); }

// largest visited number < x (x >= 1; 0 is always visited)
static inline u64 predVisited(u64 x) {
  auto it = V.upper_bound(x - 1);
  --it;
  return (it->second >= x - 1) ? x - 1 : it->second;
}

static std::map<u64, u64> R;   // intervals written since the current cascade began
static bool inCascade = false;
static void addTo(std::map<u64,u64>& M, u64 lo, u64 hi) {
  auto it = M.upper_bound(lo);
  if (it != M.begin()) { auto p = std::prev(it); if (p->second + 1 >= lo) it = p; }
  u64 nlo = lo, nhi = hi;
  while (it != M.end() && it->first <= hi + 1) { if (it->first < nlo) nlo = it->first; if (it->second > nhi) nhi = it->second; it = M.erase(it); }
  M.emplace(nlo, nhi);
}
static bool inR(u64 y) { auto it = R.upper_bound(y); if (it == R.begin()) return false; --it; return it->second >= y; }
static void addInterval0(u64 lo, u64 hi);
static void addInterval(u64 lo, u64 hi) { if (inCascade) addTo(R, lo, hi); addInterval0(lo, hi); }
static void addInterval0(u64 lo, u64 hi) {
  auto it = V.upper_bound(lo);
  if (it != V.begin()) {
    auto p = std::prev(it);
    if (p->second + 1 >= lo) it = p;
  }
  u64 nlo = lo, nhi = hi;
  while (it != V.end() && it->first <= hi + 1) {
    if (it->first < nlo) nlo = it->first;
    if (it->second > nhi) nhi = it->second;
    it = V.erase(it);
  }
  V.emplace(nlo, nhi);
}

static u64 scanSteps = 0;
// largest free y with lowb <= y <= P and y = P (mod 3); 0 if none (requires lowb >= 1)
static u64 firstFreeInClass(u64 P, u64 lowb) {
  u64 y = P;
  for (;;) {
    scanSteps++;
    if (y < lowb) return 0;
    auto it = findInterval(y);
    if (it == V.end()) return y;
    u64 lo = it->first;
    if (lo == 0) return 0;
    u64 t = lo - 1;
    u64 r = (t % 3 + 3 - P % 3) % 3;
    if (t < r) return 0;
    y = t - r;
  }
}

struct Phase { u64 k, x; char how; };  // zigzag start: step, value, how it was entered

static void printValue(const char* label, u64 k, u64 x) {
  // write x as L*k + offset with L = nearest integer to x/k
  long double ratio = k ? (long double)x / (long double)k : 0;
  long long L = (long long)(ratio + 0.5L);
  __int128 off = (__int128)x - (__int128)L * (__int128)k;
  printf("%s step %llu: value %llu = %lld*t %+lld\n", label, k, x, L, (long long)off);
}

int main(int argc, char** argv) {
  if (argc < 2) { fprintf(stderr, "usage: %s N [--records] [--quiet]\n", argv[0]); return 1; }
  u64 N = strtoull(argv[1], 0, 10);
  bool records = false, quiet = false, stats = false;
  u64 watch = 0; u64 cascB = 0; u64 cascStart = 0, sinceDeep = 0; (void)cascStart;   // --watch B: log every zigzag that starts on a number below B
  u64 dumpLo = 1, dumpHi = 0;  // --dump A B: print every zigzag starting at a step in [A, B]
  double sampleF = 0; u64 nextSample = 1000;  // --sample F: print one zigzag start per factor F of time
  // stats[d][e]: jumps in decade d (10^d <= step < 10^(d+1)) whose landing is within 10^e above
  // the diagonal (0 < y - n < 10^e), and deep[d][e]: landings on a number y < 10^e
  static u64 nearDiag[20][20], deep[20][20], jumpsInDecade[20];
  for (int i = 2; i < argc; i++) {
    if (!strcmp(argv[i], "--records")) records = true;
    if (!strcmp(argv[i], "--quiet")) quiet = true;
    if (!strcmp(argv[i], "--stats")) stats = true;
    if (!strcmp(argv[i], "--sample") && i + 1 < argc) sampleF = atof(argv[++i]);
    if (!strcmp(argv[i], "--dump") && i + 2 < argc) { dumpLo = strtoull(argv[i + 1], 0, 10); dumpHi = strtoull(argv[i + 2], 0, 10); i += 2; }
    if (!strcmp(argv[i], "--watch") && i + 1 < argc) watch = strtoull(argv[++i], 0, 10);
    if (!strcmp(argv[i], "--cascade") && i + 1 < argc) cascB = strtoull(argv[++i], 0, 10);
  }
  auto t0 = std::chrono::steady_clock::now();
  addInterval(0, 0);
  u64 n = 0, v = 0;
  u64 phases = 0, jumps = 0, genericSteps = 0;
  u64 smallestMissing = V.begin()->second + 1;
  std::vector<Phase> recent(8);  // ring buffer of recent zigzag starts
  u64 nrecent = 0;
  char lastHow = 'g';
  u64 nextReport = 1000;

  auto checkRecord = [&]() {
    u64 s = V.begin()->second + 1;
    if (s != smallestMissing) {
      if (records) {
        printf("record: by step %llu every number below %llu has occurred (previous smallest "
               "missing: %llu)\n", n, s, smallestMissing);
        u64 cnt = nrecent < 4 ? nrecent : 4;
        for (u64 i = cnt; i >= 1; i--) {
          const Phase& p = recent[(nrecent - i) % recent.size()];
          char label[64];
          snprintf(label, sizeof label, "   zigzag (%s)", p.how == 'j' ? "after jump" : "after forward steps");
          printValue(label, p.k, p.x);
        }
        fflush(stdout);
      }
      smallestMissing = s;
    }
  };

  while (n < N) {
    // one ordinary step
    u64 k1 = n + 1;
    bool back = false;
    if (v > k1 && !visited(v - k1)) { v -= k1; back = true; } else { v += k1; }
    n = k1;
    addInterval(v, v);
    genericSteps++;
    checkRecord();
    if (!back) continue;
    lastHow = 'f';   // an ordinary step always follows a forward step, so this is a transition
    // a chain of zigzags, each entered by a backward landing
    for (;;) {
      if (n >= N) break;
      u64 k = n, x = v;
      recent[nrecent % recent.size()] = Phase{k, x, lastHow};
      nrecent++;
      u64 g = predVisited(x);
      u64 r = x - 1 - g;                      // x-1, ..., x-r are free
      u64 jstar = ~0ULL, y = 0;
      if (x > k + 1) {                        // jump tests x-k-1-3j, j = 0..r
        u64 P = x - k - 1;
        u128 three_r = (u128)3 * r;
        u64 lowb = ((u128)P > three_r) ? (u64)(P - (u64)three_r) : 1;
        if (lowb < 1) lowb = 1;
        y = firstFreeInClass(P, lowb);
        if (y) jstar = (P - y) / 3;
      }
      phases++;
      bool jump = (jstar <= r);
      if (cascB) {
        bool deepz = x < cascB;
        if (deepz && !inCascade) { inCascade = true; R.clear(); cascStart = k; printf("CASCADE start %llu\n", k); }
        if (deepz) sinceDeep = 0; else sinceDeep++;
        if (inCascade) {
          u64 m = jump ? jstar : r;
          long long h = (long long)x - (long long)k;   // height above diagonal
          // classify failed tests (only when few)
          u64 selfB = 0, fossB = 0;
          if (x > k + 1 && m <= 200000) {
            u64 P = x - k - 1;
            for (u64 i = 0; i < m && 3 * i < P; i++) { u64 q = P - 3 * i; if (inR(q)) selfB++; else fossB++; }
          }
          const char* cause = "-";
          if (!jump && x > k + 1) {
            u64 P = x - k - 1;
            if (P < 2000000000ULL) {
              u64 any = firstFreeInClass(P, 1);
              cause = any ? "short-run" : "empty-class";
            } else cause = "high";
          }
          printf("Z k=%llu x=%llu lev=%llu h=%lld r=%llu %s m=%llu self=%llu fossil=%llu cause=%s y=%llu\n",
                 k, x, k ? x / k : 0, h, r, jump ? "jump" : "full", m, selfB, fossB, cause, jump ? y : 0ULL);
          if (sinceDeep > 6) { inCascade = false; printf("CASCADE end\n"); }
        }
      }
      if (sampleF > 0 && k >= nextSample) {
        printf("sample k=%llu x/k=%.9Lf\n", k, (long double)x / k);
        nextSample = (u64)((long double)k * sampleF) + 1;
      }
      if (k >= dumpLo && k <= dumpHi)
        printf("zz k=%llu x/k=%.6Lf r=%llu %s m=%llu len/k=%.3e\n", k, (long double)x / k, r,
               jump ? "jump" : "full", jump ? jstar : r, (double)(2 * (jump ? jstar : r) + 1) / k);
      if (x < watch) {
        const Phase& src = recent[(nrecent + recent.size() - 2) % recent.size()];
        long double ratio = src.k ? (long double)src.x / (long double)src.k : 0;
        long long L = (long long)(ratio + 0.5L);
        printf("deep: step %llu lands on %llu (%s), fills %llu..%llu; came from zigzag at %lld*t%+lld\n",
               k, x, lastHow == 'j' ? "jump" : "transition", jump ? x - jstar : x - r, x,
               L, (long long)((__int128)src.x - (__int128)L * src.k));
        fflush(stdout);
      }
      u64 m = jump ? jstar : r;
      u64 endTime = k + 2 * m + 1;
      if (endTime > N) {                      // stop exactly at step N, inside this zigzag
        u64 d = N - k, i = d / 2;
        if (i > 0) addInterval(x - i, x - 1);
        if (d % 2 == 0) { if (i > 0) addInterval(x + k + 1, x + k + i); v = x - i; }
        else { addInterval(x + k + 1, x + k + 1 + i); v = x + k + 1 + i; }
        n = N;
        checkRecord();
        break;
      }
      if (jump) {
        if (m > 0) { addInterval(x - m, x - 1); addInterval(x + k + 1, x + k + m); }
        n = endTime; v = y;
        addInterval(y, y);
        jumps++;
        if (stats) {
          int d = 0; for (u64 q = n; q >= 10; q /= 10) d++;
          jumpsInDecade[d]++;
          for (int e = 1; e < 20; e++) {
            u64 H = 1; for (int z = 0; z < e; z++) H *= 10;
            if (y > n && y - n < H) nearDiag[d][e]++;
            if (y < H) deep[d][e]++;
          }
        }
        lastHow = 'j';
        checkRecord();
        continue;
      }
      if (m > 0) addInterval(x - m, x - 1);
      addInterval(x + k + 1, x + k + 1 + m);
      n = endTime; v = x + k + 1 + m;
      lastHow = 'f';
      checkRecord();
      break;
    }
    if (!quiet && n >= nextReport) {
      double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
      // holes among the small numbers: missing numbers below 10^6 and 10^7, by residue mod 3
      u64 m6[3] = {0, 0, 0}, m7[3] = {0, 0, 0}; u64 prevHi = 0; bool firstIv = true;
      for (auto& [lo, hi] : V) {
        if (!firstIv) for (u64 z = prevHi + 1; z < lo && z < 10000000ULL; z++) { m7[z % 3]++; if (z < 1000000ULL) m6[z % 3]++; }
        if (lo >= 10000000ULL) break;
        firstIv = false; prevHi = hi;
      }
      printf("progress: n=%.3e  phases=%llu  jumps=%llu  intervals=%zu  smallest missing=%llu  "
             "missing<1e6 by class=(%llu,%llu,%llu)  missing<1e7 by class=(%llu,%llu,%llu)  (%.1fs)\n",
             (double)n, phases, jumps, V.size(), smallestMissing, m6[0], m6[1], m6[2], m7[0], m7[1], m7[2], secs);
      fflush(stdout);
      while (nextReport <= n) nextReport *= 10;
    }
  }

  // summary of the visited set at step N
  u64 missing = 0, holes = 0, w1 = 0, w2 = 0, w3 = 0;
  std::vector<u64> firstMissing;
  u64 prevHi = 0; bool firstIv = true;
  for (auto& [lo, hi] : V) {
    if (!firstIv) {
      u64 glo = prevHi + 1, ghi = lo - 1;      // gap [glo, ghi]
      if (glo <= N) {
        u64 top = ghi < N ? ghi : N;
        u64 w = top - glo + 1;
        missing += w; holes++;
        if (w == 1) w1++; else if (w == 2) w2++; else w3++;
      }
      for (u64 z = glo; z <= ghi && firstMissing.size() < 20; z++) firstMissing.push_back(z);
    }
    firstIv = false;
    prevHi = hi;
  }
  double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  printf("N=%llu a(N)=%llu\n", N, v);
  printf("smallest missing=%llu  missing in [1,N]=%llu  holes=%llu (w1=%llu w2=%llu w3+=%llu)\n",
         smallestMissing, missing, holes, w1, w2, w3);
  printf("first missing numbers (mod 3):");
  for (u64 z : firstMissing) printf(" %llu(%llu)", z, z % 3);
  printf("\nphases=%llu jumps=%llu ordinary steps=%llu intervals=%zu scan steps=%llu time=%.2fs\n",
         phases, jumps, genericSteps, V.size(), scanSteps, secs);
  if (stats) {
    printf("\njump landings per decade of the step number:\n");
    printf("decade   jumps      | landing < 10^e above diagonal, e=3..9 | landing on a number < 10^e, e=3..9\n");
    for (int d = 0; d < 20; d++) {
      if (!jumpsInDecade[d]) continue;
      printf("1e%-2d %10llu  |", d, jumpsInDecade[d]);
      for (int e = 3; e <= 9; e++) printf(" %7llu", nearDiag[d][e]);
      printf("  |");
      for (int e = 3; e <= 9; e++) printf(" %7llu", deep[d][e]);
      printf("\n");
    }
  }
  return 0;
}

// Fresh-frontier shadow test (Phase 5, steps 1-2).
// Runs the real walk with the exact zigzag-skipping algorithm. When a cascade starts (a zigzag
// starting on a number below B), it forks a "shadow" walk that keeps only the visited numbers
// below B plus whatever the real walk wrote in its last few phases, and treats every other
// number >= B as free. If cascades are driven only by the small holes and their own writes,
// the shadow eats the same holes in the same order as the real walk.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <vector>
#include <deque>
#include <functional>
typedef unsigned long long u64; typedef unsigned __int128 u128;
typedef std::map<u64, u64> IMap;
#include "walk.hpp"
struct WalkUnused {
  IMap V; u64 n = 0, v = 0;
  std::deque<std::pair<u64,u64>>* log = nullptr;  // records written intervals if set
  bool visited(u64 y) const { auto it = V.upper_bound(y); if (it == V.begin()) return false; --it; return it->second >= y; }
  u64 predVisited(u64 x) const { auto it = V.upper_bound(x - 1); --it; return (it->second >= x - 1) ? x - 1 : it->second; }
  void add(u64 lo, u64 hi) {
    if (log) { log->push_back({lo, hi}); if (log->size() > 64) log->pop_front(); }
    auto it = V.upper_bound(lo);
    if (it != V.begin()) { auto p = std::prev(it); if (p->second + 1 >= lo) it = p; }
    u64 nlo = lo, nhi = hi;
    while (it != V.end() && it->first <= hi + 1) { if (it->first < nlo) nlo = it->first; if (it->second > nhi) nhi = it->second; it = V.erase(it); }
    V.emplace(nlo, nhi);
  }
  u64 firstFreeInClass(u64 P, u64 lowb) const {
    u64 y = P;
    for (;;) {
      if (y < lowb) return 0;
      auto it = V.upper_bound(y);
      if (it == V.begin()) return y;
      --it;
      if (it->second < y) return y;
      u64 lo = it->first; if (lo == 0) return 0;
      u64 t = lo - 1; u64 r = (t % 3 + 3 - P % 3) % 3; if (t < r) return 0; y = t - r;
    }
  }
  // One ordinary step followed (if it went back) by a chain of zigzags. cb(k, x) is called at
  // each zigzag start; if it returns false the walk stops before running that zigzag.
  bool phase(u64 N, const std::function<bool(u64,u64)>& cb) {
    u64 k1 = n + 1; bool back = false;
    if (v > k1 && !visited(v - k1)) { v -= k1; back = true; } else v += k1;
    n = k1; add(v, v);
    if (!back) return true;
    return chain(N, cb);
  }
  bool chain(u64 N, const std::function<bool(u64,u64)>& cb) {
    for (;;) {
      if (n >= N) return true;
      u64 k = n, x = v;
      if (!cb(k, x)) return false;
      u64 g = predVisited(x), r = x - 1 - g, jstar = ~0ULL, y = 0;
      if (x > k + 1) {
        u64 P = x - k - 1; u128 t3 = (u128)3 * r;
        u64 lowb = ((u128)P > t3) ? (u64)(P - (u64)t3) : 1; if (lowb < 1) lowb = 1;
        y = firstFreeInClass(P, lowb); if (y) jstar = (P - y) / 3;
      }
      bool jump = jstar <= r; u64 m = jump ? jstar : r; u64 end = k + 2 * m + 1;
      if (end > N) {
        u64 d = N - k, i = d / 2;
        if (i > 0) add(x - i, x - 1);
        if (d % 2 == 0) { if (i > 0) add(x + k + 1, x + k + i); v = x - i; } else { add(x + k + 1, x + k + 1 + i); v = x + k + 1 + i; }
        n = N; return true;
      }
      if (jump) { if (m > 0) { add(x - m, x - 1); add(x + k + 1, x + k + m); } n = end; v = y; add(y, y); continue; }
      if (m > 0) add(x - m, x - 1);
      add(x + k + 1, x + k + 1 + m); n = end; v = x + k + 1 + m; return true;
    }
  }
};
int main(int argc, char** argv) {
  u64 N = strtoull(argv[1], 0, 10), B = strtoull(argv[2], 0, 10), KMIN = argc > 3 ? strtoull(argv[3], 0, 10) : 0;
  Walk real; std::deque<std::pair<u64,u64>> recent; real.log = &recent;
  real.add(0, 0);
  bool inC = false; u64 since = 0; std::vector<u64> realSeq;
  long nC = 0, nExact = 0;
  auto finishCascade = [&](const std::vector<u64>& shadowSeq) {
    size_t p = 0; while (p < realSeq.size() && p < shadowSeq.size() && realSeq[p] == shadowSeq[p]) p++;
    bool exact = (p == realSeq.size() && p == shadowSeq.size());
    nC++; nExact += exact;
    u64 rmin = ~0ULL, smin = ~0ULL; for (u64 z : realSeq) rmin = z < rmin ? z : rmin; for (u64 z : shadowSeq) smin = z < smin ? z : smin;
    printf("cascade %ld: real eats %zu holes (lowest %llu), shadow %zu (lowest %llu), agree on first %zu%s\n",
           nC, realSeq.size(), rmin, shadowSeq.size(), smin, p, exact ? "  EXACT" : "");
    fflush(stdout);
  };
  std::vector<u64> shadowSeq;
  while (real.n < N) {
    real.phase(N, [&](u64 k, u64 x) {
      bool deep = x < B;
      if (inC) {
        if (deep) { realSeq.push_back(x); since = 0; }
        else if (++since > 6) { inC = false; finishCascade(shadowSeq); }
      } else if (deep && k >= KMIN) {
        // fork the shadow walk at this zigzag start
        Walk sh; sh.n = k; sh.v = x;
        for (auto& [lo, hi] : real.V) { if (lo >= B) break; sh.V.emplace(lo, hi < B ? hi : B - 1); }
        for (auto& [lo, hi] : recent) sh.add(lo, hi);       // the real walk's last writes
        shadowSeq.clear(); u64 sSince = 0; bool stop = false;
        auto scb = [&](u64 k2, u64 x2) {
          if (x2 < B) { shadowSeq.push_back(x2); sSince = 0; } else if (++sSince > 6) { stop = true; return false; }
          return true;
        };
        sh.chain(~0ULL, scb);
        for (long guard = 0; !stop && guard < 2000000; guard++) sh.phase(~0ULL, scb);
        inC = true; since = 0; realSeq.clear(); realSeq.push_back(x);
      }
      return true;
    });
  }
  printf("cascades compared: %ld, exact agreement: %ld\n", nC, nExact);
}

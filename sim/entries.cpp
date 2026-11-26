// Phase 5 step 1: run the fresh-frontier cascade model on Chaffin's holes below 2^32 (after
// 10^612 steps), entering at every hole the way cascades enter: a level-1 scan whose first jump
// test is that hole. Everything above 2^32 is treated as free except what the cascade writes.
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <utility>
#include "walk.hpp"
int main(int argc, char** argv) {
  const u64 B = 1ULL << 32;
  std::vector<std::pair<u64,u64>> holes;
  FILE* f = fopen(argv[1], "r"); char line[256];
  while (fgets(line, sizeof line, f)) { u64 lo, hi; int c = sscanf(line, "%llu - %llu", &lo, &hi); if (c == 1) hi = lo; if (c >= 1) holes.push_back({lo, hi}); }
  Walk base; u64 prev = 0;                          // visited = [0, B) minus the holes
  for (auto& [lo, hi] : holes) { if (lo > prev) base.V.emplace(prev, lo - 1); prev = hi + 1; }
  base.V.emplace(prev, B - 1);
  const u64 Ts[6] = {1000000000000000000ULL, 1000000000000000001ULL, 1000000000000000002ULL,
                     1000000000000000003ULL, 1000000000000000004ULL, 1000000000000000005ULL};
  long reach852655 = 0, below976368 = 0, total = 0; u64 globalMin = ~0ULL;
  // entry list: by default the top of every hole run (first test = the hole); with a second
  // argument, a file of first-test values P (the scan starts at height P + 1)
  std::vector<u64> starts;
  if (argc > 2) { FILE* g = fopen(argv[2], "r"); u64 P; while (fscanf(g, "%llu", &P) == 1) starts.push_back(P); }
  else for (auto& [hlo, hhi] : holes) starts.push_back(hhi);
  for (u64 y : starts) for (u64 T : Ts) {
    Walk w = base; w.n = T; w.v = T + y + 1; w.add(w.v, w.v);
    u64 mn = ~0ULL; long eaten = 0, since = 0; bool stop = false, hit = false;
    auto cb = [&](u64 k, u64 x) {
      if (x < B) { since = 0; eaten++; if (x < mn) mn = x; if (x == 852655) hit = true; }
      else if (++since > 6) { stop = true; return false; }
      return true;
    };
    w.chain(~0ULL, cb);
    for (long g = 0; !stop && g < 200000; g++) w.phase(~0ULL, cb);
    total++; reach852655 += hit; below976368 += (mn < 976368); if (mn < globalMin) globalMin = mn;
    if (T == Ts[0]) printf("entry %llu: eats %ld, lowest %llu%s\n", y, eaten, mn, hit ? "  REACHES 852655" : "");
  }
  printf("runs: %ld (each hole-run top x 6 start times); lowest reached %llu; runs below 976368: %ld; runs reaching 852655: %ld\n",
         total, globalMin, below976368, reach852655);
}

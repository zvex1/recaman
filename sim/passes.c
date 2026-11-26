#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc,char**argv){ uint64_t N=strtoull(argv[1],0,10); uint64_t cap=8*N+64;
 uint8_t*s=calloc(cap/8+1,1); uint64_t a=1; s[0]|=1; s[1]|=2;
 uint64_t passStart=1, below=0, firstBelow=0, minLevSeen=99;
 for(uint64_t n=1;n<N;n++){ uint64_t q=a/n, r=a%n; int wrap = r<q;
  if(q<minLevSeen)minLevSeen=q;
  int back=0; uint64_t k=n+1; if(a>k){uint64_t b=a-k; if(!(s[b>>3]>>(b&7)&1)) back=1;}
  if(wrap){ printf("pass [%llu,%llu] ratio %.3f  wrap at level %llu (%s, off %llu)  min level in pass %llu  steps below diag %llu  first below at %.4f of pass\n",
     (unsigned long long)passStart,(unsigned long long)n,(double)n/passStart,(unsigned long long)q,back?"back":"fwd",(unsigned long long)r,(unsigned long long)minLevSeen,(unsigned long long)below, below? (double)(firstBelow-passStart)/(n-passStart+1):-1.0);
     passStart=n+1; below=0; minLevSeen=99; }
  a = back? a-k : a+k; s[a>>3]|=1<<(a&7);
  if(a<k){ if(!below) firstBelow=k; below++; }
 } return 0;}

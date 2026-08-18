"""projection, Prop A.8: make the ORIGINAL defect concrete, and check the repaired test.

The old acceptance rule required the per-step outputs of the q copies to be literally equal at
every step. The repair compares COMPLETED outputs, carrying the unmatched cross-copy delay in a
buffer. The referee said the old rule rejects runs whose completed outputs agree; this exhibits
such runs in explicit subsequential transducers with bounded terminal output.
"""
import sys, random, itertools
sys.stdout.reconfigure(encoding='utf-8', errors='replace')

def run(T, tau, w):
    """T[(state,letter)] = (out, next); returns (completed output, per-step outputs)"""
    s=0; steps=[]; out=''
    for a in w:
        o,s = T[(s,a)]
        steps.append(o); out+=o
    out += tau[s]
    return out, steps

def make(rng, nstates=3, L=2):
    T={}; 
    for s in range(nstates):
        for a in '01':
            o=''.join(rng.choice('01') for _ in range(rng.choice([0,0,1,1,2])))
            T[(s,a)]=(o, rng.randrange(nstates))
    tau=[''.join(rng.choice('01') for _ in range(rng.randrange(L+1))) for _ in range(nstates)]
    return T, tau

rng=random.Random(3)
print(f'{"trial":>5} {"pairs colliding":>16} {"of those, per-step UNEQUAL":>27} {"old rule loses":>15}')
tot_coll=0; tot_lost=0
for trial in range(12):
    T,tau = make(rng)
    words=[''.join(t) for t in itertools.product('01', repeat=6)]
    res={w: run(T,tau,w) for w in words}
    coll=0; lost=0
    for u,v in itertools.combinations(words,2):
        ou,su = res[u]; ov,sv = res[v]
        if ou==ov:
            coll+=1
            if su!=sv: lost+=1
    tot_coll+=coll; tot_lost+=lost
    print(f'{trial:5d} {coll:16d} {lost:27d} {("YES" if lost else "no"):>15}')
print(f'\ntotals: colliding pairs {tot_coll}, of which the per-step rule rejects {tot_lost}'
      f'  ({100*tot_lost/max(1,tot_coll):.1f} percent)')
print()
print('--- one explicit witness ---')
T,tau = make(random.Random(3))
words=[''.join(t) for t in itertools.product('01', repeat=6)]
res={w: run(T,tau,w) for w in words}
for u,v in itertools.combinations(words,2):
    ou,su=res[u]; ov,sv=res[v]
    if ou==ov and su!=sv:
        print(f'   inputs {u} and {v}')
        print(f'   completed outputs both {ou!r}  -> they DO collide')
        print(f'   per-step emissions {su} vs {sv}  -> the old rule rejects the pair')
        break

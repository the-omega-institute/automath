# Standalone Sage/Python reproduction certificate for the finite window-6 audit.
# Run with: sage supplement/window6_audit_certificate.sage
# This file intentionally mirrors the executable artifact printed in
# Appendix A of the manuscript.
from hashlib import sha256
from itertools import product

fib=[0,1]
while len(fib)<200:
    fib.append(fib[-1]+fib[-2])

def fold(N,m):
    z=[0]*200
    r=N
    while r>0:
        j=max(i for i in range(1,150) if fib[i+1] <= r)
        z[j-1]=1
        r-=fib[j+1]
    return ''.join(str(a) for a in z[:m])

def states(m):
    return sorted(set(fold(N,m) for N in range(2**m)))

for m,h in [(6,'3b3a9f44074afc02177af79f9f4107aea061789f817bf7d288cb9fd473cdeee5'),
            (7,'4a182c2503f6a82433ed6501cdea0997d5d274ef7b35415e3b0ec0d2cb7e7232'),
            (8,'cce73204f542296c6966285ca60f307f97a630814b9fd108c85cd3b974351c36')]:
    X=states(m)
    d=[sum(1 for N in range(2**m) if fold(N,m)==x) for x in X]
    bd=[(x,d[i]) for i,x in enumerate(X) if x[0]=='1' and x[-1]=='1']
    stream='m=%d;X=%s;d=%s;bd=%s' % (
        m, ','.join(X), ','.join(map(str,d)),
        ','.join('%s:%d' % p for p in bd))
    assert sha256(stream.encode()).hexdigest()==h

m=6
X=states(m)
idx={x:i for i,x in enumerate(X)}
d=[sum(1 for N in range(2**m) if fold(N,m)==x) for x in X]
Nmat=[[0]*len(X) for _ in X]
for bits in product([0,1], repeat=m):
    N=sum(bits[i]<<i for i in range(m))
    a=idx[fold(N,m)]
    for k in range(m):
        M=N^(1<<k)
        b=idx[fold(M,m)]
        Nmat[a][b]+=1

def bits_to_int(s):
    return int(s, 2)

def sigma_geo_word(s):
    a=[int(c) for c in s]
    return ''.join(map(str, [1-a[4], a[1], a[2], a[3], 1-a[0], a[5]]))

for s in (''.join(map(str,bits)) for bits in product([0,1], repeat=m)):
    assert fold(bits_to_int(s), m) == fold(bits_to_int(sigma_geo_word(s)), m)

def neighbor_count(source, target):
    N=bits_to_int(source)
    return sum(1 for k in range(m) if fold(N^(1 << (m-1-k)), m) == target)

assert fold(bits_to_int('000000'), m) == '000000'
assert fold(bits_to_int('010101'), m) == '000000'
assert neighbor_count('000000', '000100') == 0
assert neighbor_count('010101', '000100') == 1

rows=['%d:%s' % (i, ','.join('%d:%d' % (j,c)
      for j,c in enumerate(row) if c)) for i,row in enumerate(Nmat)]
estream='m=6;states=%s;d=%s;N=%s' % (
    ','.join(X), ','.join(map(str,d)), ';'.join(rows))
assert sha256(estream.encode()).hexdigest() == '2bbf7acda82a4c07d39ac76a621cee9751abaf253f6298d8540704146a2db4f0'

R.<t> = PolynomialRing(QQ)
P = Matrix(QQ, [[QQ(Nmat[i][j])/(6*d[i]) for j in range(len(X))]
                for i in range(len(X))])
L = 3234734993627557134336
Q = (L*(P.charpoly(t)//(t-1))).change_ring(ZZ)
coeffs = Q.list()[::-1]
assert sha256(('Q6='+','.join(map(str,coeffs))).encode()).hexdigest() == 'a4f32303d20419c1608c177dafdc43904e3831f0c2eaf6f65895d49c654667dd'

def sgn(v): return '+' if v>0 else '-' if v<0 else '0'
S = Q.sturm_sequence()
pts = [QQ(4841207858)/10**10, QQ(4841207859)/10**10,
       QQ(-6030939755)/10**10, QQ(-6030939754)/10**10]
signs = [''.join(sgn(p(a)) for p in S) for a in pts]
assert signs == ['-++++++++++++++++++++','+++++++++++++++++++++',
                 '+-+-+-+-+-+-+-+-+-+-+','--+-+-+-+-+-+-+-+-+-+']
pts = [QQ(2420603929)/5000000000, QQ(4841207859)/10000000000,
       QQ(-1206187951)/2000000000, QQ(-3015469877)/5000000000]
sst=';'.join('%s:%s' % (pts[i], signs[i]) for i in range(4))
assert sha256(sst.encode()).hexdigest() == '3f456cb31806cf82559e07691386f8a42b2a0555d409e74f2a03063238592ec0'
print('window6 finite audit certificate: all assertions passed')

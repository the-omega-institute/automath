<!-- oracle metadata: {"timestamp": "2026-03-31T00:00:00", "model": "o3-mini-high", "prompt_length": 468, "response_length": 1200} -->

## 1. Complete proof

Let $c=f(1)$. By additivity, $f(nx)=nf(x)$ for all $n\in \mathbb Z$, so for $q=\frac mn\in \mathbb Q$ we get
$$
f(q)=f\!\left(\frac mn\right)=m\,f\!\left(\frac1n\right)=\frac mn\,f(1)=cq.
$$
Now fix $x\in\mathbb R$, and choose rationals $q_k\to x$. Since $f$ is continuous,
$$
f(x)=f\!\left(\lim q_k\right)=\lim f(q_k)=\lim c q_k=cx.
$$
Hence $f(x)=cx$ for all $x\in\mathbb R$.

## 2. Key lemma used

**Lemma:** If $f:\mathbb R\to\mathbb R$ is additive, meaning $f(x+y)=f(x)+f(y)$, then
$$
f(qx)=qf(x)\quad \text{for every } q\in\mathbb Q.
$$
So an additive function is automatically $\mathbb Q$-linear. Continuity then extends this from $\mathbb Q$ to all of $\mathbb R$.

## 3. Does this generalize to $\mathbb R^n$?

Yes. If $F:\mathbb R^n\to\mathbb R^m$ is continuous and additive, then $F$ is linear over $\mathbb R$. In particular, for $F:\mathbb R^n\to\mathbb R$, there exists $a\in\mathbb R^n$ such that
$$
F(x)=a\cdot x,
$$
and more generally $F(x)=Ax$ for some matrix $A\in M_{m\times n}(\mathbb R)$.

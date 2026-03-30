# THEOREM_LIST

Catalogue of every theorem-level claim.

| # | Label | Location | Statement | Status |
|---|-------|----------|-----------|--------|
| 1 | `lem:primitive-orbit-asymptotic` | sec_preliminaries.tex:17 | Primitive orbit count satisfies $p_n(M) = \lambda^n/n + O(\max\{\Lambda(M)^n, \lambda^{n/2}\}/n)$. | Proved |
| 2 | `prop:sync-self-duality` | sec_preliminaries.tex:79 | The involution $\iota$ on the state set exchanges $B_0$ and $B_1$, giving $\Delta(z,u)=\Delta(uz,u^{-1})$. | Proved |
| 3 | `prop:kernel-delta-explicit` | sec_kernel.tex:6 | Explicit closed form of $\Delta(z,u)$ as a degree-6 polynomial in $z$ with coefficients in $\mathbb{Z}[u]$. | Proved (by direct computation; proof references elimination from the 10x10 matrix) |
| 4 | `prop:sync-kernel-spectrum` | sec_kernel.tex:27 | $\det(I-zB) = (z-1)(z+1)(3z-1)(z^3-z^2+z+1)$, $\rho(B)=3$, $C_B = 243/272$. | Proved |
| 5 | `prop:sync-hatdelta-completion` | sec_kernel.tex:61 | Completed determinant $\widehat\Delta(w,s) = 1 - sw - 5w^2 + 3sw^3 + (5-s^2)w^4 + (s^3-6s)w^5 + (s^2-1)w^6$; parity relation $\widehat\Delta(w,-s) = \widehat\Delta(-w,s)$. | Proved |
| 6 | `prop:sync-hatdelta-quotient` | sec_kernel.tex:88 | Quotient of the curve by involution $(w,s)\mapsto(-w,-s)$ is a smooth plane quartic of genus 3. | Proved |
| 7 | `prop:sync-hatdelta-double-cover` | sec_kernel.tex:116 | Two-sheeted cover branched at exactly two points; normalisation has genus 6 by Hurwitz. | Proved |
| 8 | `prop:sync-hatdelta-galois-s6-generic` | sec_kernel.tex:136 | Generic Galois group of $\widehat\Delta(w,s)$ over $\mathbb{Q}(s)$ is $S_6$. | Proved (sketch: discriminant not a square + specialisation producing transposition and 5-cycle) |
| 9 | `thm:sync-cyclotomic-degree-law` | sec_kernel.tex:166 | $\deg_w R_m = 3\varphi(2m)$ for $m \ge 4$; $R_m$ is even when $m$ is even. | Proved |
| 10 | `cor:rho-m2-closed-form` | sec_kernel.tex:185 | $R_2(w) = (1-w^2)(w^4-4w^2+1)$, $\rho_2 = \sqrt{2+\sqrt{3}}$. | Proved |
| 11 | `prop:sync-endpoint-jet` | sec_kernel.tex:213 | Endpoint jet of the analytic branch $\rho(s)$ near $s=2$: leading coefficients $w'(2)=-11/153$, $\rho'(2)=11/17$, etc. | Proved |
| 12 | `thm:rho-gap-m12` | sec_kernel.tex:242 | Asymptotic expansion of $\rho_m$ to order $O(m^{-14})$; leading gap $3 - \rho_m \sim 11\pi^2/(17m^2)$. | Proved |
| 13 | `prop:cyclic-lift-primitive-asymptotics` | sec_kernel.tex:279 | Primitive orbit count for cyclic lift $M^{\langle q\rangle} = M \otimes P_q$: vanishes for $q \nmid n$, standard asymptotics for $n = qm$. | Proved |

**Summary**: 13 theorem-level claims, all marked as proved. No claims are merely cited or assumed. External dependencies are limited to Perron--Frobenius theory, the implicit function theorem, and Hurwitz's formula, all standard.

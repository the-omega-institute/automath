<!-- oracle metadata: {"timestamp": "2026-04-11T18:06:44.262239", "model": "chatgpt-5.4-pro-extended", "response_length": 10958} -->

1. Overall assessment

Major revision

The core computation, especially Theorem 5.12, looks potentially publishable and is the strongest part of the manuscript. But the paper is not ready for acceptance in its current form because one of its main conceptual interpretations is false as written, Appendix C contains a genuine proof error, and the novelty discussion around Theorem 5.11 overstates the contrast with Gaussian entropy expansions. The last point matters because the entropic CLT literature already gives Gaussian entropy expansions in powers of 
1
/
𝑛
1/n, not with odd half-orders. 

main

 
arXiv

2. Novelty rating for each theorem

All theorem labels below refer to the attached manuscript. 

main

Theorem	Rating	One-line justification
Theorem 5.7	LOW	Useful explicit mode formula, but it is a direct generating-function consequence of the Cayley substitution.
Theorem 5.11	LOW	The parity proof is neat, but the absence of odd terms is not as distinctive as claimed at the level of entropy expansions.
Theorem 5.12	HIGH	The explicit 
𝑡
−
8
t
−8
 coefficient in centered moments through order six is the clearest new technical contribution.
Theorem 5.15	MEDIUM	The nonnegative defect decomposition is interesting, but the sixth-order part repackages Pearson and the geometric interpretation is currently overstated.
Theorem 5.16	MEDIUM	The amplification inequality appears new, but it is largely an algebraic consequence of the decomposition in Theorem 5.15.
Theorem 5.19	MEDIUM	The stability consequence is useful, though the proof is elementary once the 
Δ
6
Δ
6
	​

 formula is available.
Theorem C.1	LOW	The closed kernel formula is elegant, but appendix-level and obtained by a fairly direct residue computation.

The low rating for Theorem 5.11 is specifically because Gaussian entropy expansions already appear in powers of 
1
/
𝑛
1/n in Bobkov-Chistyakov-Götze, so the current novelty contrast is too strong. 
arXiv

3. Issue table
ID	Section	Severity	Description	Suggested fix
B1	Abstract, §1.2, §5.6	BLOCKER	The paper repeatedly says the defect coordinates are “squared orthogonal residuals” and that 
𝑄
3
Q
3
	​

 orthogonalizes 
𝑋
𝑄
2
XQ
2
	​

 against 
𝑋
X and 
𝑄
2
Q
2
	​

. With 
𝑄
3
=
𝑋
𝑄
2
−
∥
𝑄
2
∥
2
2
𝑋
−
𝛽
3
4
𝑄
2
Q
3
	​

=XQ
2
	​

−∥Q
2
	​

∥
2
2
	​

X−
4
β
3
	​

	​

Q
2
	​

, one has 
𝐸
[
𝑋
𝑄
3
]
=
0
E[XQ
3
	​

]=0 but generally 
𝐸
[
𝑄
2
𝑄
3
]
≠
0
E[Q
2
	​

Q
3
	​

]

=0. So 
∥
𝑄
3
∥
2
2
∥Q
3
	​

∥
2
2
	​

 is not the Gram-Schmidt residual variance after projection onto 
s
p
a
n
{
1
,
𝑋
,
𝑋
2
}
span{1,X,X
2
}.	Either remove all orthogonality/projection language, or redefine 
𝑄
3
Q
3
	​

 by true Gram-Schmidt and rederive (5.26) and (5.28).
M1	Appendix C, Proposition C.3	MEDIUM	The proof is incorrect as written. From 
⟨
𝑓
,
Ψ
𝜀
⟩
=
0
⟨f,Ψ
ε
	​

⟩=0 and 
∫
𝑓
 
𝑑
𝜔
=
0
∫fdω=0, one gets 
∫
𝑓
(
𝑦
)
𝑃
1
(
𝑦
−
𝜀
)
 
𝑑
𝑦
=
0
∫f(y)P
1
	​

(y−ε)dy=0, not 
𝑃
1
∗
(
𝑓
/
(
𝜋
(
1
+
𝑦
2
)
)
)
=
0
P
1
	​

∗(f/(π(1+y
2
)))=0. The stated 
𝐿
1
L
1
 injectivity argument therefore does not follow.	Replace the proof with a correct one, either via the Cayley/trigonometric representation of the modes or via tempered distributions and the nonvanishing Fourier multiplier (e^{-
M2	§1.2, especially the Theorem 5.11 bullet	MEDIUM	The Gaussian comparison is misleading. The manuscript contrasts Theorem 5.11 with Gaussian Edgeworth expansions having odd corrections, but that is a density-level comparison. For entropy, the Gaussian entropic CLT already has an expansion 
𝐷
(
𝑍
𝑛
)
=
𝑐
1
/
𝑛
+
𝑐
2
/
𝑛
2
+
⋯
D(Z
n
	​

)=c
1
	​

/n+c
2
	​

/n
2
+⋯.	Rewrite the comparison so it is entropy-to-entropy, not density-to-entropy. The specific feature here is the Cayley-Chebyshev parity mechanism, not the bare absence of odd entropy terms.
M3	Overall structure, §§1–4, §5.7, App. C–D	MEDIUM	The manuscript contains two partially disconnected stories: entropy asymptotics, and RKHS/lattice sampling. Since C–D are not used in the proofs of the main entropy theorems, the paper feels unfocused, and the abstract overweights secondary material.	Refocus the paper on Theorems 5.11–5.19. Move most of C–D to a supplement or separate note unless you make them genuinely interact with the entropy results. Compress standard preliminaries in §§3–4.
L1	Abstract, §1.1, §1.4	LOW	Appendix cross-references are inconsistent. The abstract and early introduction send the kernel/lattice material to A/B, while the actual appendices place it in C/D.	Fix all appendix labels after the final reorganization.
L2	§5.18–§5.19 and related intro prose	LOW	Under only a fourth-moment assumption, 
Δ
6
Δ
6
	​

 is being used as an algebraic moment functional extending the sixth-order coefficient formula, but the prose still calls it “the sixth-order gap” without qualification.	State explicitly that the asymptotic interpretation needs stronger moments; in Theorem 5.19 only the algebraic extension is used.
L3	References around Pearson inequality	LOW	The paper cites only recent/secondary sources for Pearson’s inequality and misses the classical provenance.	Add Pearson (1916) and Wilkins (1944), and adjust the wording to credit the classical inequality properly.

The mathematically substantive points are B1 and M1. B1 comes from the definitions and claims around 
𝑄
3
Q
3
	​

 in §5.6. M1 comes from the proof of Proposition C.3. M2 is supported by the Gaussian entropic CLT expansion 
𝐷
(
𝑍
𝑛
)
=
𝑐
1
/
𝑛
+
𝑐
2
/
𝑛
2
+
⋯
D(Z
n
	​

)=c
1
	​

/n+c
2
	​

/n
2
+⋯. 

main

 
arXiv

4. Missing references

The two most important missing citations are these:

Karl Pearson (1916), Mathematical Contributions to the Theory of Evolution. XIX. Second Supplement to a Memoir on Skew Variation. This is the classical provenance for the skewness-kurtosis constraint the paper invokes around Theorem 5.15. 
Royal Society Publishing
+1

J. Ernest Wilkins Jr. (1944), A Note on Skewness and Kurtosis, Annals of Mathematical Statistics 15(3), 333–335. This is a standard short reference for the inequality and should be cited if Theorem 5.15 is presented as repackaging Pearson’s relation. 
Project Euclid
+1

I would also recommend revising the prose around Theorem 5.11 to engage more accurately with the already cited Gaussian entropic expansion paper of Bobkov-Chistyakov-Götze, because that literature is directly relevant to the manuscript’s comparison sentence. 
arXiv

5. Specific improvements needed to reach acceptance

First, the paper must stop claiming an orthogonal-residual geometry unless it is actually proved. Right now that interpretation is wrong, and it appears in the abstract, introduction, and §5.6. 

main

Second, Proposition C.3 needs a correct proof. This is not just polish. The current argument does not establish the stated density result. 

main

Third, the novelty section needs to be rewritten in a more careful and less categorical way. In particular, the Theorem 5.11 comparison to the Gaussian case should be corrected, and the Pearson discussion should cite the classical sources. 

main

 
arXiv
+2
Project Euclid
+2

Fourth, the manuscript should be refocused. The entropy asymptotics are the real contribution. The RKHS/sampling appendices are currently too detached and take space and attention away from the main theorem sequence. 

main

Fifth, the paper needs a full editorial pass: appendix labels, theorem cross-references, and the status of 
Δ
6
Δ
6
	​

 under weaker moment assumptions should all be cleaned up. 

main

6. Concrete fixes
B1. False orthogonal-residual interpretation

Actionable solution

Use one of these two routes:

Minimal-change route. Keep the formulas in Theorems 5.15 and 5.16, but remove every claim that 
𝑄
3
Q
3
	​

 is an orthogonal projection residual. Replace phrases like “squared orthogonal residuals,” “orthogonalizes against 
𝑋
X and 
𝑄
2
Q
2
	​

,” and “residual variance in 
𝑋
3
X
3
 after projection onto 
s
p
a
n
{
1
,
𝑋
,
𝑋
2
}
span{1,X,X
2
}” by a weaker but correct description such as “nonnegative defect coordinates chosen to make the coefficient decomposition positive.”

Structural route. If you want a true geometric interpretation, redefine

𝑄
~
3
=
𝑋
𝑄
2
−
⟨
𝑋
𝑄
2
,
𝑋
⟩
∥
𝑋
∥
2
𝑋
−
⟨
𝑋
𝑄
2
,
𝑄
2
⟩
∥
𝑄
2
∥
2
𝑄
2
Q
	​

3
	​

=XQ
2
	​

−
∥X∥
2
⟨XQ
2
	​

,X⟩
	​

X−
∥Q
2
	​

∥
2
⟨XQ
2
	​

,Q
2
	​

⟩
	​

Q
2
	​


when 
𝑄
2
≠
0
Q
2
	​


=0, handle 
𝑄
2
=
0
Q
2
	​

=0 separately, and then rederive the analogues of (5.26) and (5.28). This is a genuine rewrite, not a cosmetic edit.

I strongly recommend the minimal-change route unless the geometric viewpoint is central to your intended contribution. 

main

M1. Incorrect proof of Proposition C.3

Actionable solution

Replace the current proof by one of the following:

Fourier-series/Cayley proof. Identify 
𝐿
2
(
𝜔
)
L
2
(ω) with 
𝐿
2
(
−
𝜋
/
2
,
𝜋
/
2
)
L
2
(−π/2,π/2) via 
𝑦
=
tan
⁡
𝜃
y=tanθ. Use Theorem 5.7 to show that the mode functions generate the nonconstant trigonometric system. Then use the 
𝐿
2
L
2
-power series

Ψ
𝜀
=
∑
𝑛
≥
1
𝑢
𝑛
 
𝜀
𝑛
−
1
Ψ
ε
	​

=
n≥1
∑
	​

u
n
	​

ε
n−1

for 
∣
𝜀
∣
∣ε∣ small to conclude that each 
𝑢
𝑛
u
n
	​

 lies in the closure of 
s
p
a
n
{
Ψ
𝜀
}
span{Ψ
ε
	​

}, hence that this span is dense in 
𝐿
0
2
(
𝜔
)
L
0
2
	​

(ω).

Distributional Fourier proof. Show that orthogonality to all 
Ψ
𝜀
Ψ
ε
	​

 implies 
𝑃
1
∗
𝑓
=
0
P
1
	​

∗f=0 in the sense of tempered distributions, then use that 
𝑃
1
^
(
𝜉
)
=
𝑒
−
∣
𝜉
∣
P
1
	​

	​

(ξ)=e
−∣ξ∣
 never vanishes to conclude 
𝑓
^
=
0
f
	​

=0, hence 
𝑓
=
0
f=0.

Either route is fine. The current weighted-
𝐿
1
L
1
 convolution argument should be removed. 

main

M2. Misframed novelty claim for Theorem 5.11

Actionable solution

Rewrite the relevant paragraph in §1.2 along these lines:

“Theorem 5.11 shows that in the fixed-
𝜈
ν, large-
𝑡
t Poisson-Cauchy regime, the entropy expansion admits a particularly transparent parity derivation via Cayley-Chebyshev modes. We do not claim that the absence of odd terms is unique among entropy expansions. Rather, the specific mechanism and the fixed-
𝜈
ν Poisson-Cauchy setting appear to be distinctive here.”

That wording is accurate and still leaves room for novelty. It also avoids conflating density Edgeworth corrections with entropy asymptotics. 
arXiv

M3. Refocus the manuscript

Actionable solution

A cleaner journal version would look like this:

Compress §§3–4 to a short preliminaries section or move routine material to an appendix.

Keep Appendix A and Appendix B only if they materially support Theorem 5.12.

Move most of Appendices C–D to supplementary material unless you explicitly use them in the main theorem chain.

Shorten the abstract so it leads with Theorems 5.12, 5.15, 5.16, and 5.19, and mentions the RKHS material only briefly, if at all.

That would make the paper read like one paper rather than two adjacent notes. 

main

If the authors fix B1, M1, and M2 properly, and tighten the paper’s scope, I would be open to a substantially revised resubmission.
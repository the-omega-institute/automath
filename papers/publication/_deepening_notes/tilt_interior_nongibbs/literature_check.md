# Literature and novelty check

Date: 2026-08-02. Scope: cylinder-information variance rigidity for full-support non-Gibbs measures on mixing shifts of finite type.

## Search method and arXiv API record

The arXiv Atom API (`https://export.arxiv.org/api/query`) was queried directly before drafting. The searches included:

```text
all:"g-measures" AND all:Keane
ti:"g-measures"
all:"Bramson-Kalikow"
ti:"Chains with complete connections"
all:"Gibbs measures" AND all:"shift of finite type"
all:"information function" AND all:"asymptotic variance"
all:"entropy variance" AND all:symbolic
all:"Parry measure" AND all:rigidity
all:"Parry measure"
all:"Square summability of variations" AND all:"g-measures"
all:"cylinder information" AND (all:"g-measure" OR all:"Parry measure")
```

The API returned the directly relevant records `arXiv:1106.4188`, `arXiv:1302.1267`, `arXiv:1110.6530`, `arXiv:1004.0650`, `arXiv:math/0509109`, `arXiv:math/0612131`, `arXiv:math/0305025`, and `arXiv:math/0305026`, together with Parry-measure records including `arXiv:1409.0946`, `arXiv:1308.2996`, `arXiv:1807.07208`, and `arXiv:2005.03282`. The arXiv HTML author/title search separately located `arXiv:math/0401093`. The final exact API query `all:"cylinder information" AND (all:"g-measure" OR all:"Parry measure")` returned a result count of zero. This is evidence of novelty, not proof of novelty.

The export endpoint rate-limited later requests with HTTP 429; successful responses and the arXiv abstract pages were cross-checked against DOI metadata. No claim below relies on absence from arXiv alone.

## Exact citations and relevance

1. **Keane and the definition of g-measures.** M. Keane, “Strongly mixing g-measures,” *Inventiones Mathematicae* 16 (1972), 309–324. DOI: `10.1007/BF01418784`. This predates arXiv. It supplies the classical normalized g-function framework, not the cylinder-information rigidity theorem proved in `note.tex`.

2. **Bramson--Kalikow nonuniqueness.** M. Bramson and S. Kalikow, “Nonuniqueness in g-functions,” *Israel Journal of Mathematics* 84 (1993), 153–160. DOI: `10.1007/BF02761697`; no original arXiv posting found. Modern quantitative treatments found by the API include C. Gallesco, S. Gallo, and D. Y. Takahashi, “Explicit estimates in the Bramson--Kalikow model,” *Nonlinearity* 27 (2014), 2281–2296, `arXiv:1302.1267`, DOI: `10.1088/0951-7715/27/9/2281`, and Gallo et al., “Attractive regular stochastic chains: perfect simulation and phase transition,” `arXiv:1110.6530`. These show that regularity of g does not imply uniqueness or projective contraction. They justify keeping condition (G) explicit.

3. **Regular g-measures can be non-Gibbs.** R. Fernández, S. Gallo, and G. Maillard, “Regular g-measures are not always Gibbsian,” *Electronic Communications in Probability* 16 (2011), 732–740. `arXiv:1106.4188`; DOI: `10.1214/ECP.v16-1681`. The paper proves that its visible-renewal law is continuous, non-null, unique, and non-Gibbsian. The banked note cites that published theorem and independently checks the two hypotheses (D) and (G); it does not reproduce the authors’ non-Gibbsianness proof.

4. **Chains with complete connections versus Gibbs measures.** R. Fernández and G. Maillard, “Chains with complete connections and one-dimensional Gibbs measures,” *Electronic Journal of Probability* 9 (2004), 145–176, `arXiv:math/0305025`, DOI: `10.1214/EJP.v9-149`. Their companion “Chains with complete connections: General theory, uniqueness, loss of memory and mixing properties” is `arXiv:math/0305026`. These works delimit when one-sided and two-sided specifications agree; the banked class does not assume that agreement.

5. **Square-variation g-measure theory.** A. Johansson and A. Öberg, “Square summability of variations and convergence of the transfer operator,” *Ergodic Theory and Dynamical Systems* 28 (2008), 1145–1151, `arXiv:math/0612131`, DOI: `10.1017/S0143385707000788`. Related API records include “Unique Bernoulli g-measures,” `arXiv:1004.0650`, and “Countable state shifts and uniqueness of g-measures,” `arXiv:math/0509109`, DOI: `10.1353/ajm.2007.0044`. These establish uniqueness/convergence results under variation assumptions. They do not identify zero cylinder-information variance with the MME under the sub-root Gordin hypotheses used here.

6. **Bowen--Ruelle Gibbs theory.** R. Bowen, *Equilibrium States and the Ergodic Theory of Anosov Diffeomorphisms*, LNM 470 (1975; Springer reprint 2008, ISBN `978-3-540-77605-5`); D. Ruelle, *Thermodynamic Formalism* (1978; later editions exist). These sources give the Gibbs property, transfer-operator spectral theory, and the standard coboundary criterion for zero variance in Hölder classes. The new note does not present that criterion as new. Its contribution is a proof using only cylinder distortion plus an observable-specific Gordin condition, and the inclusion of a published DLR-non-Gibbs renewal family.

7. **Information function and entropy fluctuations.** J.-R. Chazottes and E. Ugalde, “Entropy estimation and fluctuations of hitting and recurrence times for Gibbsian sources,” *Discrete and Continuous Dynamical Systems B* 5 (2005), 565–586, `arXiv:math/0401093`, DOI: `10.3934/dcdsb.2005.5.565`. The arXiv abstract explicitly compares hitting-time fluctuations with inverse cylinder measures. This is Gibbs-source fluctuation theory, not the non-Gibbs rigidity statement here. Classical information-function limit theory also appears in P. C. Shields, *The Ergodic Theory of Discrete Sample Paths* (AMS, 1996), and in Gordin-type martingale approximations; these are background for existence/CLT questions, not a source for the theorem proved here.

8. **Parry measure and maximal entropy.** W. Parry, “Intrinsic Markov chains,” *Transactions of the AMS* 112 (1964), 55–66, DOI: `10.1090/S0002-9947-1964-0161372-1` (also JSTOR DOI: `10.2307/1994294`). This gives the intrinsic Markov chain/unique MME on a mixing SFT. Recent arXiv records returned by the search include “Effective uniqueness of Parry measure and exceptional sets in ergodic theory,” `arXiv:1409.0946`, and “The natural measure of a symbolic dynamical system,” `arXiv:1308.2996`. None states the sub-root Gordin g-measure cylinder-information characterization.

## Novelty assessment

The theorem in `note.tex` should be described narrowly:

- It proves an exact variance formula for cylinder information in the explicitly defined class `SRG(A)` of full-support regular g-measures satisfying sub-root cylinder distortion (D) and uniform Gordin summability (G).
- Within that class it proves zero cylinder-information variance if and only if the measure is Parry/MME.
- The class is demonstrably not contained in the DLR/SRB Gibbs class: the Fernández--Gallo--Maillard renewal example lies in it and is non-Gibbsian.
- It strengthens the elementary periodic-orbit objection by giving a stationary **full-support** atomic zero-variance non-MME outside the regular g class.

No source found in the API queries states this combination. However, “largest natural class” is not claimed: removing (G), admitting root-order cylinder distortion, or finding an ergodic full-support zero-variance counterexample beyond the class are explicit open interfaces.

## Claims deliberately not made

- Not all regular g-measures are covered.
- Square-summable variations alone are not asserted to imply the exact uniform Gordin condition used here.
- The Bramson--Kalikow measures are not asserted to have zero cylinder-information variance.
- The full-support atomic counterexample is not ergodic and is not a regular positive g-measure.
- arXiv search non-detection is not treated as conclusive priority evidence.

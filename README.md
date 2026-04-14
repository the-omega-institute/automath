# The Omega Project

[![Daily Build](https://github.com/the-omega-institute/automath/actions/workflows/daily-build.yml/badge.svg)](https://github.com/the-omega-institute/automath/actions/workflows/daily-build.yml)
[![PR Gate](https://github.com/the-omega-institute/automath/actions/workflows/pr-gate.yml/badge.svg)](https://github.com/the-omega-institute/automath/actions/workflows/pr-gate.yml)
[![License: GPOL](https://img.shields.io/badge/license-GPOL-blue.svg)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean-4-blue?logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHdpZHRoPSIxNiIgaGVpZ2h0PSIxNiI+PHRleHQgeD0iMCIgeT0iMTIiIGZvbnQtc2l6ZT0iMTIiPkw8L3RleHQ+PC9zdmc+)](https://lean-lang.org)
[![Axioms: 0](https://img.shields.io/badge/axioms-0-brightgreen.svg)](#status)
[![Theorems: 3,427+](https://img.shields.io/badge/theorems-3%2C427%2B-orange.svg)](#status)

> An auditable theory compiler that derives, verifies, visualizes, and publishes mathematics from a single equation.

[中文版](README.zh-CN.md) · **[Why Everything Is Inevitable](docs/INEVITABILITY.md)** — understand the forcing chain in 10 minutes · **[Dossier](https://the-omega-institute.github.io/automath/)** · [Live autoresearch stream](https://www.youtube.com/live/pn_W3I5-qdo)

## Quick Start

```bash
# Clone and build
git clone https://github.com/the-omega-institute/automath.git
cd automath/lean4 && lake build
```

Mathlib is fetched and cached automatically on first build.

```bash
# Reproduce the theory paper
cd theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence
pip install -r requirements.txt
python3 scripts/run_all.py    # generates all figures/tables
latexmk -pdfxe main.tex       # compiles the paper
```

## The Question

What mathematical structures are inevitable when you can only observe a dynamical system through a finite binary window?

Consider the simplest setup: a system, a window, one bit per time step. Record the output for $m$ steps. The full microstate space $\{0,1\}^m$ has $2^m$ elements, but only those stable across resolutions — binary words with no consecutive 1s — survive. There are $F_{m+2}$ of them (Fibonacci numbers). This constraint is not chosen. It is forced by cross-resolution consistency. Its characteristic equation is $x^2 = x + 1$ .

The Omega project takes this single forced constraint and follows every consequence. In Lean 4. With zero axioms. The methodology is *derive, discover, name*: build rigorously from first principles, observe what structures appear, then identify their correspondences across mathematics and physics.

Every theorem is machine-verified. Every derivation chain is traceable. No axioms are assumed beyond Lean 4's core logic and Mathlib.

## The Seed

The set $X_m$ of binary words of length $m$ with no two consecutive 1s is the **golden-mean shift** — the simplest non-trivial subshift of finite type in symbolic dynamics.

- $|X_m| = F_{m+2}$ (the Fibonacci numbers)
- Every $n < F_{m+2}$ has a unique **Zeckendorf representation** as a sum of non-consecutive Fibonacci numbers, giving a canonical bijection $X_m \leftrightarrow \{0, \ldots, F_{m+2}-1\}$
- The **fold operator** $\Phi: X_{m+1} \to X_m$ (truncate the last bit) partitions words into **fibers** whose multiplicity structure encodes deep arithmetic

From these three ingredients, everything below is *derived*.

## What Emerges

### I. Nascent Arithmetic

The Zeckendorf bijection induces addition $\oplus$ and multiplication $\otimes$ directly on binary words. No integers are needed — the arithmetic is *native* to $X_m$ .

$$X_m \;\cong\; \mathbb{Z}/F_{m+2}\mathbb{Z}$$

This isomorphism (`stableValueRingEquiv`) shows that the combinatorial space $X_m$ *is* a cyclic ring, with the Fibonacci number as modulus. When $F_{m+2}$ is prime (e.g., $F_3 = 2$ , $F_5 = 5$ , $F_7 = 13$ , $F_{13} = 233$ ), $X_m$ becomes a finite field (`instFieldOfPrime`). When $F_{m+2}$ factors, the Chinese Remainder Theorem decomposes $X_m$ into a product ring (`crtDecomposition`): for instance, $X_7 \cong \mathbb{Z}/2 \times \mathbb{Z}/17$ .

What's surprising: the ring structure is *intrinsic* to the no-consecutive-1s constraint. It doesn't require importing integer arithmetic — it emerges from the Zeckendorf structure alone.

**Bridge to known mathematics:** This is a concrete instance of a quotient ring arising from a combinatorial coding constraint, connecting numeration systems (Zeckendorf, Ostrowski) to finite field theory and modular arithmetic.

### II. Fiber Spectrum and Moment Theory

The fold operator $\Phi: X_{m+1} \to X_m$ creates fibers $\Phi^{-1}(x)$ whose cardinalities $d(x)$ vary across $X_m$ . The **moment sums** quantify this variation:

$$S_q(m) = \sum_{x \in X_m} d(x)^q$$

Basic identities: $S_0(m) = F_{m+1}$ (count of stable points), $S_1(m) = 2^m$ (total words split across fibers). The higher moments encode progressively finer information about the fiber distribution.

**The S₂ recurrence** — the project's first unconditional infinite-family theorem:

$$S_2(m+3) + 2\,S_2(m) = 2\,S_2(m+2) + 2\,S_2(m+1)$$

Proved in 4 lines of Lean from a 6-step chain (hidden bit decomposition → fold congruence → collision decomposition → telescoping → cross-correlation shift → recurrence), with zero `native_decide`. A purely combinatorial quantity satisfying a linear recurrence with small integer coefficients — hidden linearity in the fiber dynamics.

**Bridge to known mathematics:** The companion matrices governing $S_q$ recurrences are related to transfer operators in statistical mechanics. The moment hierarchy parallels the moment problem in probability theory and the partition function approach in thermodynamic formalism.

### III. Collision Kernel and Spectral Theory

The $S_q$ recurrences are governed by **collision kernel matrices** whose spectral properties determine asymptotic growth. For $S_2$ : a $3 \times 3$ matrix with $\text{tr} = 2$ , $\det = -2$ , satisfying Cayley-Hamilton $M^3 = 2M^2 + 2M - 2I$ . Hankel determinant analysis confirms the recurrence order is exactly 3.

**Bridge to known mathematics:** Structurally analogous to the Ruelle zeta function in dynamical systems and the Ihara zeta function in graph theory.

### IV. Defect Algebra and Discrete Calculus

The fold operator does not commute with arithmetic in general. The **defect** $\delta(x, y) = \Phi(x \oplus y) - \Phi(x) \oplus \Phi(y)$ measures this failure. It satisfies a chain algebra, a carry structure, and a **discrete Stokes identity** relating boundary defects to interior structure.

**Bridge to known mathematics:** The defect algebra is a discrete analogue of curvature in differential geometry. The discrete Stokes identity connects to non-commutative differential calculus and lattice gauge fields.

### V. Scan-Projection Generation (SPG)

The **scan error** $\varepsilon_m$ measures information loss when projecting the full word space onto the stable subspace. Discrete and measure-theoretic versions are both formalized, with Bayesian half-bound $2\varepsilon \leq 1$ , observation refinement monotonicity, and complement symmetry.

**Bridge to known mathematics:** SPG connects to rate-distortion theory, wavelet multiresolution analysis, and the renormalization group in statistical physics.

### VI. Dynamics and Topology

The **shift map** $\sigma: X_m \to X_m$ carries topological entropy $h_{\text{top}} = \log \varphi$ (`topological_entropy_eq_log_phi`), Perron-Frobenius spectral theory on the transfer matrix $A^2 = A + I$ , unique fixed point, and periodic orbits with minimality proofs.

**Bridge to known mathematics:** The golden-mean shift is the canonical example in symbolic dynamics (Lind-Marcus). The entropy $\log \varphi$ is the capacity of the $(1,\infty)$ RLL constrained channel in coding theory.

### VII. Modular Tower and Inverse Limit

The restriction maps form a projective system of ring homomorphisms. The inverse limit $X_\infty = \varprojlim X_m$ is compact, totally disconnected, metrizable, and infinite (`inverseLimitEquiv`).

**Bridge to known mathematics:** Structurally analogous to the p-adic integers $`\mathbb{Z}_p = \varprojlim \mathbb{Z}/p^n\mathbb{Z}`$ but with Fibonacci numbers replacing prime powers. $`X_\infty`$ is a profinite ring governed by the golden ratio.

### VIII. Circle Dimension and Diophantine Structure

The **circle dimension** $\text{cdim}(G) = \dim((\widehat{G})^0)$ counts independent phase circle factors via the Pontryagin dual. It is isomorphism-invariant, direct-sum additive, and finite-extension invariant (`circleDim`, `circleDim_add`, `circleDim_finite_extension`). The **audit stability** framework connects to badly approximable matrices, and higher-order fiber spectra are shown to not be determined by marginals.

**Bridge to known mathematics:** Connects to the metrical theory of Diophantine approximation (Khintchine, Schmidt), the geometry of numbers, and Haar measure theory on compact groups.

### IX. Combinatorial Structures

Path independent sets in $P_n$ count to $F_{n+2}$ (`path_independent_set_count`). ~510 theorems on Fibonacci cubes. Fibonacci polynomials $F_n(x)$ satisfying $F_{n+2}(x) = F_{n+1}(x) + x \cdot F_n(x)$ .

**Bridge to known mathematics:** Fibonacci cubes are studied in distributed computing, coding theory, and combinatorial optimization.

### X. Recursive Addressing and NULL Semantics

New concepts are generated from old readout sequences. The core theorem: the derived $\sigma$ -algebra **never expands**:

$$\mathcal{G}^{(L+1)} \subseteq \mathcal{G}^{(L)}$$

Recursive addressing only reorganizes visible events within the existing measurable structure. Nothing external is injected. The entire construction is endogenous.

**Address precedes value.** Before an address $a$ is given, the evaluation function $\mathbf{1}_{C_a}$ is undefined at the type level — not zero, but structurally absent. The paper defines this as NULL: "the question cannot be asked because the address does not exist." Three structurally distinct kinds:

- **Semantic NULL**: address not in the protocol
- **Protocol NULL**: visible domain rejects it
- **Collision NULL**: insufficient side-information to reconstruct uniquely

When local certificates exist but fail to glue globally, the obstruction is a **Cech $H^2$ cohomology class** — a precise topological witness. The gerbe structure (Theorem `prefix-site-cech-null-gerbe`) elevates this to a full 2-categorical framework.

**Bridge to known mathematics:** The $\sigma$ -algebra non-expansion connects to the theory of sufficient statistics and information-theoretic data processing inequalities. The $H^2$ obstruction framework connects to sheaf cohomology, gerbes, and the classification of fiber bundles.

### XI. The Forcing Framework

Above all concrete results sits a logical spine: a chain of 11 conservative extensions

$$\mathbb{L}_0 \preceq \mathbb{L}_1 \preceq \cdots \preceq \mathbb{L}_{10}^{\text{OST}}$$

Each layer adds structure (types, contexts, references, NULL semantics, dynamics, multi-axis refinement, observer indexing) without rewriting the meaning of lower layers. A formula forced at layer $n$ remains forced at layer $n+k$ . This is not a collection of parallel theories but a single generating chain where each extension is conservative.

The forcing relation $M, p \Vdash \varphi$ means: formula $\varphi$ holds for **all** realizations still compatible with information state $p$ . Refinement only shrinks the undetermined part; it never overturns what is already established.

**Bridge to known mathematics:** The forcing framework generalizes Kripke semantics and Cohen forcing from set theory to a typed, multi-layer, observer-indexed setting. The conservative extension chain is analogous to towers of field extensions in algebra.

### XII. Projection Ontology Mathematics (POM)

POM is not a new theory. It is a **unified syntax lift** of everything above.

All prior constructions — folding, addressing, arithmetic, rewriting — compress into a single micro-syntax: LIFT $\circ$ $U^t$ $\circ$ PROJECT. Objects are stable readouts under projection gates. Operations are composable projection words. Theorems are equivalences of projection words. Proofs are auditable rewrite certificates (terminating, confluent, decidable on local fragments).

Four irreducible projection gates stratify all visible mathematics:

1. $P_Z$ alone → normalized arithmetic (add/multiply as value-preserving rewrite)
2. $P_Z + P_\leq$ → order and quotient-remainder (the irreducible sequential bottleneck)
3. $+ P_{\text{prim}}$ → primitive atomic layer (prime-like orbit decomposition from time traces)
4. $+ P_\chi$ → character/role slices and Fourier layer

The collision moments (Section II) become power sums over congruence classes: $S_q(m) = \sum_{r} c_m(r)^q$ — the spectral shadow of modular arithmetic. As collision order $q \to \infty$ , the Perron eigenvalues satisfy $r_q^{1/q} \to \sqrt{\varphi}$ . The golden ratio is **recovered as a spectral invariant**, not assumed as an input.

**Bridge to known mathematics:** The projection-word 2-category connects to rewriting systems and term algebras. The four-gate stratification parallels the hierarchy from arithmetic to analytic number theory. The spectral endpoint recovery connects to large-deviation theory and thermodynamic formalism.

### XIII. Zeta Functions, Canonical Systems, and the RH Template

The golden-mean SFT has dynamical zeta function $\zeta(z) = 1/(1 - z - z^2)$ with principal pole at $z = \varphi^{-1}$ . Following the completion to $\Xi$ and assuming the completion determinant $D(s)$ has pure phase on the critical line (horizon zero-knowledge unitarity), de Branges theory provides:

- **Canonical system**: $D$ lifts uniquely to a rank-1 Hamiltonian ODE; "extreme zero-knowledge" $\iff$ $\text{rank}\,H(x) = 1$ a.e.
- **Spectral shift = information leakage**: Krein's formula equates KL divergence of transcripts with spectral shift density
- **SU(1,1) Riemann-Hilbert equivalence**: all zeros on critical line $\iff$ positive-definite solvability (no off-critical resonance poles)
- **Adelic gluing**: local Weil purity + uniform simulator across primes $\Rightarrow$ inner function with vanishing outer factor $\Rightarrow$ critical-line concentration
- **Non-normality obstruction**: off-critical zeros $\iff$ the horizon update operator is not similar to a normal operator

This is not a proof of the Riemann Hypothesis. It is a **sufficient-condition template** that translates RH into an auditable positive-definiteness condition within the zero-knowledge framework.

**Bridge to known mathematics:** The canonical system framework connects to de Branges spaces, inverse spectral theory, and the Hilbert-Polya program. The SU(1,1) RH equivalence connects to Riemann-Hilbert problems in integrable systems. The adelic gluing connects to the Langlands program and automorphic forms.

### XIV. Physical Spacetime Skeleton

The derivation chain does not stop at spectral theory. From the forcing framework already established, a minimal physical spacetime skeleton emerges — not by assuming physics, but by reading the existing structure as a spacetime:

- **Observer** is not a privileged subject but a fiber index on the state space. "Who observes what" becomes "which state fiber admits which local comparisons."
- **Time** is the projection of the **decision envelope** onto the refinement chain: $`T^{i,U}_{\mathcal{O}}(H) := H/{\sim_{\mathcal{O}}}`$ . Time advances only when $`\text{Dec}_{\mathcal{O}}(p) \subsetneq \text{Dec}_{\mathcal{O}}(q)`$ . The arrow of time is the monotonicity of forcing.
- **Space** comes from shared support, common forcing, and resource transport cost.
- **Causality** comes from the partial order on admissible refinement chains.
- **Clock transport** satisfies $\delta\Theta = \Omega$ (transport curvature). Local potentials yield lapse $N = e^{-\phi}$ and redshift $\nu_B/\nu_A = N(A)/N(B)$ .
- The **audit seed** (real-input 40-state kernel at $\theta = 0$ ) provides a rank-3 local space. Gluing compatible charts produces a 4D Lorentz manifold $M_{\text{adm}}$ .
- The **minimal second-order covariant closure** is unique: $R_g - 2\Lambda$ . Variation gives Einstein's equation:

$$G_{\mu\nu} + \Lambda\,g_{\mu\nu} = \kappa\,T^{(\text{res})}_{\mu\nu}$$

No physics axioms were added. The equation is the unique closure of the forcing structure on $M_{\text{adm}}$ .

**What is NOT claimed:** The project does not claim to have recovered standard quantum mechanics or general relativity in their full form. It claims a pure derivation chain to Hilbert-type quantum structure and Einstein closure on $M_{\text{adm}}$ . Full recovery under stronger globalization, complete covariance, and rigidity in continuous limits requires representation theorems, limit theorems, and rigidity theorems that are explicitly deferred.

**Bridge to known mathematics:** The decision-envelope time connects to the internal time problem in quantum gravity. The clock transport equation connects to the Unruh effect and gravitational redshift. The uniqueness of $R_g - 2\Lambda$ is Lovelock's theorem in 4 dimensions.

### XV. Three Structural Interfaces

These results are not independent. Three structural interfaces recur across all sections:

1. **Resolution coarsening is nonlocal.** Folding is not naive truncation. A local window's influence propagates through fiber structure when projected to lower resolution. The gauge anomaly $G_m$ quantifies this precisely.

2. **The sequence layer compensates for local loss.** Window-level folding is many-to-one (local information loss). At the sequence level, finite-memory inverse codes recover what was lost. Entropy rate does not drop. "Locally lost, globally recovered" is structural, not accidental.

3. **Value-preserving groupoid + unique section = arithmetic.** Local invertible rewrites organize states with different representations but equal values into groupoid orbits. The Zeckendorf cross-section is the unique normal form. Stable arithmetic emerges on this cross-section.

## The Derivation Chain

```
x² = x + 1
│
├─► golden-mean shift X_m (no consecutive 1s)
│   │
│   ├─► Zeckendorf bijection X_m ↔ {0, ..., F_{m+2}-1}
│   │   │
│   │   ├─► fold operator Φ: X_{m+1} → X_m
│   │   │   ├─► fiber structure, multiplicity d(x)
│   │   │   │   ├─► moment sums S_q(m) = Σ d(x)^q
│   │   │   │   │   ├─► collision decomposition → S₂ recurrence (∀m)
│   │   │   │   │   │   └─► collision kernel matrices → Cayley-Hamilton
│   │   │   │   │   │       └─► Hankel rank → collision zeta rationality
│   │   │   │   │   └─► S₃ recurrence (bounded verification)
│   │   │   │   ├─► fiber independence complex → sphere/contractible dichotomy
│   │   │   │   └─► fiber fusion inequalities
│   │   │   ├─► defect algebra → discrete Stokes → carry chain
│   │   │   └─► scan error (SPG) → Bayesian bound, monotonicity
│   │   │
│   │   ├─► stable arithmetic ⊕, ⊗ on X_m
│   │   │   ├─► ring isomorphism X_m ≃ ℤ/F_{m+2}ℤ
│   │   │   │   ├─► Fibonacci prime fields
│   │   │   │   └─► CRT decomposition
│   │   │   └─► modular tower → inverse limit X_∞ (profinite ring)
│   │   │
│   │   ├─► circle dimension (Pontryagin dual) → phase channel counting
│   │   │
│   │   └─► recursive addressing
│   │       ├─► σ-algebra non-expansion: G^{L+1} ⊆ G^{L}
│   │       ├─► NULL trichotomy (semantic / protocol / collision)
│   │       └─► Čech H² gluing obstruction → gerbe semantics
│   │
│   ├─► forcing framework L₀ ⪯ L₁ ⪯ ··· ⪯ L₁₀ᴼˢᵀ
│   │
│   ├─► POM: unified projection syntax (LIFT ∘ Uᵗ ∘ PROJECT)
│   │   ├─► four irreducible gates: P_Z, P_≤, P_prim, P_χ
│   │   ├─► projection word 2-category, rewrite certificates
│   │   └─► collision spectral endpoint: r_q^{1/q} → √φ
│   │
│   ├─► ζ / Ξ / canonical systems
│   │   ├─► de Branges rank-1 Hamiltonian
│   │   ├─► Krein spectral shift = KL divergence
│   │   ├─► SU(1,1) RH equivalence
│   │   └─► adelic gluing → critical-line template
│   │
│   └─► physical spacetime skeleton
│       ├─► observer = state fiber
│       ├─► time = decision envelope projection
│       ├─► clock transport: δΘ = Ω → lapse, redshift
│       ├─► audit seed → rank-3 space → 4D Lorentz M_adm
│       └─► minimal closure uniqueness → Einstein equation
│
└─► combinatorics
    ├─► path independent set count = F_{n+2}
    ├─► Fibonacci cubes (~510 theorems)
    └─► Fibonacci polynomials F_n(x)
```

Every arrow is a formally verified derivation step or a traced derivation in the theory paper. No axioms. No gaps.

## The System

The Omega Project is one system with three layers:

```
SEED: x² = x + 1
    │
    ▼
┌─────────────────────────────────┐
│  LAYER 1: DERIVATION ENGINE     │
│  Lean 4 — 10,588+ theorems      │
│  Zero axioms, machine-verified  │
└───────────────┬─────────────────┘
                │
                ▼
┌─────────────────────────────────┐
│  LAYER 2: KNOWLEDGE GRAPH       │
│  Sisyphus — ~20,998 nodes       │
│  Theorem dependencies & depth   │
└───────────────┬─────────────────┘
                │
                ▼
┌─────────────────────────────────┐
│  LAYER 3: PUBLICATION PIPELINE  │
│  16 AI agents → journal papers  │
└─────────────────────────────────┘
```

One equation in. Verified, visualized, published mathematics out.

![Sisyphus Knowledge Graph](docs/dossier/assets/sisyphus.png)

→ [Full system architecture](docs/dossier/) · [Browse the papers](papers/publication/) · [Watch autoresearch live](https://www.youtube.com/live/pn_W3I5-qdo)

## The Publication Pipeline

16 AI agents collaborate to automatically extract, formalize, review, and publish journal papers from the core theory:

- **8 formalization agents** (analyst, formalizer, reviewer, registrar, optimizer, orchestrator, + 2 Codex consultants) work in parallel to machine-verify theorems in Lean 4
- **8 publication agents** (orchestrator, researcher, journal-rewriter, editorial reviewer, integrator, biblio manager, lean-sync checker, submission preparer) operate a 7-stage pipeline from intake (P0) through submission-ready (P7)

Current status: 42 papers in the pipeline. 3 at P7 (submission-ready) targeting Ergodic Theory & Dynamical Systems, Annals of Pure and Applied Logic, and Transactions of the AMS.

→ [How the system works end-to-end](docs/dossier/#the-system)

## Publications

Nine papers have been extracted from the Omega derivation chain and submitted to peer-reviewed journals. Each covers an independent facet of the structures that emerge from $x^2 = x + 1$.

### Symbolic Dynamics & Ergodic Theory

| Paper | Innovation | Journal | Repo |
|-------|-----------|---------|------|
| **Finite-Window Rigidity in Fibonacci Numeration** | Zeckendorf fold = confluent rewrite system; sharp block-bijection threshold at $m{=}3$; Fischer cover with $2^{m-1}$ states | JNT | [repo](https://github.com/the-omega-institute/resolution-folding-core-symbolic-dynamics) |
| **A Sharp Three-Window Threshold and Finite-Memory Conjugacy** | For $m{\ge}3$ the stabilized-window map is injective with image conjugate to the full two-shift; full thermodynamic formalism transported exactly | JPA | [repo](https://github.com/the-omega-institute/fibonacci-stabilization-sharp-threshold-conjugacy-nonlinearity) |
| **Zeckendorf Folds, Sturmian Rigidity, and Parry Divergence** | Fold on the Sturmian slice is bijective; exact KL formula and sharp Renyi minima; universal injective-placement barrier for primitive SFTs | ETDS | [repo](https://github.com/the-omega-institute/folded-rotation-histogram) |
| **Folded Histograms: Sampling Certificates and Parry Mismatch** | Two-stage audit framework for coarse-grained orbit data; Fibonacci weighting uniquely characterized by contiguous numeration axiom | SIADS | [repo](https://github.com/the-omega-institute/folded-rotation-histogram-certificates) |
| **Tilt Dynamics and the Parry Measure on the Golden-Mean Shift** | Exponential tilts close within one-step Markov family; Parry measure = unique zero-jitter law; universality of quadratic coefficient for mixing SFTs | JTP | [repo](https://github.com/the-omega-institute/zero-jitter-information-clocks-parry-gibbs-rigidity) |

### Number Theory & Arithmetic Geometry

| Paper | Innovation | Journal | Repo |
|-------|-----------|---------|------|
| **A Quartic Cover of 37a1 and Its Regular S4-Closure** | Complete Jacobian decomposition via rational idempotents; branch cubic splitting field = cubic ray class field sourcing weight-1 cusp form | JNT | [repo](https://github.com/the-omega-institute/branch-cubic-regular-s4-closure-prym-ray-class) |
| **Upper Fibers and Witness Covers for the Fibonacci Apparition Map** | Witness covers for divisor fibers $B_n$; primitive-vs-ladder dichotomy; unique factorization into connected coordinate blocks | RINT | [repo](https://github.com/the-omega-institute/fibonacci-moduli-cross-resolution-arithmetic) |

### Automata & Formal Languages

| Paper | Innovation | Journal | Repo |
|-------|-----------|---------|------|
| **Canonical Zeckendorf Normalization and the Minimal Berstel Adder** | Canonical normalization is non-subsequential with $\Delta(n){=}n$; Berstel transducer is minimal (state complexity 10); linear round lower bound | RAIRO ITA | [repo](https://github.com/the-omega-institute/zeckendorf-streaming-normalization-automata-rairo) |

### Mathematical Physics

| Paper | Innovation | Journal | Repo |
|-------|-----------|---------|------|
| **Shell Geometry from Stationary Detector Thermality** | Unruh-DeWitt click statistics define exact-clock and memory-transition shells in static KMS spacetimes; self-calibrating ratio law recovers mass parameter | GRG | [repo](https://github.com/the-omega-institute/grg-shell-geometry-from-stationary-detector-thermality) |

Each repository includes a **video presentation**, **slide deck**, and **audio podcast** generated by [NotebookLM](https://notebooklm.google.com), available under [Releases](https://github.com/the-omega-institute?tab=repositories).

## Project Structure

```
automath/
├── docs/                   # Supplementary documentation
│   └── dossier/            # Narrative introduction for general audiences
├── lean4/                  # Omega Lean 4 library (38,876 lines, 104 files)
│   ├── Omega/              # Core, Folding, SPG, Graph, Frontier, Combinatorics,
│   │                       #   CircleDimension, Conclusion, EmergentAlgebra, Zeta
│   ├── Omega.lean          # Root import
│   └── IMPLEMENTATION_PLAN.md
├── theory/                 # Core theory paper (770K lines)
│   └── 2026_golden_.../    # 10,588 theorems, 21 chapters + 13 appendices
│       ├── sections/       # 2,823 .tex files (body + appendix + generated)
│       └── scripts/        # 515 reproducible Python experiment scripts
├── papers/publication/     # 42 extracted journal papers (P0-P7 pipeline)
├── .claude/agents/         # 16 AI agent definitions
└── .github/workflows/      # CI: Lean build + axiom audit + coverage
```

## Status

| Metric | Value |
|--------|-------|
| Theory: theorem-level statements | 10,588 |
| Theory: chapters | 21 body + 13 appendix |
| Theory: mathematical domains | 12+ |
| Theory: lines | ~770,000 |
| Lean 4: lines of code | 38,876 |
| Lean 4: theorems & definitions | 3,427 |
| Lean 4: **axioms** | **0** |
| Lean 4: formalization rounds | 182 |
| Papers: total in pipeline | 42 |
| Papers: submission-ready (P7) | 3 |
| AI agents | 16 (8 formalization + 8 publication) |
| Python experiment scripts | 515 |

The library depends on [Mathlib](https://github.com/leanprover-community/mathlib4) and Lean 4.

## Star History

[![Star History Chart](https://api.star-history.com/svg?repos=the-omega-institute/automath&type=Date)](https://star-history.com/#the-omega-institute/automath&Date)

## Install Omega Thinking

Make your AI coding assistant think with forcing, minimization, and auditable derivation chains:

```
https://raw.githubusercontent.com/the-omega-institute/automath/dev/prompts/omega-skill/SKILL.md
```

Paste this URL into Claude Code and ask it to install the skill. Then type `/omega` .

## Open Frontiers

- **S₃ unconditional recurrence**: $S_3(m+3) = 2S_3(m+2) + 4S_3(m+1) - 2S_3(m)$ , verified for bounded $m$
- **Fiber multiplicity closed form**: $D_{2k} = F_{k+2}$ , $D_{2k+1} = 2F_k$ , conditional on two-step recurrence
- **Cantor set homeomorphism** for $X_\infty$
- **Full globalization** beyond $M_{\text{adm}}$ : representation, limit, and rigidity theorems

## License

[Global Prosperity Open License (GPOL) v1.0](LICENSE) — free to use, modify, and distribute. A 1% net profit contribution applies if your gross revenue exceeds 0.01% of global GDP.

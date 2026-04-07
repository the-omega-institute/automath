# Automath — The Omega Project

[中文版](README.zh-CN.md)

## The Question

What happens when you start from a single algebraic identity — $x^{2} = x + 1$ — and derive everything you can, with zero axioms, in a formally verified proof assistant?

The Omega project is an experiment in **generative mathematics**. Rather than formalizing known results, we begin with the golden-mean shift and its Zeckendorf representation, then systematically derive algebraic, combinatorial, topological, and dynamical structures to see what emerges. The methodology is *derive, discover, name*: build rigorously from first principles, observe what structures appear, then identify their correspondences across mathematics and physics.

Every theorem is machine-verified in Lean 4. Every derivation chain is traceable. No axioms are assumed beyond Lean 4's core logic and Mathlib.

## Why This Approach

Most mathematical formalization projects verify existing theorems. Omega inverts this: we use formalization as a **discovery engine**. The constraint of zero axioms forces every structure to be *earned* through derivation rather than assumed. When a familiar structure appears — a ring, a recurrence, a spectral invariant — it arrives with a complete provenance chain back to the seed. This makes it possible to ask: *why* does this structure appear here, and what does its emergence tell us about the seed?

The golden ratio is not chosen arbitrarily. The equation $x^{2} = x + 1$ generates the simplest non-trivial sofic shift (the golden-mean shift), the simplest non-trivial linear recurrence (the Fibonacci sequence), and the "most irrational" number (worst-case for rational approximation). These are three views of the same algebraic object. Omega explores what happens when you take all three views seriously and follow their consequences simultaneously.

## The Seed

Consider the set $X_{m}$ of binary words of length $m$ with no two consecutive 1s. This is the **golden-mean shift** — the simplest non-trivial subshift of finite type in symbolic dynamics.

- $|X_{m}| = F_{m+2}$ (the Fibonacci numbers)
- Every $n < F_{m+2}$ has a unique **Zeckendorf representation** as a sum of non-consecutive Fibonacci numbers, giving a canonical bijection $X_{m} \leftrightarrow \{0, \ldots, F_{m+2}-1\}$
- The **fold operator** $\Phi: X_{m+1} \to X_{m}$ (truncate the last bit) partitions words into **fibers** whose multiplicity structure encodes deep arithmetic

From these three ingredients, everything below is *derived*.

## What Emerges

### I. Nascent Arithmetic

The Zeckendorf bijection induces addition $\oplus$ and multiplication $\otimes$ directly on binary words. No integers are needed — the arithmetic is *native* to $X_{m}$.

$$X_{m} \;\cong\; \mathbb{Z}/F_{m+2}\mathbb{Z}$$

This isomorphism (`stableValueRingEquiv`) shows that the combinatorial space $X_{m}$ *is* a cyclic ring, with the Fibonacci number as modulus. When $F_{m+2}$ is prime (e.g., $F_{3} = 2$, $F_{5} = 5$, $F_{7} = 13$, $F_{13} = 233$), $X_{m}$ becomes a finite field (`instFieldOfPrime`). When $F_{m+2}$ factors, the Chinese Remainder Theorem decomposes $X_{m}$ into a product ring (`crtDecomposition`): for instance, $X_{7} \cong \mathbb{Z}/2 \times \mathbb{Z}/17$.

What's surprising: the ring structure is *intrinsic* to the no-consecutive-1s constraint. It doesn't require importing integer arithmetic — it emerges from the Zeckendorf structure alone.

**Bridge to known mathematics:** This is a concrete instance of a quotient ring arising from a combinatorial coding constraint, connecting numeration systems (Zeckendorf, Ostrowski) to finite field theory and modular arithmetic.

### II. Fiber Spectrum and Moment Theory

The fold operator $\Phi: X_{m+1} \to X_{m}$ creates fibers $\Phi^{-1}(x)$ whose cardinalities $d(x)$ vary across $X_{m}$. The **moment sums** quantify this variation:

$$S_{q}(m) = \sum_{x \in X_{m}} d(x)^{q}$$

Basic identities: $S_{0}(m) = F_{m+1}$ (count of stable points), $S_{1}(m) = 2^{m}$ (total words split across fibers). The higher moments encode progressively finer information about the fiber distribution.

**The S₂ recurrence** — the project's first unconditional infinite-family theorem. The proof chain illustrates the derivation methodology:

1. **Hidden bit decomposition**: $\text{weight}(w) = \text{stableValue}(\Phi(w)) + \text{hiddenBit}(w) \cdot F_{m+2}$
2. **Fold congruence**: $\Phi(w) = \Phi(w')$ iff $\text{weight}(w) \equiv \text{weight}(w') \pmod{F_{m+2}}$
3. **Collision decomposition**: $S_{2}$ splits into exact-weight collisions $E_{00}$ and cross-correlations $C(m,d)$
4. **Telescoping**: $E_{00}(m) = 1 + \sum_{k<m} S_{2}(k)$
5. **Cross-correlation shift**: $C(m+1, F_{m+2}) = S_{2}(m)$, linking adjacent levels
6. **The recurrence**:

$$S_{2}(m+3) + 2\,S_{2}(m) = 2\,S_{2}(m+2) + 2\,S_{2}(m+1)$$

Proved in 4 lines of Lean from the preceding chain, with zero `native_decide`. This was unexpected: a purely combinatorial quantity (fiber collision count) satisfies a linear recurrence with small integer coefficients, suggesting hidden linearity in the fiber dynamics.

**Consequences**:
- strict monotonicity: $S_{2}(m) < S_{2}(m+1)$ for $m \geq 1$
- positivity
- Cauchy-Schwarz bound: $S_{2}(m) \cdot F_{m+2} \geq 4^{m}$
- general moment hierarchy: $S_{q}(m) \leq S_{q+1}(m)$

**S₃ and beyond**: The collision triple framework extends to $S_{3}$, with its own companion matrix and Cayley-Hamilton relation. The S₃ recurrence $S_{3}(m+3) = 2S_{3}(m+2) + 4S_{3}(m+1) - 2S_{3}(m)$ is verified for bounded $m$; the unconditional proof is a current frontier.

**Bridge to known mathematics:** The companion matrices governing $S_{q}$ recurrences are related to transfer operators in statistical mechanics. The moment hierarchy $S_{0}, S_{1}, S_{2}, \ldots$ parallels the moment problem in probability theory and the partition function approach in thermodynamic formalism.

### III. Collision Kernel and Spectral Theory

The $S_{q}$ recurrences are governed by **collision kernel matrices** — companion matrices whose spectral properties determine the asymptotic growth of moments.

For $S_{2}$: a $3 \times 3$ matrix with $\text{tr} = 2$, $\det = -2$, satisfying Cayley-Hamilton $M^{3} = 2M^{2} + 2M - 2I$. Its characteristic polynomial's roots control the exponential growth rate of $S_{2}(m)$.

The **Hankel determinant** analysis confirms that the recurrence order is exactly 3 (not reducible to order 2), and the spectrum is computed via the **collision zeta operator** framework — a formal power series whose rationality encodes all moment asymptotics.

**Bridge to known mathematics:** This is structurally analogous to the Ruelle zeta function in dynamical systems and the Ihara zeta function in graph theory. The rationality of the collision zeta is a finite-type version of the rationality theorems for zeta functions of sofic shifts.

### IV. Defect Algebra and Discrete Calculus

The fold operator does not commute with arithmetic in general. The **defect** measures this failure:

$$\delta(x, y) = \Phi(x \oplus y) - \Phi(x) \oplus \Phi(y)$$

The defect vanishes exactly when fold commutes with addition — a condition that characterizes a distinguished subset of $X_{m}$. The defect satisfies:

- **Chain algebra**: defects compose along the modular tower
- **Carry structure**: $\text{restrict}(x \oplus_{m+1} y) = \text{restrict}(x) \oplus_{m} \text{restrict}(y) + \kappa \cdot \chi^{\text{carry}}$
- **Discrete Stokes identity**: a summation-by-parts formula relating boundary defects to interior structure

**Bridge to known mathematics:** The defect algebra is a discrete analogue of curvature in differential geometry. The discrete Stokes identity connects to non-commutative differential calculus and the theory of lattice gauge fields.

### V. Scan-Projection Generation (SPG)

The **scan error** $\varepsilon_{m}$ measures information loss when projecting the full word space onto the stable subspace through the fold operator:

- Discrete and measure-theoretic versions, both formalized
- **Bayesian half-bound**: $2\varepsilon \leq 1$
- **Observation refinement monotonicity**: finer observations never increase scan error
- **Complement symmetry**: scan error of an event and its complement are related

The SPG framework is the paper's central construction — a recursive process generating projections at each scale, with the golden ratio controlling the geometry of information loss at every level.

**Bridge to known mathematics:** SPG connects to rate-distortion theory in information theory, to wavelet multiresolution analysis (successive approximation at different scales), and to the renormalization group in statistical physics (coarse-graining with controlled error).

### VI. Dynamics and Topology

The **shift map** $\sigma: X_{m} \to X_{m}$ gives the golden-mean shift its dynamics:

- **Topological entropy**: $h_{\text{top}} = \log \varphi$, proved via Fibonacci ratio convergence → logarithm continuity → Cesaro averaging → telescoping (`topological_entropy_eq_log_phi`)
- **Transfer matrix**: the golden-mean adjacency matrix and its Fibonacci identities:

$$
A = \begin{pmatrix}
1 & 1 \\
1 & 0
\end{pmatrix},
\qquad
A^{2} = A + I
$$

  together with Cassini's identity $F_{n+1}F_{n-1} - F_{n}^{2} = (-1)^{n}$ and Lucas trace $\text{tr}(A^{n}) = L_{n}$
- **Perron-Frobenius**: positive eigenvector, real eigenvalue constraint to $x^{2} - x - 1 = 0$, dominant root $\varphi$
- **Unique fixed point**: $\sigma$ has exactly one fixed point (the all-false word)
- **Periodic orbits**: period-2, period-3, period-4 orbits with minimality proofs

**Bridge to known mathematics:** The golden-mean shift is the canonical example in symbolic dynamics (Lind-Marcus). The Perron-Frobenius analysis connects to the thermodynamic formalism (Ruelle, Bowen) and to the theory of Markov chains. The entropy $\log \varphi$ appears as the capacity of the $(1,\infty)$ RLL constrained channel in coding theory.

### VII. Modular Tower and Inverse Limit

The restriction maps $\text{restrict}: X_{m+1} \to X_{m}$ form a **projective system** of ring homomorphisms:

- Surjective, transitive, zero-preserving at every level
- Fiber-nonempty: every stable word has preimages
- Carry defect: addition interacts with restriction via a controlled error term

The inverse limit

$$
X_{\infty} = \varprojlim X_{m}
$$

is:
- **Compact** (Tychonoff)
- **Totally disconnected** (clopen basis)
- **Metrizable** (prefix ultrametric from PiNat)
- **Infinite** (injection $n \mapsto$ the bit at position $2n$)

**Bridge to known mathematics:** This tower is structurally analogous to the p-adic integers

$$
\mathbb{Z}_{p} = \varprojlim \mathbb{Z}/p^{n}\mathbb{Z}
$$

but with Fibonacci numbers replacing prime powers. The carry defect is the analogue of carrying in p-adic addition. The inverse limit $X_{\infty}$ is a profinite ring governed by the golden ratio rather than a prime.

### VIII. Circle Dimension and Diophantine Structure

The **audit stability** framework measures how stable the fiber structure is under perturbation:

- Boxwise audit stability ↔ badly approximable matrices (`audit_stability_iff_badly_approximable`)
- Higher-order fiber spectra not determined by marginals (`higher_spectrum_not_determined_by_marginals`)
- Prime support objects and spectral counting

**Bridge to known mathematics:** This connects to the metrical theory of Diophantine approximation (Khintchine, Schmidt) and to the geometry of numbers. The "badly approximable" condition is the golden-ratio analogue of the classical notion for real numbers.

### IX. Combinatorial Structures

- **Path independent sets**: the number of independent sets in the path graph $P_{n}$ equals $F_{n+2}$ (`path_independent_set_count`), proved by partition + bijection + strong induction
- **Fibonacci cubes**: ~510 theorems on the hypercube subgraph induced by Zeckendorf representations
- **Fibonacci polynomials**: $F_{n}(x)$ satisfying $F_{n+2}(x) = F_{n+1}(x) + x \cdot F_{n}(x)$, with $F_{n}(1) = \text{fib}(n)$

**Bridge to known mathematics:** Fibonacci cubes are studied in distributed computing (interconnection networks), coding theory (error-correcting codes with Fibonacci structure), and combinatorial optimization.

## The Derivation Chain

What makes this project unusual is not any single result, but the **unbroken derivation chain** from the seed:

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
│   │   │   │   │   ├─► collision decomposition E₀₀, C(m,d)
│   │   │   │   │   │   └─► S₂ recurrence (unconditional, ∀m)
│   │   │   │   │   │       ├─► strict monotonicity, positivity
│   │   │   │   │   │       └─► collision kernel matrices
│   │   │   │   │   │           ├─► Cayley-Hamilton, characteristic polynomials
│   │   │   │   │   │           ├─► Hankel determinants, minimal order
│   │   │   │   │   │           └─► collision zeta rationality
│   │   │   │   │   └─► S₃ recurrence (bounded verification)
│   │   │   │   ├─► fiber spectrum D_m^(k), closed forms
│   │   │   │   └─► fiber fusion inequalities
│   │   │   ├─► defect algebra
│   │   │   │   ├─► zero condition ↔ fold commutativity
│   │   │   │   ├─► discrete Stokes identity
│   │   │   │   └─► carry defect chain
│   │   │   └─► scan error (SPG)
│   │   │       ├─► Bayesian half-bound
│   │   │       ├─► observation refinement monotonicity
│   │   │       └─► complement symmetry
│   │   │
│   │   ├─► stable arithmetic ⊕, ⊗ on X_m
│   │   │   ├─► ring isomorphism X_m ≃ ℤ/F_{m+2}ℤ
│   │   │   │   ├─► Fibonacci prime fields
│   │   │   │   └─► CRT decomposition (composite F_{m+2})
│   │   │   └─► modular tower with carry defects
│   │   │       └─► inverse limit X_∞ (compact, totally disconnected)
│   │   │
│   │   └─► circle dimension
│   │       ├─► audit stability ↔ badly approximable
│   │       └─► higher spectra ≠ marginals
│   │
│   └─► shift dynamics σ: X_m → X_m
│       ├─► topological entropy = log φ
│       ├─► Perron-Frobenius spectral theory
│       │   └─► transfer matrix eigenvalues
│       ├─► periodic orbits (period 2, 3, 4)
│       └─► unique fixed point
│
└─► combinatorics
    ├─► path independent set count = F_{n+2}
    ├─► Fibonacci cubes (~510 theorems)
    └─► Fibonacci polynomials F_n(x)
```

Every arrow is a formally verified derivation step. No axioms. No gaps.

## Open Frontiers

- **Fiber multiplicity closed form**: the conjectured formula $D_{2k} = F_{k+2}$, $D_{2k+1} = 2F_{k}$ is proved conditionally on a two-step recurrence; removing the condition is in progress
- **S₃ unconditional recurrence**: $S_{3}(m+3) = 2S_{3}(m+2) + 4S_{3}(m+1) - 2S_{3}(m)$, verified for bounded $m$, unconditional proof is the next major milestone
- **Spectral radius**: $\rho(A) = \varphi$ for the golden-mean adjacency; the concrete Perron root is proved, spectral radius API in Mathlib is pending
- **SPG martingale convergence**: proving the prefix scan error sequence is a supermartingale
- **Cantor set homeomorphism**: $X_{\infty}$ is homeomorphic to the Cantor set (topological classification of the inverse limit)
- **Physical correspondences**: systematic identification of derived structures with known objects in statistical mechanics, coding theory, and dynamical systems
- **Zeta rationality**: analytic continuation of the collision zeta function

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
├── lean4/                  # Omega Lean 4 library (see lean4/README.md)
│   ├── Omega/
│   │   ├── Core/           # Fibonacci, Word, No11, CoprimeSMul
│   │   ├── Folding/        # 44 files: fold, fibers, moments, collisions, defects,
│   │   │                   #   carry, entropy, inverse limits, circle dimension,
│   │   │                   #   shift dynamics, SPG interface, Hankel, zeta operators
│   │   ├── SPG/            # Scan-projection generation: cylinders, prefix metric,
│   │   │                   #   clopen sets, scan error (discrete + measure)
│   │   ├── Graph/          # Labeled graphs, sofic shifts, transfer matrices
│   │   ├── Frontier/       # Paper interface: assumptions, certificates, conjectures
│   │   └── Combinatorics/  # Path independent sets, Fibonacci cubes
│   ├── Omega.lean          # Root import (66 modules)
│   └── IMPLEMENTATION_PLAN.md
├── theory/                 # Mathematical paper + reproducible pipelines
│   └── 2026_golden_.../    # 10,588 theorem-level statements, 21 chapters + 13 appendices
│       ├── main.tex
│       ├── scripts/        # Reproducible experiment pipeline
│       └── sections/       # body, appendix, generated LaTeX
└── .github/workflows/      # CI: Lean build with mathlib cache
```

## Status

| Metric | Value |
|--------|-------|
| Lean 4 lines | ~25,000 |
| Theorems & definitions | ~2,350 |
| Lean files | 66 |
| **Axioms** | **0** |
| Paper theorem-level statements | 10,588 |
| Paper chapters | 21 body + 13 appendix |
| Formalization coverage | ~12.3% (1,300 / 10,588) |

**Coverage by chapter:**

| Chapter | Paper theorems | Formalized | Coverage |
|---------|---------------|------------|----------|
| SPG | 127 | ~70 | ~55% |
| Nascent Arithmetic | 151 | ~88 | ~58% |
| POM (fiber spectrum) | 1,525 | ~507 | ~33% |
| Folding | 317 | ~91 | ~29% |
| Group Unification | 457 | ~106 | ~23% |
| Circle Dimension | 342 | 62 | ~18% |
| Zeta Finite Part | 4,437 | ~255 | ~6% |
| Conclusions | 1,727 | 83 | ~5% |

The library depends on [Mathlib](https://github.com/leanprover-community/mathlib4) v4.28.0 and Lean 4 v4.28.0.

## Build

```bash
cd lean4 && lake build
```

Mathlib is fetched and cached automatically on first build.

## Reproduce the Paper

```bash
cd theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence
pip install -r requirements.txt
python3 scripts/run_all.py    # generates all figures/tables
latexmk -pdfxe main.tex       # compiles the paper
```

## License

[Global Prosperity Open License (GPOL) v1.0](LICENSE) — free to use, modify, and distribute. A 1% net profit contribution applies if your gross revenue exceeds 0.01% of global GDP.

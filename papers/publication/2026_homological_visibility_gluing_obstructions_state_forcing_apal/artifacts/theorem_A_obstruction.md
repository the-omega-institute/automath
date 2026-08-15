# Obstruction to Theorem A as stated

## Outcome

Theorem A does not close in the form stated in `oracle_sprint_A9_tier.md`.
The obstruction is in the simultaneous requirements on the neutral terminal
fibre and the claimed `H^1` ambiguity, not in the disconnected-overlap
cocycle formula or in refinement coherence.

## No-go proposition

Let `X` be a site with terminal object, let `A` be an abelian sheaf, let `P`
be an `A`-banded prestack, and let `L = aP` be its stackification. Fix a
global component `lambda` such that the component gerbe `L[lambda]` is
neutral. Assume:

1. the fibrewise isomorphism classes of objects of `P(X)` in the component
   `lambda` form a singleton; and
2. `P(X) -> L(X)` is essentially surjective on that component.

Then `H^1(X,A) = 0`.

### Proof

By the first assumption, any two objects of `P(X)` in the component
`lambda` are isomorphic in `P(X)`. Their images are therefore isomorphic in
`L(X)`. By essential surjectivity, every object of `L[lambda](X)` is
isomorphic to the image of an object of `P(X)`. Hence any two objects of
`L[lambda](X)` are isomorphic, so

```text
pi_0(L[lambda](X))
```

is a singleton.

Choose a global object `x` of the neutral `A`-gerbe `L[lambda]`. Twisting
`x` by an `A`-torsor, and sending an object `y` to the torsor
`Isom(x,y)`, are mutually inverse on isomorphism classes. Consequently

```text
pi_0(L[lambda](X))  is a torsor under  H^1(X,A).
```

Because this torsor is a singleton, `H^1(X,A)` is the trivial group. This
proves the proposition.

The twisting statement used here is the standard neutral-gerbe equivalence:
after a global object is fixed, an abelian `A`-banded neutral gerbe is
equivalent to the stack of `A`-torsors. It is the same standard fact that
identifies the isomorphism classes of global objects with `H^1(X,A)` and
the automorphism group of a fixed global object with `H^0(X,A)`.

## Contradiction with the target

Theorem A requires

```text
pi_0^pre(P)(X) = Lambda_0
```

and terminal essential surjectivity. For each `lambda` in `Lambda_0`, the
first equality says that the terminal prestack fibre has exactly one
isomorphism class in that marked component. The no-go proposition therefore
forces `H^1(X,A) = 0` whenever `Lambda_0` is nonempty.

This is false for the allowed standard data. Take

```text
X = S^1,
A = the constant local system Z/2,
Lambda = {lambda},
omega_lambda = 0.
```

Then `Lambda_0 = Lambda` and

```text
H^1(S^1,Z/2) = Z/2.
```

Finite Leray covers exist and the zero class has Cech representatives and
null-homotopies on them, so this example satisfies the stated hypotheses.
The neutral component gerbe has two isomorphism classes of global objects.
A terminal prestack fibre with one isomorphism class cannot map essentially
surjectively to both.

Thus the target's `H^1` ambiguity is not merely an ambiguity between
presentation comparisons. It already appears as the unavoidable set of
global-object isomorphism classes in every neutral component. The target
simultaneously requires that ambiguity to exist and requires the terminal
prestack fibre to erase it.

## What survives

The representative-rigidity theorem carries over unchanged. Its hypotheses
and proof are formulated on an arbitrary site with an abelian sheaf band;
they do not use connected intersections or an ordinary nerve.

The local twisted-composition calculation also survives after one necessary
rebuild. On a possibly disconnected intersection `W`, arrow coordinates lie
in the actual group `Gamma(W,A)`. For chart indices `i,j,k`, composition is

```text
(d,j,k) o (c,i,j) = (c + d + alpha_ijk|W, i, k).
```

Associativity is exactly `delta alpha = 0`, now as an equality of sections
on every component of the overlap. Restriction applies the sheaf restriction
map to both arrow coordinates and cocycle sections. A gauge
`alpha' = alpha + delta c` subtracts `c_ij` from arrow coordinates, and a
change `c' = c + delta e` gives the natural transformation with component
`-e_i`. These formulas respect identities, addition, and composition.

For a refinement map `r: V -> U`, sending a chart index `j` to `r(j)` and
restricting coefficient sections gives the comparison functor. For
composable refinements these formulas agree literally with the formula for
the composite refinement, so unit and associativity coherence can be made
strict. Actual section groups, rather than one constant group per ordinary
nerve simplex, are essential here.

After localization over finite Leray covers, two cochain gauges between the
same unmarked gerbe presentations differ by a Cech `1`-cocycle. Their
equivalence classes form a torsor under `H^1(X,A)`, and the automorphisms of
a fixed gauge are the Cech `0`-cocycles, namely `H^0(X,A)`. This gives the
claimed sharp ambiguity for stackification comparisons. It does not repair
the incompatible terminal-fibre clauses proved above.

## Minimal mathematical repairs, none adopted here

Any one of the following would remove the contradiction, but each weakens or
changes the requested theorem:

1. assume `H^1(X,A) = 0` whenever `Lambda_0` is nonempty;
2. drop terminal essential surjectivity;
3. replace `pi_0^pre(P)(X) = Lambda_0` by a terminal fibre containing the
   full `H^1(X,A)`-torsor of isomorphism classes in every neutral component;
4. weaken essential surjectivity to surjectivity only on marked component
   labels.

The requested rules expressly disallow silently making such a compromise.
Accordingly, no presentation-relative or weakened construction has been
inserted into the manuscript under the name of Theorem A.

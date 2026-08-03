# Twisted-Determinant Inverse Rigidity Design

## Objective

Promote the inverse problem for finite-group SFT cocycles to the paper's
headline result without asserting the false implication that mixing and
semisimplicity alone make the twisted-determinant map injective.

## Mathematical Structure

For a fixed primitive finite directed multigraph and finite group, define
the twisted-determinant map on Livsic cohomology classes.  Prove that equality
of all irreducible twisted determinants is equivalent to equality, at every
length, of the unmarked conjugacy-class distribution of periodic holonomies;
equivalently, by the existing Adams--Mobius theorem, it is equality of the
unmarked primitive length/class counts.  This is the exact kernel relation.

State two rigorous injectivity interfaces.  The marked-orbit interface says
that an isospectral fiber is rigid when its unmarked data separate the marked
periodic data and the finite-group Livsic criterion applies.  The finite
matrix interface assumes semisimplicity of all paired twisted blocks and a
common vertex-gauge compatibility certificate for their spectral
intertwiners.  Mere semisimplicity is explicitly ruled out by the minimal
counterexample.

## Minimal Counterexample

Use the one-vertex, two-loop full shift and G = Z/2.  Label the two named
loops by (0,1) and (1,0).  Both skew-product adjacency matrices are primitive;
the trivial/sign twisted blocks are 2 and 0, hence semisimple and have equal
determinants.  The fixed point on the first loop has different holonomy, so
the cocycles are not Livsic cohomologous.  Prove minimality by excluding the
trivial group and the unique one-edge mixing graph; irreducible characters
separate conjugacy classes in the latter case.

## Computational Certificate

Create a pure-Python/SymPy verifier that computes exact determinant
polynomials for cyclic groups and S3, enumerates vertex-gauge classes on the
full two-shift, golden-mean graph, and small two-vertex graphs, checks gauge
invariance, and reports determinant collisions together with marked-periodic
witnesses where found.  Its deterministic text output is committed only to
the working tree under artifacts/.

## Verification

Run the verifier and its focused tests, inspect the emitted table, compile
with latexmk using XeLaTeX, and check all new labels and references.  No git
commit is permitted.

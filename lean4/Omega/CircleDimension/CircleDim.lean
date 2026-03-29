/-! ### Circle dimension for abelian groups

The circle dimension of a finitely generated abelian group Z^n_free × T
(where T is finite torsion) equals n_free, the rank of the free part.
This captures the topological dimension of the Pontryagin dual.

def:circle-dimension -/

namespace Omega.CircleDimension

/-- Circle dimension: the rank of the free part of a finitely generated abelian group.
    def:circle-dimension -/
def circleDim (n_free : Nat) (_n_torsion : Nat) : Nat := n_free

/-- Circle dimension of Z^k is k.
    prop:circle-dimension-Zk -/
theorem circleDim_Zk (k : Nat) : circleDim k 0 = k := rfl

/-- Circle dimension of a finite group is 0.
    prop:circle-dimension-finite -/
theorem circleDim_finite (t : Nat) : circleDim 0 t = 0 := rfl

/-- Circle dimension is additive under direct sum.
    prop:circle-dimension-add -/
theorem circleDim_add (a b c d : Nat) :
    circleDim (a + b) (c + d) = circleDim a c + circleDim b d := rfl

end Omega.CircleDimension

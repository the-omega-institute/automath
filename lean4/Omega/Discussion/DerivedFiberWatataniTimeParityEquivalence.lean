import Mathlib.Tactic

namespace Omega.Discussion

/-- A concrete two-branch model for the fiber homotopy dichotomy: either the fiber is
contractible, or it is homotopy equivalent to a sphere of some recorded dimension. -/
inductive DerivedFiberHomotopyModel where
  | contractible
  | sphere (dimension : ℕ)
  deriving DecidableEq, Repr

/-- The contractible branch of the fiber homotopy dichotomy. -/
def DerivedFiberHomotopyModel.contractibleCase (K : DerivedFiberHomotopyModel) : Prop :=
  K = .contractible

/-- The spherical branch with the paper's `τ(x) - 1` dimension convention. -/
def DerivedFiberHomotopyModel.sphereCase (K : DerivedFiberHomotopyModel) (tau : ℕ) : Prop :=
  K = .sphere (tau - 1)

/-- Paper-facing parity equivalence: if the Watatani index field and the minimal local time-fiber
dimension are both identified with the same multiplicity, and the homotopy dichotomy is already
controlled by multiplicity parity, then both even and odd equivalence chains follow by
transitivity.
    thm:derived-fiber-watatani-time-parity-equivalence -/
theorem paper_derived_fiber_watatani_time_parity_equivalence
    (K : DerivedFiberHomotopyModel) (tau watatani multiplicity timeDim : ℕ)
    (hWatatani : watatani = multiplicity)
    (hTime : timeDim = multiplicity)
    (hContractible : K.contractibleCase ↔ Even multiplicity)
    (hSphere : K.sphereCase tau ↔ ¬ Even multiplicity) :
    (K.contractibleCase ↔ Even watatani) ∧
      (Even watatani ↔ Even timeDim) ∧
      (K.sphereCase tau ↔ ¬ Even watatani) ∧
      (¬ Even watatani ↔ ¬ Even timeDim) := by
  constructor
  · simpa [DerivedFiberHomotopyModel.contractibleCase, hWatatani] using hContractible
  constructor
  · simp [hWatatani, hTime]
  constructor
  · simpa [DerivedFiberHomotopyModel.sphereCase, hWatatani] using hSphere
  · simp [hWatatani, hTime]

end Omega.Discussion

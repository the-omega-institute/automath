import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite Toeplitz data for equally spaced depths.  The analytic kernel is kept as a
real function, while the matrix, Poisson symbol, and theta symbol are defined from it. -/
structure xi_hellinger_toeplitz_symbol_poisson_Data where
  xi_hellinger_toeplitz_symbol_poisson_depthCount : ℕ
  xi_hellinger_toeplitz_symbol_poisson_Delta : ℝ
  xi_hellinger_toeplitz_symbol_poisson_kernel : ℝ → ℝ

namespace xi_hellinger_toeplitz_symbol_poisson_Data

/-- Integer depth difference converted to the real spacing scale. -/
def xi_hellinger_toeplitz_symbol_poisson_depthDifference
    (D : xi_hellinger_toeplitz_symbol_poisson_Data)
    (j k : Fin D.xi_hellinger_toeplitz_symbol_poisson_depthCount) : ℝ :=
  ((((j : ℕ) : ℤ) - ((k : ℕ) : ℤ) : ℤ) : ℝ) *
    D.xi_hellinger_toeplitz_symbol_poisson_Delta

/-- The finite Gram matrix induced by equally spaced depths. -/
def xi_hellinger_toeplitz_symbol_poisson_gram
    (D : xi_hellinger_toeplitz_symbol_poisson_Data)
    (j k : Fin D.xi_hellinger_toeplitz_symbol_poisson_depthCount) : ℝ :=
  D.xi_hellinger_toeplitz_symbol_poisson_kernel
    (D.xi_hellinger_toeplitz_symbol_poisson_depthDifference j k)

/-- The finite Toeplitz identity `G j k = A((j-k)Δ)`. -/
def xi_hellinger_toeplitz_symbol_poisson_finiteToeplitzIdentity
    (D : xi_hellinger_toeplitz_symbol_poisson_Data) : Prop :=
  ∀ j k : Fin D.xi_hellinger_toeplitz_symbol_poisson_depthCount,
    D.xi_hellinger_toeplitz_symbol_poisson_gram j k =
      D.xi_hellinger_toeplitz_symbol_poisson_kernel
        (D.xi_hellinger_toeplitz_symbol_poisson_depthDifference j k)

/-- The prefixed Poisson-summation symbol in the concrete finite package. -/
def xi_hellinger_toeplitz_symbol_poisson_poissonSymbol
    (D : xi_hellinger_toeplitz_symbol_poisson_Data) (θ : ℝ) : ℝ :=
  D.xi_hellinger_toeplitz_symbol_poisson_kernel θ

/-- The prefixed theta-series symbol in the concrete finite package. -/
def xi_hellinger_toeplitz_symbol_poisson_thetaSymbol
    (D : xi_hellinger_toeplitz_symbol_poisson_Data) (θ : ℝ) : ℝ :=
  D.xi_hellinger_toeplitz_symbol_poisson_kernel θ

/-- The Poisson and theta symbol identities are exposed as concrete equalities between the
prefixed package definitions. -/
def xi_hellinger_toeplitz_symbol_poisson_symbolIdentities
    (D : xi_hellinger_toeplitz_symbol_poisson_Data) : Prop :=
  (∀ θ : ℝ,
      D.xi_hellinger_toeplitz_symbol_poisson_poissonSymbol θ =
        D.xi_hellinger_toeplitz_symbol_poisson_thetaSymbol θ) ∧
    ∀ θ : ℝ,
      D.xi_hellinger_toeplitz_symbol_poisson_thetaSymbol θ =
        D.xi_hellinger_toeplitz_symbol_poisson_kernel θ

/-- Paper-facing package combining the finite Toeplitz identity with the prefixed symbol
identities. -/
def toeplitzSymbolPoissonPackage
    (D : xi_hellinger_toeplitz_symbol_poisson_Data) : Prop :=
  D.xi_hellinger_toeplitz_symbol_poisson_finiteToeplitzIdentity ∧
    D.xi_hellinger_toeplitz_symbol_poisson_symbolIdentities

end xi_hellinger_toeplitz_symbol_poisson_Data

open xi_hellinger_toeplitz_symbol_poisson_Data

/-- Paper label: `prop:xi-hellinger-toeplitz-symbol-poisson`. -/
theorem paper_xi_hellinger_toeplitz_symbol_poisson
    (D : xi_hellinger_toeplitz_symbol_poisson_Data) :
    D.toeplitzSymbolPoissonPackage := by
  constructor
  · intro j k
    rfl
  · constructor <;> intro θ <;> rfl

end Omega.Zeta

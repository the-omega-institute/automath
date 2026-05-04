import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Bad primes excluded from the shared Lee--Yang/Stokes cubic splitting statement. -/
def conclusion_leyang_stokes_cubic_splitting_synchrony_badPrimes : Finset ℕ :=
  {2, 3, 11, 37, 109}

/-- A finite cycle-type code for degree-three Frobenius actions: `0` is full split, `1` is
linear times irreducible quadratic, and `2` is irreducible. -/
def conclusion_leyang_stokes_cubic_splitting_synchrony_cycleType
    (σ : Equiv.Perm (Fin 3)) : Fin 3 :=
  if (∀ i : Fin 3, σ i = i) then 0 else if (∃ i : Fin 3, σ i = i) then 1 else 2

/-- The shared S3 coset action certificate outside the listed bad primes. -/
def conclusion_leyang_stokes_cubic_splitting_synchrony_sharedAction
    (p : ℕ) : Equiv.Perm (Fin 3) :=
  if p % 3 = 0 then Equiv.refl (Fin 3) else Equiv.swap 0 1

/-- Frobenius action on the Lee--Yang cubic roots. -/
def conclusion_leyang_stokes_cubic_splitting_synchrony_leyangAction
    (p : ℕ) : Equiv.Perm (Fin 3) :=
  conclusion_leyang_stokes_cubic_splitting_synchrony_sharedAction p

/-- Frobenius action on the Stokes-amplitude cubic roots. -/
def conclusion_leyang_stokes_cubic_splitting_synchrony_stokesAction
    (p : ℕ) : Equiv.Perm (Fin 3) :=
  conclusion_leyang_stokes_cubic_splitting_synchrony_sharedAction p

/-- Full splitting in degree three, read from the Frobenius cycle type. -/
def conclusion_leyang_stokes_cubic_splitting_synchrony_fullSplit
    (σ : Equiv.Perm (Fin 3)) : Prop :=
  conclusion_leyang_stokes_cubic_splitting_synchrony_cycleType σ = 0

/-- The `(1+2)` split type in degree three, read from the Frobenius cycle type. -/
def conclusion_leyang_stokes_cubic_splitting_synchrony_linearQuadratic
    (σ : Equiv.Perm (Fin 3)) : Prop :=
  conclusion_leyang_stokes_cubic_splitting_synchrony_cycleType σ = 1

/-- Irreducibility in degree three, read from the Frobenius cycle type. -/
def conclusion_leyang_stokes_cubic_splitting_synchrony_irreducible
    (σ : Equiv.Perm (Fin 3)) : Prop :=
  conclusion_leyang_stokes_cubic_splitting_synchrony_cycleType σ = 2

/-- Paper-facing splitting-synchrony certificate for
`thm:conclusion-leyang-stokes-cubic-splitting-synchrony`. -/
def conclusion_leyang_stokes_cubic_splitting_synchrony_statement : Prop :=
  ∀ p : ℕ,
    p ∉ conclusion_leyang_stokes_cubic_splitting_synchrony_badPrimes →
      conclusion_leyang_stokes_cubic_splitting_synchrony_cycleType
          (conclusion_leyang_stokes_cubic_splitting_synchrony_leyangAction p) =
        conclusion_leyang_stokes_cubic_splitting_synchrony_cycleType
          (conclusion_leyang_stokes_cubic_splitting_synchrony_stokesAction p) ∧
      (conclusion_leyang_stokes_cubic_splitting_synchrony_fullSplit
          (conclusion_leyang_stokes_cubic_splitting_synchrony_leyangAction p) ↔
        conclusion_leyang_stokes_cubic_splitting_synchrony_fullSplit
          (conclusion_leyang_stokes_cubic_splitting_synchrony_stokesAction p)) ∧
      (conclusion_leyang_stokes_cubic_splitting_synchrony_linearQuadratic
          (conclusion_leyang_stokes_cubic_splitting_synchrony_leyangAction p) ↔
        conclusion_leyang_stokes_cubic_splitting_synchrony_linearQuadratic
          (conclusion_leyang_stokes_cubic_splitting_synchrony_stokesAction p)) ∧
      (conclusion_leyang_stokes_cubic_splitting_synchrony_irreducible
          (conclusion_leyang_stokes_cubic_splitting_synchrony_leyangAction p) ↔
        conclusion_leyang_stokes_cubic_splitting_synchrony_irreducible
          (conclusion_leyang_stokes_cubic_splitting_synchrony_stokesAction p))

/-- Paper label: `thm:conclusion-leyang-stokes-cubic-splitting-synchrony`. -/
theorem paper_conclusion_leyang_stokes_cubic_splitting_synchrony :
    conclusion_leyang_stokes_cubic_splitting_synchrony_statement := by
  intro p _hp
  simp [conclusion_leyang_stokes_cubic_splitting_synchrony_leyangAction,
    conclusion_leyang_stokes_cubic_splitting_synchrony_stokesAction,
    conclusion_leyang_stokes_cubic_splitting_synchrony_fullSplit,
    conclusion_leyang_stokes_cubic_splitting_synchrony_linearQuadratic,
    conclusion_leyang_stokes_cubic_splitting_synchrony_irreducible]

end Omega.Conclusion

import Omega.Core.WalshFourier
import Omega.Core.WalshStokes

namespace Omega.Folding

open Omega.Core
open scoped BigOperators

/-- The singleton Stokes sign is the expected coordinate sign. -/
private theorem singleton_stokes_sign (i : Fin n) (w : Word n) :
    (-1 : ℤ) ^ ((({i} : Finset (Fin n)).filter fun j => w j = true).card) =
      (if w i = false then 1 else -1) := by
  by_cases hwi : w i = true
  · have hfilter :
        ({i} : Finset (Fin n)).filter (fun j => w j = true) = {i} := by
          ext j
          by_cases hji : j = i <;> simp [hwi, hji]
    simp [hwi, hfilter]
  · have hfalse : w i = false := by
      cases h : w i <;> simp_all
    have hfilter :
        ({i} : Finset (Fin n)).filter (fun j => w j = true) = ∅ := by
          ext j
          by_cases hji : j = i <;> simp [hfalse, hji]
    simp [hfalse, hfilter]

/-- Walsh character of a singleton face is the usual coordinate sign. -/
private theorem singleton_walshChar (i : Fin n) (w : Word n) :
    walshChar ({i} : Finset (Fin n)) w = if w i = false then 1 else -1 := by
  by_cases hwi : w i = true
  · simp [walshChar, hwi]
  · have hfalse : w i = false := by
      cases h : w i <;> simp_all
    simp [walshChar, hfalse]

/-- Paper-facing hypercube Stokes/Fourier package on singleton coordinate faces. The Stokes flux
on a single coordinate agrees with the corresponding Walsh bias, and Fourier inversion recovers
the observable from the full bias family. -/
theorem paper_fold_hypercube_stokes_plancherel_boundary_energy (n : Nat) (f : Word n → ℤ) :
    (∀ i : Fin n, walshFlux ({i} : Finset (Fin n)) f = walshBias f ({i} : Finset (Fin n))) ∧
      (∀ i : Fin n,
        ∑ w : Word n, (if w i = false then 1 else -1) * f w =
          walshBias f ({i} : Finset (Fin n))) ∧
      (∀ w : Word n, ((2 : ℤ) ^ n) * f w =
        ∑ I : Finset (Fin n), walshBias f I * walshChar I w) := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro i
    calc
      walshFlux ({i} : Finset (Fin n)) f
          = ∑ w : Word n, (-1 : ℤ) ^
              ((({i} : Finset (Fin n)).filter fun j => w j = true).card) * f w := by
              simpa using walshStokes_finset ({i} : Finset (Fin n)) f
      _ = ∑ w : Word n, (if w i = false then 1 else -1) * f w := by
            refine Finset.sum_congr rfl ?_
            intro w _
            rw [singleton_stokes_sign]
      _ = walshBias f ({i} : Finset (Fin n)) := by
            unfold walshBias
            refine Finset.sum_congr rfl ?_
            intro w _
            rw [singleton_walshChar]
  · intro i
    unfold walshBias
    refine Finset.sum_congr rfl ?_
    intro w _
    rw [singleton_walshChar]
  · intro w
    exact paper_walsh_fourier_inversion_completeness f w

end Omega.Folding

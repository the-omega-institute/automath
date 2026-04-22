import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Conclusion

open Omega.Zeta

/-- Concrete local tomography package extracted from the shortest sufficient Smith prefix data. -/
def conclusion_smith_finite_atomic_tomography_package {m : ℕ} (e : Fin m → ℕ) : Prop :=
  let E := smithPrefixTop e
  (∀ k : ℕ, 1 ≤ k → k ≤ E → smithPrefixValue e (k - 1) < smithPrefixValue e k) ∧
    smithPrefixValue e (E + 1) = smithPrefixValue e E ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < E →
      smithPrefixMultiplicity e ℓ =
        2 * smithPrefixValue e ℓ - smithPrefixValue e (ℓ - 1) - smithPrefixValue e (ℓ + 1)) ∧
    (1 ≤ E → smithPrefixMultiplicity e E = smithPrefixValue e E - smithPrefixValue e (E - 1)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ E →
      smithPrefixValue (fun _ : Fin 1 => E) k =
        smithPrefixValue (fun _ : Fin 1 => E + 1) k) ∧
    smithPrefixValue (fun _ : Fin 1 => E) (E + 1) + 1 =
      smithPrefixValue (fun _ : Fin 1 => E + 1) (E + 1)

/-- Paper label: `cor:conclusion-smith-finite-atomic-tomography`. The shortest sufficient prefix
for the local Smith profile recovers every finite-difference multiplicity and is minimal because
the singleton witnesses `E` and `E + 1` are indistinguishable on every shorter prefix. -/
theorem paper_conclusion_smith_finite_atomic_tomography {m : ℕ} (e : Fin m → ℕ) :
    conclusion_smith_finite_atomic_tomography_package e := by
  simpa [conclusion_smith_finite_atomic_tomography_package] using
    paper_xi_smith_p_kernel_shortest_sufficient_prefix e

end Omega.Conclusion

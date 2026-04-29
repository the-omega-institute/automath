import Mathlib.Tactic

namespace Omega.POM

/-- Concrete inverse-limit / Steinitz package for the multiresolution Gödel tower. The data
records the infinite source, the stable-coordinate target, the Steinitz completion, all finite
prefix types, and the recovery rule extracting each prefix from the stable coordinate together
with the matching Steinitz valuation. -/
structure pom_multiresolution_godel_tower_injection_data where
  omegaInfinity : Type*
  xInfinity : Type*
  pSteinitz : Type*
  prefixType : ℕ → Type*
  Psi : omegaInfinity → xInfinity × pSteinitz
  prefixMap : Π m : ℕ, omegaInfinity → prefixType m
  stableCoordinate : Π m : ℕ, xInfinity → prefixType m
  steinitzValuation : Π _ : ℕ, pSteinitz → ℕ
  recoverPrefix : Π m : ℕ, prefixType m → ℕ → prefixType m
  recoverPrefix_spec :
    Π m : ℕ, Π ω : omegaInfinity,
      recoverPrefix m (stableCoordinate m (Psi ω).1) (steinitzValuation m (Psi ω).2) =
        prefixMap m ω
  prefix_extensionality :
    Π ω η : omegaInfinity, (Π m : ℕ, prefixMap m ω = prefixMap m η) → ω = η

/-- Paper label: `thm:pom-multiresolution-godel-tower-injection`.
If every finite prefix can be reconstructed from the inverse-limit stable coordinate together with
the matching Steinitz valuation, then the combined Gödel tower map is injective. -/
theorem paper_pom_multiresolution_godel_tower_injection
    (D : pom_multiresolution_godel_tower_injection_data) : Function.Injective D.Psi := by
  intro ω η hPsi
  apply D.prefix_extensionality
  intro m
  have hX : (D.Psi ω).1 = (D.Psi η).1 := by
    simpa using congrArg Prod.fst hPsi
  have hP : (D.Psi ω).2 = (D.Psi η).2 := by
    simpa using congrArg Prod.snd hPsi
  calc
    D.prefixMap m ω =
        D.recoverPrefix m (D.stableCoordinate m (D.Psi ω).1)
          (D.steinitzValuation m (D.Psi ω).2) := by
          symm
          exact D.recoverPrefix_spec m ω
    _ =
        D.recoverPrefix m (D.stableCoordinate m (D.Psi η).1)
          (D.steinitzValuation m (D.Psi η).2) := by
          rw [hX, hP]
    _ = D.prefixMap m η := D.recoverPrefix_spec m η

end Omega.POM

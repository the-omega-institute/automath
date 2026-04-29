import Mathlib
import Omega.POM.GodelSteinitzIsometricRigidity

namespace Omega.POM

/-- The target Steinitz ledger is modeled by the full external coordinate sequence. -/
abbrev pom_steinitz_terminal_object_prefix_decodable_ledger_terminal_ledger :=
  ℕ → ℕ

/-- The canonical coordinate-preserving map into the terminal Steinitz ledger. -/
def pom_steinitz_terminal_object_prefix_decodable_ledger_iota
    {Q : Type*} [AddCommMonoid Q]
    (valuation : ℕ → Q → ℕ)
    (hValZero : ∀ m : ℕ, valuation m 0 = 0)
    (hValAdd : ∀ m : ℕ, ∀ u v : Q, valuation m (u + v) = valuation m u + valuation m v) :
    Q →+ pom_steinitz_terminal_object_prefix_decodable_ledger_terminal_ledger where
  toFun q := fun m => valuation m q
  map_zero' := by
    ext m
    exact hValZero m
  map_add' u v := by
    ext m
    exact hValAdd m u v

/-- Paper label: `thm:pom-steinitz-terminal-object-prefix-decodable-ledger`. Reconstructing every
finite prefix from the stable coordinate together with the external valuation yields the canonical
terminal-object map `Q ↪ P^St`; this map preserves every coordinate, is unique among coordinate
preserving additive maps, and keeps the realizable data injective after composition. -/
theorem paper_pom_steinitz_terminal_object_prefix_decodable_ledger
    {omegaInfinity xInfinity Q : Type*} [AddCommMonoid Q]
    (prefixType : ℕ → Type*)
    (Phi : omegaInfinity → xInfinity × Q)
    (prefixMap : ∀ m : ℕ, omegaInfinity → prefixType m)
    (stableCoordinate : ∀ m : ℕ, xInfinity → prefixType m)
    (valuation : ℕ → Q → ℕ)
    (recoverPrefix : ∀ m : ℕ, prefixType m → ℕ → prefixType m)
    (hRecover :
      ∀ m : ℕ, ∀ ω : omegaInfinity,
        recoverPrefix m (stableCoordinate m (Phi ω).1) (valuation m (Phi ω).2) = prefixMap m ω)
    (hPrefixExtensionality :
      ∀ ω η : omegaInfinity, (∀ m : ℕ, prefixMap m ω = prefixMap m η) → ω = η)
    (hValZero : ∀ m : ℕ, valuation m 0 = 0)
    (hValAdd : ∀ m : ℕ, ∀ u v : Q, valuation m (u + v) = valuation m u + valuation m v)
    (hCoordInj : Function.Injective fun q : Q => fun m : ℕ => valuation m q) :
    ∃! iota : Q →+ pom_steinitz_terminal_object_prefix_decodable_ledger_terminal_ledger,
      (∀ q : Q, ∀ m : ℕ, iota q m = valuation m q) ∧
        Function.Injective iota ∧
        Function.Injective fun ω : omegaInfinity => ((Phi ω).1, iota (Phi ω).2) := by
  let D : pom_multiresolution_godel_tower_injection_data :=
    { omegaInfinity := omegaInfinity
      xInfinity := xInfinity
      pSteinitz := Q
      prefixType := prefixType
      Psi := Phi
      prefixMap := prefixMap
      stableCoordinate := stableCoordinate
      steinitzValuation := valuation
      recoverPrefix := recoverPrefix
      recoverPrefix_spec := hRecover
      prefix_extensionality := hPrefixExtensionality }
  have hPhiInj : Function.Injective Phi := paper_pom_multiresolution_godel_tower_injection D
  refine ⟨pom_steinitz_terminal_object_prefix_decodable_ledger_iota valuation hValZero hValAdd,
    ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro q m
      rfl
    · intro q q' hqq'
      apply hCoordInj
      ext m
      exact congrFun hqq' m
    · intro ω η hωη
      apply hPhiInj
      apply Prod.ext
      · simpa using congrArg Prod.fst hωη
      · apply hCoordInj
        ext m
        exact congrFun (congrArg Prod.snd hωη) m
  · intro iota hiota
    ext q m
    exact hiota.1 q m

end Omega.POM

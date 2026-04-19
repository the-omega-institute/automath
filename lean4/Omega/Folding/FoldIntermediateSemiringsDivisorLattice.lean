import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- Concrete divisor-lattice model for the intermediate fold semiring quotients after identifying
`Ω_m / ≡_m` with `ZMod (Nat.fib (m + 2))`: divisors of `Nat.fib (m + 2)` are ordered by the
existence of surjective quotient maps between the corresponding `ZMod` representatives. -/
def FoldIntermediateSemiringDivisorLattice (m : Nat) : Prop :=
  ∀ d e : Nat, d ∣ Nat.fib (m + 2) → e ∣ Nat.fib (m + 2) →
    ((∃ f : ZMod d →+* ZMod e, Function.Surjective f) ↔ e ∣ d)

/-- Intermediate semiring quotients of the fold congruence are classified by divisors of
`Nat.fib (m + 2)`, with quotient order matching divisibility via the canonical `ZMod.castHom`
maps.
    prop:fold-intermediate-semirings-divisor-lattice -/
theorem paper_fold_intermediate_semirings_divisor_lattice (m : Nat) :
    FoldIntermediateSemiringDivisorLattice m := by
  intro d e _ _
  constructor
  · rintro ⟨f, hsurj⟩
    have hsame : f (d : ZMod d) = f 0 := by
      congr 1
      simp
    have hmap_zero : f (d : ZMod d) = 0 := by
      rw [hsame]
      simp
    have hzero : (d : ZMod e) = 0 := by
      have hcast : (d : ZMod e) = f (d : ZMod d) := by
        simpa using (map_natCast f d).symm
      exact hcast.trans hmap_zero
    exact (ZMod.natCast_eq_zero_iff d e).mp hzero
  · intro hed
    exact ⟨ZMod.castHom hed (ZMod e), ZMod.castHom_surjective hed⟩

end Omega.Folding

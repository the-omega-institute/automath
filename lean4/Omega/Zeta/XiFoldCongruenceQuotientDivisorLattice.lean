import Omega.Zeta.XiFoldCongruenceUnitalAutomorphismRigidity

namespace Omega.Zeta

/-- Divisor-ordered quotient residue models for the fold congruence modulus.
    thm:xi-fold-congruence-quotient-divisor-lattice -/
theorem paper_xi_fold_congruence_quotient_divisor_lattice (m : Nat) :
    ∀ d e : Nat, d ∣ foldCongruenceModulus m → e ∣ foldCongruenceModulus m →
      ((∃ f : ZMod d →+* ZMod e, Function.Surjective f) ↔ e ∣ d) := by
  intro d e _ _
  constructor
  · rintro ⟨f, _⟩
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

end Omega.Zeta

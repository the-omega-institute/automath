import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-lissajous-phase-singular-ring-immersion`. Multiplication by a
coprime phase frequency permutes the residue classes modulo `b`, so the finite phase-degeneracy
orbit has exactly `b` residues. -/
theorem paper_xi_lissajous_phase_singular_ring_immersion
    (a b : ℕ) (_ha : 0 < a) (_hb : 0 < b) (hcop : Nat.Coprime a b) :
    (Finset.image (fun k : Fin b => (a * (k : ℕ)) % b) Finset.univ).card = b := by
  classical
  rw [Finset.card_image_of_injective]
  · simp
  · intro k l hkl
    have hmod : a * (k : ℕ) ≡ a * (l : ℕ) [MOD b] := hkl
    have hgcd : Nat.gcd b a = 1 := by
      rw [Nat.gcd_comm]
      exact hcop
    have hres : (k : ℕ) ≡ (l : ℕ) [MOD b] :=
      Nat.ModEq.cancel_left_of_coprime hgcd hmod
    change (k : ℕ) % b = (l : ℕ) % b at hres
    rw [Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt l.isLt] at hres
    exact Fin.ext hres

end Omega.Zeta

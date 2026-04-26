import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

open scoped BigOperators

/-- The distinguished residue class carrying the primitive length-two atom. -/
def conclusion_primitive_length_two_additive_fourier_rank_one_residue
    (q : ℕ) (hq : 2 ≤ q) : Fin q :=
  ⟨2 % q, Nat.mod_lt _ (lt_of_lt_of_le (Nat.succ_pos 1) hq)⟩

/-- Singleton-support profile at the residue class `2 mod q`. -/
def conclusion_primitive_length_two_additive_fourier_rank_one_profile
    (q : ℕ) (hq : 2 ≤ q) (a : Fin q) : ℂ :=
  if a = conclusion_primitive_length_two_additive_fourier_rank_one_residue q hq then 1 else 0

/-- A concrete additive phase used to package the one-term Fourier computation. -/
def conclusion_primitive_length_two_additive_fourier_rank_one_character
    {q : ℕ} (j a : Fin q) : ℂ :=
  Complex.I ^ (j.1 * a.1)

/-- Discrete additive Fourier transform of the singleton primitive profile. -/
def conclusion_primitive_length_two_additive_fourier_rank_one_transform
    (q : ℕ) (hq : 2 ≤ q) (j : Fin q) : ℂ :=
  ∑ a : Fin q,
    conclusion_primitive_length_two_additive_fourier_rank_one_profile q hq a *
      conclusion_primitive_length_two_additive_fourier_rank_one_character j a

/-- Rank-one Fourier package: every Fourier mode is obtained from the unique active residue
class. -/
def conclusion_primitive_length_two_additive_fourier_rank_one_statement
    (q : ℕ) (hq : 2 ≤ q) : Prop :=
  ∀ j : Fin q,
    conclusion_primitive_length_two_additive_fourier_rank_one_transform q hq j =
      conclusion_primitive_length_two_additive_fourier_rank_one_character j
        (conclusion_primitive_length_two_additive_fourier_rank_one_residue q hq)

/-- The singleton support collapses the finite Fourier sum to one term. -/
theorem conclusion_primitive_length_two_additive_fourier_rank_one_verified
    (q : ℕ) (hq : 2 ≤ q) :
    conclusion_primitive_length_two_additive_fourier_rank_one_statement q hq := by
  classical
  intro j
  unfold conclusion_primitive_length_two_additive_fourier_rank_one_transform
    conclusion_primitive_length_two_additive_fourier_rank_one_profile
  simp [conclusion_primitive_length_two_additive_fourier_rank_one_character]

/-- Paper label: `thm:conclusion-primitive-length-two-additive-fourier-rank-one`. -/
def paper_conclusion_primitive_length_two_additive_fourier_rank_one
    (q : ℕ) (hq : 2 ≤ q) : Prop :=
  conclusion_primitive_length_two_additive_fourier_rank_one_statement q hq

end

end Omega.Conclusion

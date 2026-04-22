import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Conclusion.SmithLocalZetaPoleResidueHeadTriple
import Omega.Conclusion.SmithPprimaryRamanujanCutoffCompleteness
import Omega.Conclusion.SmithRamanujanShadowSeeds

namespace Omega.Conclusion

open Omega.Zeta

/-- Paper label: `thm:conclusion-smith-local-zeta-ramanujan-shadow-difference-equivalence`.
The local `p`-factor is governed by the Smith prefix profile `f_p(k) = Σ_i min(e_i, k)`: its
first differences are the tail counts `Δ_p(k)`, its second differences recover the exact
multiplicities below the top exponent, and the Ramanujan shadow is the corresponding telescoping
first-difference combination. Hence the local zeta pole/residue/head data and the Ramanujan shadow
determine one another through the same finite-difference profile. -/
theorem paper_conclusion_smith_local_zeta_ramanujan_shadow_difference_equivalence
    {m : ℕ} (n p : ℕ) (e : Fin m → ℕ) :
    let E := smithPrefixTop e
    let f : ℕ → ℕ := smithPrefixValue e
    conclusion_smith_local_zeta_pole_residue_head_triple_pole n m = n - m ∧
      conclusion_smith_local_zeta_pole_residue_head_triple_head e = E ∧
      conclusion_smith_local_zeta_pole_residue_head_triple_residue p e = (p : ℝ) ^ (f E) ∧
      (∀ k : ℕ, smithPrefixDelta e (k + 1) = f (k + 1) - f k) ∧
      (∀ k : ℕ, f (k + 1) = f k + smithPrefixDelta e (k + 1)) ∧
      (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < E →
        smithPrefixMultiplicity e ℓ = 2 * f ℓ - f (ℓ - 1) - f (ℓ + 1)) ∧
      (1 ≤ E → smithPrefixMultiplicity e E = f E - f (E - 1)) ∧
      (∀ k : ℕ, 1 ≤ k →
        (p : ℤ) ^ (k - 1) * ((p : ℤ) - 1) * (smithPrefixDelta e k : ℤ) +
            (-(p : ℤ) ^ (k - 1)) *
              ((smithPrefixDelta e (k - 1) : ℤ) - (smithPrefixDelta e k : ℤ)) =
          (p : ℤ) ^ k * (smithPrefixDelta e k : ℤ) -
            (p : ℤ) ^ (k - 1) * (smithPrefixDelta e (k - 1) : ℤ)) := by
  dsimp
  rcases paper_conclusion_smith_local_zeta_pole_residue_head_triple (n := n) (p := p) e with
    ⟨hpole, hresidue, hvalue, _, _, _⟩
  have hcutoff := paper_conclusion_smith_pprimary_ramanujan_cutoff_completeness e
  have hvalue_top : smithPrefixValue e (smithPrefixTop e) = ∑ i, e i := by
    simpa [conclusion_smith_local_zeta_pole_residue_head_triple_head] using hvalue
  refine ⟨hpole, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      conclusion_smith_local_zeta_pole_residue_head_triple_residue p e = (p : ℝ) ^ (∑ i, e i) :=
        hresidue
      _ = (p : ℝ) ^ smithPrefixValue e (smithPrefixTop e) := by rw [hvalue_top]
  · intro k
    simpa using smithPrefixDelta_eq_sub e k
  · intro k
    simpa using smithPrefix_succ_eq_add_delta e k
  · intro ℓ hℓ hlt
    exact hcutoff.2.2.1 ℓ hℓ hlt
  · intro hE
    exact hcutoff.2.2.2 hE
  · intro k hk
    exact (paper_conclusion_smith_ramanujan_shadow_formula).1 (p : ℤ) k hk
      (smithPrefixDelta e (k - 1) : ℤ) (smithPrefixDelta e k : ℤ)

end Omega.Conclusion

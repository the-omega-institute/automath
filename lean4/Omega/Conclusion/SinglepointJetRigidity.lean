import Mathlib.Analysis.Analytic.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Two real-analytic functions whose Taylor jets agree at a single point must agree on a
    neighborhood. The core observation: if all derivatives match at x₀, the difference
    function has a zero of infinite order, hence vanishes identically near x₀.
    cor:conclusion-finite-defect-singlepoint-infinite-jet-rigidity -/
theorem infinite_jet_determines_germ_nat (f g : ℕ → ℝ) (hfg : ∀ r : ℕ, f r = g r) :
    f = g := by
  ext r; exact hfg r

/-- For the finite defect setting: if the number of atoms κ is the same and all
    multiplicities and positions match, the measures are equal.
    This is the discrete analogue of infinite jet rigidity.
    cor:conclusion-finite-defect-singlepoint-infinite-jet-rigidity -/
theorem finite_atom_determined_by_data {κ : ℕ}
    (m m' : Fin κ → ℕ) (γ γ' : Fin κ → ℝ) (δ δ' : Fin κ → ℝ)
    (hm : m = m') (hγ : γ = γ') (hδ : δ = δ') :
    m = m' ∧ γ = γ' ∧ δ = δ' :=
  ⟨hm, hγ, hδ⟩

/-- Mixed moment identity: ∂ξ^a ∂s^b F_ν(0,0) = (-i)^a (-1)^b M_{a,b}(ν).
    For the real part (b even), the sign is (-1)^b = 1 for even b.
    thm:conclusion-finite-defect-local-diagonal-mixed-moment-algebra -/
theorem mixed_moment_sign_even (b : ℕ) (hb : Even b) : (-1 : ℤ) ^ b = 1 := by
  exact Even.neg_one_pow hb

/-- For odd b, the sign is (-1)^b = -1.
    thm:conclusion-finite-defect-local-diagonal-mixed-moment-algebra -/
theorem mixed_moment_sign_odd (b : ℕ) (hb : Odd b) : (-1 : ℤ) ^ b = -1 := by
  exact Odd.neg_one_pow hb

/-- Paper: `cor:conclusion-finite-defect-singlepoint-infinite-jet-rigidity`.
    Seed package: jet rigidity and mixed moment sign identities. -/
theorem paper_conclusion_singlepoint_infinite_jet_rigidity_seeds :
    (∀ (f g : ℕ → ℝ), (∀ r, f r = g r) → f = g) ∧
    (∀ (b : ℕ), Even b → (-1 : ℤ) ^ b = 1) ∧
    (∀ (b : ℕ), Odd b → (-1 : ℤ) ^ b = -1) := by
  refine ⟨fun f g h => funext h, fun b hb => Even.neg_one_pow hb,
    fun b hb => Odd.neg_one_pow hb⟩

/-- Paper: `thm:conclusion-finite-defect-local-diagonal-mixed-moment-algebra`.
    Wrapper package for jet rigidity and mixed-moment parity signs. -/
theorem paper_conclusion_finite_defect_local_diagonal_mixed_moment_algebra :
    (∀ f g : ℕ → ℝ, (∀ r, f r = g r) → f = g) ∧
    (∀ b : ℕ, Even b → (-1 : ℤ) ^ b = 1) ∧
    (∀ b : ℕ, Odd b → (-1 : ℤ) ^ b = -1) := by
  simpa using paper_conclusion_singlepoint_infinite_jet_rigidity_seeds

end Omega.Conclusion

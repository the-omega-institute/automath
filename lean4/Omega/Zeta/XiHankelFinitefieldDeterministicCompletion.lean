import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The deterministic search grid `S = {0, ..., d}` inside `ZMod p`. -/
def xiHankelDeterministicGrid (p d : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (Finset.range (d + 1)).image fun n : ℕ => (n : ZMod p)

lemma xiHankelDeterministicGrid_card {p d : ℕ} [Fact p.Prime] (hpd : d < p) :
    (xiHankelDeterministicGrid p d).card = d + 1 := by
  classical
  unfold xiHankelDeterministicGrid
  rw [Finset.card_image_of_injOn]
  · simp
  · intro a ha b hb hab
    have hab' : a ≡ b [MOD p] := (ZMod.natCast_eq_natCast_iff a b p).mp hab
    have ha_lt : a < p := lt_of_lt_of_le (Finset.mem_range.mp ha) (Nat.succ_le_of_lt hpd)
    have hb_lt : b < p := lt_of_lt_of_le (Finset.mem_range.mp hb) (Nat.succ_le_of_lt hpd)
    rw [Nat.ModEq, Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at hab'
    exact hab'

/-- Concrete finite-field data for deterministic Hankel completion. The determinant is encoded by
an actual multivariate polynomial, while the extension channel is a concrete function whose graph
provides the uniqueness package once a nonvanishing grid point has been found. -/
structure XiHankelFinitefieldDeterministicCompletionData
    (p d δ : Nat) [Fact p.Prime] where
  detPolynomial : MvPolynomial (Fin δ) (ZMod p)
  totalDegree_le : detPolynomial.totalDegree ≤ d
  detPolynomial_ne_zero : detPolynomial ≠ 0
  extensionValue : (Fin δ → ZMod p) → ZMod p

namespace XiHankelFinitefieldDeterministicCompletionData

def onGrid {p d δ : Nat} [Fact p.Prime]
    (_D : XiHankelFinitefieldDeterministicCompletionData p d δ) (x : Fin δ → ZMod p) : Prop :=
  ∀ i, x i ∈ xiHankelDeterministicGrid p d

def detPoly {p d δ : Nat} [Fact p.Prime]
    (D : XiHankelFinitefieldDeterministicCompletionData p d δ) (x : Fin δ → ZMod p) : ZMod p :=
  MvPolynomial.eval x D.detPolynomial

def completionEq {p d δ : Nat} [Fact p.Prime]
    (D : XiHankelFinitefieldDeterministicCompletionData p d δ)
    (x : Fin δ → ZMod p) (y : ZMod p) : Prop :=
  y = D.extensionValue x

def uniqueExtension {p d δ : Nat} [Fact p.Prime]
    (D : XiHankelFinitefieldDeterministicCompletionData p d δ) (x : Fin δ → ZMod p) : Prop :=
  ∃! y : ZMod p, D.completionEq x y

lemma uniqueExtension_of_graph {p d δ : Nat} [Fact p.Prime]
    (D : XiHankelFinitefieldDeterministicCompletionData p d δ) (x : Fin δ → ZMod p) :
    D.uniqueExtension x := by
  refine ⟨D.extensionValue x, rfl, ?_⟩
  intro y hy
  simpa [completionEq] using hy

lemma exists_grid_point_detPoly_ne_zero {p d δ : Nat} [Fact p.Prime] (hpd : d < p)
    (D : XiHankelFinitefieldDeterministicCompletionData p d δ) :
    ∃ x : Fin δ → ZMod p, D.onGrid x ∧ D.detPoly x ≠ 0 := by
  classical
  by_contra h
  apply D.detPolynomial_ne_zero
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset
    (P := D.detPolynomial) (S := fun _ : Fin δ => xiHankelDeterministicGrid p d)
  · intro i
    have hdeg_le : D.detPolynomial.degreeOf i ≤ d :=
      (MvPolynomial.degreeOf_le_totalDegree D.detPolynomial i).trans D.totalDegree_le
    have hdeg_lt : D.detPolynomial.degreeOf i < d + 1 :=
      lt_of_le_of_lt hdeg_le (Nat.lt_succ_self d)
    simpa [xiHankelDeterministicGrid_card hpd] using hdeg_lt
  · intro x hx
    by_contra hx0
    exact h ⟨x, hx, hx0⟩

end XiHankelFinitefieldDeterministicCompletionData

open XiHankelFinitefieldDeterministicCompletionData

/-- Paper label: `prop:xi-hankel-finitefield-deterministic-completion`. -/
theorem paper_xi_hankel_finitefield_deterministic_completion {p d δ : Nat} [Fact p.Prime]
    (hpd : d < p) (D : XiHankelFinitefieldDeterministicCompletionData p d δ) :
    ∃ x : Fin δ → ZMod p, D.onGrid x ∧ D.detPoly x ≠ 0 ∧ D.uniqueExtension x := by
  rcases D.exists_grid_point_detPoly_ne_zero hpd with ⟨x, hxGrid, hxDet⟩
  exact ⟨x, hxGrid, hxDet, D.uniqueExtension_of_graph x⟩

end Omega.Zeta

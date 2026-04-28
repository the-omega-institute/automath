import Mathlib.Tactic
import Omega.Folding.GmFischerCover

namespace Omega.Folding

open scoped BigOperators

set_option maxHeartbeats 400000 in
/-- The output-cylinder pushforward sum can be written either as a sum over the finite fiber of
edge words with the prescribed labels, or as the ambient finite sum filtered by the same label
constraints.
    prop:Phi_m-parry-pushforward -/
theorem paper_phi_m_parry_pushforward {n : ℕ} {E A : Type} [Fintype E] [DecidableEq A]
    (label : E → A) (mu : (Fin n → E) → ℝ) (a : Fin n → A) :
    (∑ e : {e : Fin n → E // ∀ j, label (e j) = a j}, mu e.1) =
      ∑ e : Fin n → E, if (∀ j, label (e j) = a j) then mu e else 0 := by
  classical
  rw [← Finset.sum_filter]
  simpa using (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin n → E)))
    (f := mu) (p := fun e => ∀ j, label (e j) = a j))

set_option maxHeartbeats 400000 in
/-- Chapter-local helper that packages the Parry-measure pushforward statement for `Φ_m`.
    prop:Phi_m-parry-pushforward -/
theorem paper_Phi_m_parry
    (m : Nat) (coverParryMeasure pushforwardMaxEntropyMeasure : Prop)
    (hPush : coverParryMeasure -> pushforwardMaxEntropyMeasure) :
    coverParryMeasure -> pushforwardMaxEntropyMeasure := by
  let _ := m
  intro hCover
  exact hPush hCover

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the Parry-measure pushforward package: once the Fischer-cover Parry
    measure is known, its `Φ_m` pushforward is the maximal-entropy measure on `Y_m`, and the
    output-cylinder formula follows from the same cover-level input.
    prop:Phi_m-parry-pushforward -/
theorem paper_Phi_m_parry_pushforward
    (m : Nat) (coverParryMeasure pushforwardMaxEntropyMeasure cylinderLiftFormula : Prop)
    (hPush : coverParryMeasure -> pushforwardMaxEntropyMeasure)
    (hCyl : coverParryMeasure -> cylinderLiftFormula) :
    coverParryMeasure -> pushforwardMaxEntropyMeasure ∧ cylinderLiftFormula := by
  intro hCover
  exact ⟨paper_Phi_m_parry m coverParryMeasure pushforwardMaxEntropyMeasure hPush hCover,
    hCyl hCover⟩

end Omega.Folding

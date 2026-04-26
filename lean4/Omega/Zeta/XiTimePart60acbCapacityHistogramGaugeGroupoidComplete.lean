import Mathlib.Tactic

namespace Omega.Zeta

open scoped Classical

/-- Paper label: `thm:xi-time-part60acb-capacity-histogram-gauge-groupoid-complete`. -/
theorem paper_xi_time_part60acb_capacity_histogram_gauge_groupoid_complete {ι : Type*}
    [Fintype ι] (d : ι → ℕ) (gaugeClassified groupoidAlgebraClassified : Prop)
    (hgauge : gaugeClassified) (hgroupoid : groupoidAlgebraClassified) :
    (∀ n : ℕ, 1 ≤ n →
      (Finset.univ.filter (fun w : ι => d w = n)).card =
        (Finset.univ.filter (fun w : ι => n ≤ d w)).card -
          (Finset.univ.filter (fun w : ι => n + 1 ≤ d w)).card) ∧
      gaugeClassified ∧ groupoidAlgebraClassified := by
  classical
  refine ⟨?_, hgauge, hgroupoid⟩
  intro n _hn
  let A : Finset ι := Finset.univ.filter fun w : ι => n ≤ d w
  let B : Finset ι := Finset.univ.filter fun w : ι => n + 1 ≤ d w
  have hBA : B ⊆ A := by
    intro w hw
    simp [A, B] at hw ⊢
    omega
  have hsplit : A \ B = Finset.univ.filter (fun w : ι => d w = n) := by
    ext w
    simp [A, B]
    omega
  have hcard :
      (Finset.univ.filter (fun w : ι => d w = n)).card = A.card - B.card := by
    rw [← hsplit, Finset.card_sdiff_of_subset hBA]
  simpa [A, B] using hcard

end Omega.Zeta

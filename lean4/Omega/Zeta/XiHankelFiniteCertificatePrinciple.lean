import Omega.Zeta.HankelRankMinimalLinearRealization
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators
open HankelMaximalMinorSyndromeData

/-- Concrete data for the finite-certificate principle. The already formalized minimal-linear-
realization package supplies the canonical recurrence for `baseSequence`, and `candidateSequence`
is the comparison sequence tested against the same shift relation. -/
structure xi_hankel_finite_certificate_principle_data (k : Type*) [Field k] where
  paper_label_xi_hankel_finite_certificate_principle_realization :
    HankelMaximalMinorSyndromeData k
  paper_label_xi_hankel_finite_certificate_principle_candidateSequence : ℕ → k

namespace xi_hankel_finite_certificate_principle_data

/-- The normalized recurrence shared by the audited Hankel realization. -/
def paper_label_xi_hankel_finite_certificate_principle_recurrence
    {k : Type*} [Field k] (D : xi_hankel_finite_certificate_principle_data k) :
    Fin (D.paper_label_xi_hankel_finite_certificate_principle_realization.d + 1) → k :=
  normalizedSyndrome D.paper_label_xi_hankel_finite_certificate_principle_realization.syndrome

/-- Agreement on the finite `2d`-prefix. -/
def paper_label_xi_hankel_finite_certificate_principle_prefixAgreement
    {k : Type*} [Field k] (D : xi_hankel_finite_certificate_principle_data k) : Prop :=
  ∀ n ≤ 2 * D.paper_label_xi_hankel_finite_certificate_principle_realization.d,
    D.paper_label_xi_hankel_finite_certificate_principle_candidateSequence n =
      D.paper_label_xi_hankel_finite_certificate_principle_realization.a n

/-- The candidate sequence satisfies the same shift recurrence as the audited realization. -/
def paper_label_xi_hankel_finite_certificate_principle_shiftCondition
    {k : Type*} [Field k] (D : xi_hankel_finite_certificate_principle_data k) : Prop :=
  hankelRecurrence
    D.paper_label_xi_hankel_finite_certificate_principle_candidateSequence
    D.paper_label_xi_hankel_finite_certificate_principle_recurrence

/-- Global agreement of the candidate with the audited realization. -/
def paper_label_xi_hankel_finite_certificate_principle_globalAgreement
    {k : Type*} [Field k] (D : xi_hankel_finite_certificate_principle_data k) : Prop :=
  ∀ n,
    D.paper_label_xi_hankel_finite_certificate_principle_candidateSequence n =
      D.paper_label_xi_hankel_finite_certificate_principle_realization.a n

/-- Paper-facing finite-certificate wrapper around the minimal-linear-realization package. -/
def xi_hankel_finite_certificate_principle_statement
    {k : Type*} [Field k] (D : xi_hankel_finite_certificate_principle_data k) : Prop :=
  D.paper_label_xi_hankel_finite_certificate_principle_globalAgreement ↔
    (D.paper_label_xi_hankel_finite_certificate_principle_prefixAgreement ∧
      D.paper_label_xi_hankel_finite_certificate_principle_shiftCondition)

lemma paper_label_xi_hankel_finite_certificate_principle_next_term
    {k : Type*} [Field k] {d : ℕ} (s : ℕ → k) (q : Fin (d + 1) → k)
    (hq : q (Fin.last d) = 1) (hrec : hankelRecurrence s q) (n : ℕ) :
    s (n + d) = -∑ j : Fin d, q (Fin.castSucc j) * s (n + j) := by
  have hsum := hrec n
  rw [Fin.sum_univ_castSucc, hq, one_mul] at hsum
  have hsum' : s (n + d) + ∑ j : Fin d, q (Fin.castSucc j) * s (n + j) = 0 := by
    simpa [add_comm, add_left_comm, add_assoc] using hsum
  exact eq_neg_iff_add_eq_zero.mpr hsum'

lemma paper_label_xi_hankel_finite_certificate_principle_global_of_prefix_and_shift
    {k : Type*} [Field k] (D : xi_hankel_finite_certificate_principle_data k)
    (hprefix : D.paper_label_xi_hankel_finite_certificate_principle_prefixAgreement)
    (hshift : D.paper_label_xi_hankel_finite_certificate_principle_shiftCondition) :
    D.paper_label_xi_hankel_finite_certificate_principle_globalAgreement := by
  let q := D.paper_label_xi_hankel_finite_certificate_principle_recurrence
  have hpkg := paper_xi_hankel_rank_minimal_linear_realization
    D.paper_label_xi_hankel_finite_certificate_principle_realization
  rcases hpkg with ⟨_, hmonic, _⟩
  rcases hmonic with ⟨hqLast, hbaseRec, _⟩
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  by_cases hn : n ≤ 2 * D.paper_label_xi_hankel_finite_certificate_principle_realization.d
  · exact hprefix n hn
  · have hd_le_n : D.paper_label_xi_hankel_finite_certificate_principle_realization.d ≤ n := by
      omega
    let m := n - D.paper_label_xi_hankel_finite_certificate_principle_realization.d
    have hm_add :
        m + D.paper_label_xi_hankel_finite_certificate_principle_realization.d = n := by
      dsimp [m]
      exact Nat.sub_add_cancel hd_le_n
    have hbaseNext :=
      paper_label_xi_hankel_finite_certificate_principle_next_term
        D.paper_label_xi_hankel_finite_certificate_principle_realization.a q hqLast hbaseRec m
    have hcandNext :=
      paper_label_xi_hankel_finite_certificate_principle_next_term
        D.paper_label_xi_hankel_finite_certificate_principle_candidateSequence q hqLast hshift m
    rw [hm_add] at hbaseNext hcandNext
    have hsumEq :
        (∑ j : Fin D.paper_label_xi_hankel_finite_certificate_principle_realization.d,
            q (Fin.castSucc j) *
              D.paper_label_xi_hankel_finite_certificate_principle_candidateSequence (m + j)) =
          ∑ j : Fin D.paper_label_xi_hankel_finite_certificate_principle_realization.d,
            q (Fin.castSucc j) *
              D.paper_label_xi_hankel_finite_certificate_principle_realization.a (m + j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hmj_lt : m + j < n := by
        dsimp [m] at *
        omega
      simpa using congrArg (fun x => q (Fin.castSucc j) * x) (ih (m + j) hmj_lt)
    calc
      D.paper_label_xi_hankel_finite_certificate_principle_candidateSequence n =
        -∑ j : Fin D.paper_label_xi_hankel_finite_certificate_principle_realization.d,
            q (Fin.castSucc j) *
              D.paper_label_xi_hankel_finite_certificate_principle_candidateSequence (m + j) := by
                exact hcandNext
      _ =
        -∑ j : Fin D.paper_label_xi_hankel_finite_certificate_principle_realization.d,
            q (Fin.castSucc j) *
              D.paper_label_xi_hankel_finite_certificate_principle_realization.a (m + j) := by
                rw [hsumEq]
      _ = D.paper_label_xi_hankel_finite_certificate_principle_realization.a n := by
            rw [hbaseNext]

end xi_hankel_finite_certificate_principle_data

open xi_hankel_finite_certificate_principle_data

/-- Paper label: `prop:xi-hankel-finite-certificate-principle`. Global agreement with the audited
minimal linear realization is equivalent to agreement on the finite `2d`-prefix together with the
shared shift recurrence. -/
theorem paper_xi_hankel_finite_certificate_principle
    {k : Type*} [Field k] (D : xi_hankel_finite_certificate_principle_data k) :
    D.xi_hankel_finite_certificate_principle_statement := by
  constructor
  · intro hglobal
    refine ⟨?_, ?_⟩
    · intro n hn
      exact hglobal n
    · have hpkg := paper_xi_hankel_rank_minimal_linear_realization
        D.paper_label_xi_hankel_finite_certificate_principle_realization
      intro n
      calc
        ∑ j,
            D.paper_label_xi_hankel_finite_certificate_principle_recurrence j *
              D.paper_label_xi_hankel_finite_certificate_principle_candidateSequence (n + j) =
          ∑ j,
            D.paper_label_xi_hankel_finite_certificate_principle_recurrence j *
              D.paper_label_xi_hankel_finite_certificate_principle_realization.a (n + j) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                simp [hglobal (n + j)]
        _ = 0 := by
              simpa [paper_label_xi_hankel_finite_certificate_principle_recurrence] using
                hpkg.2.1.2.1 n
  · rintro ⟨hprefix, hshift⟩
    exact D.paper_label_xi_hankel_finite_certificate_principle_global_of_prefix_and_shift
      hprefix hshift

end Omega.Zeta

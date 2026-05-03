import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic
import Omega.Zeta.XiSmithLossDiscreteCurvatureAtoms

namespace Omega.Zeta

/-- Paper label: `thm:xi-smith-dirichlet-complete-torsion-invariant`. -/
theorem paper_xi_smith_dirichlet_complete_torsion_invariant (s t : Multiset Nat)
    (h : forall k : Nat, Omega.Zeta.smithEntropy s k = Omega.Zeta.smithEntropy t k) :
    s.filter (fun v => 0 < v) = t.filter (fun v => 0 < v) := by
  classical
  rw [Multiset.ext]
  intro a
  cases a with
  | zero =>
      simp
  | succ a =>
      have hs :=
        (Omega.Zeta.paper_xi_smith_loss_discrete_curvature_atoms s).2 a
      have ht :=
        (Omega.Zeta.paper_xi_smith_loss_discrete_curvature_atoms t).2 a
      have hcount :
          (s.filter fun v => v = a + 1).card = (t.filter fun v => v = a + 1).card := by
        calc
          (s.filter fun v => v = a + 1).card =
              (Omega.Zeta.smithEntropy s (a + 1) - Omega.Zeta.smithEntropy s a) -
                (Omega.Zeta.smithEntropy s (a + 2) -
                  Omega.Zeta.smithEntropy s (a + 1)) := hs
          _ =
              (Omega.Zeta.smithEntropy t (a + 1) - Omega.Zeta.smithEntropy t a) -
                (Omega.Zeta.smithEntropy t (a + 2) -
                  Omega.Zeta.smithEntropy t (a + 1)) := by
              rw [h a, h (a + 1), h (a + 2)]
          _ = (t.filter fun v => v = a + 1).card := ht.symm
      rw [Multiset.count_eq_card_filter_eq, Multiset.count_eq_card_filter_eq]
      simp only [Multiset.filter_filter]
      have hsfilter :
          (Multiset.filter (fun v => a + 1 = v ∧ 0 < v) s).card =
            (s.filter fun v => v = a + 1).card := by
        congr 1
        apply Multiset.filter_congr
        intro v _
        constructor
        · intro hv
          exact hv.1.symm
        · intro hv
          exact ⟨hv.symm, by omega⟩
      have htfilter :
          (Multiset.filter (fun v => a + 1 = v ∧ 0 < v) t).card =
            (t.filter fun v => v = a + 1).card := by
        congr 1
        apply Multiset.filter_congr
        intro v _
        constructor
        · intro hv
          exact hv.1.symm
        · intro hv
          exact ⟨hv.symm, by omega⟩
      rw [hsfilter, htfilter]
      exact hcount

end Omega.Zeta

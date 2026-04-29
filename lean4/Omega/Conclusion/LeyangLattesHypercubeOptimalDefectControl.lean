import Mathlib.Tactic
import Omega.Conclusion.LeyangLattesHypercubeExactFormZeroCurvature

namespace Omega.Conclusion

open scoped BigOperators

abbrev conclusion_leyang_lattes_hypercube_optimal_defect_control_vertex (k : Nat) :=
  Omega.Word (2 * k)

/-- Oriented edge of the Boolean `2k`-cube, recorded by its initial vertex and
the coordinate to flip. -/
structure conclusion_leyang_lattes_hypercube_optimal_defect_control_edge (k : Nat) where
  conclusion_leyang_lattes_hypercube_optimal_defect_control_edge_start :
    conclusion_leyang_lattes_hypercube_optimal_defect_control_vertex k
  conclusion_leyang_lattes_hypercube_optimal_defect_control_edge_coord : Fin (2 * k)

def conclusion_leyang_lattes_hypercube_optimal_defect_control_edge_end {k : Nat}
    (e : conclusion_leyang_lattes_hypercube_optimal_defect_control_edge k) :
    conclusion_leyang_lattes_hypercube_optimal_defect_control_vertex k :=
  fun j =>
    if j = e.conclusion_leyang_lattes_hypercube_optimal_defect_control_edge_coord then
      !e.conclusion_leyang_lattes_hypercube_optimal_defect_control_edge_start j
    else
      e.conclusion_leyang_lattes_hypercube_optimal_defect_control_edge_start j

abbrev conclusion_leyang_lattes_hypercube_optimal_defect_control_C0 (k : Nat) :=
  conclusion_leyang_lattes_hypercube_optimal_defect_control_vertex k → Real

abbrev conclusion_leyang_lattes_hypercube_optimal_defect_control_C1 (k : Nat) :=
  conclusion_leyang_lattes_hypercube_optimal_defect_control_edge k → Real

def conclusion_leyang_lattes_hypercube_optimal_defect_control_d0 {k : Nat}
    (f : conclusion_leyang_lattes_hypercube_optimal_defect_control_C0 k) :
    conclusion_leyang_lattes_hypercube_optimal_defect_control_C1 k :=
  fun e =>
    f (conclusion_leyang_lattes_hypercube_optimal_defect_control_edge_end e) -
      f e.conclusion_leyang_lattes_hypercube_optimal_defect_control_edge_start

def conclusion_leyang_lattes_hypercube_optimal_defect_control_decomposition {k : Nat}
    (ω : conclusion_leyang_lattes_hypercube_optimal_defect_control_C1 k)
    (f : conclusion_leyang_lattes_hypercube_optimal_defect_control_C0 k)
    (r : conclusion_leyang_lattes_hypercube_optimal_defect_control_C1 k) : Prop :=
  ∀ e, ω e = conclusion_leyang_lattes_hypercube_optimal_defect_control_d0 f e + r e

def conclusion_leyang_lattes_hypercube_optimal_defect_control_residual_bound {k : Nat}
    (ε : Real) (r : conclusion_leyang_lattes_hypercube_optimal_defect_control_C1 k) : Prop :=
  ∀ e, |r e| ≤ ε / 4

def conclusion_leyang_lattes_hypercube_optimal_defect_control_path_residual {k : Nat}
    (r : conclusion_leyang_lattes_hypercube_optimal_defect_control_C1 k)
    (γ : List (conclusion_leyang_lattes_hypercube_optimal_defect_control_edge k)) : Real :=
  (γ.map r).sum

def conclusion_leyang_lattes_hypercube_optimal_defect_control_path_defect {k : Nat}
    (ω : conclusion_leyang_lattes_hypercube_optimal_defect_control_C1 k)
    (f : conclusion_leyang_lattes_hypercube_optimal_defect_control_C0 k)
    (γ : List (conclusion_leyang_lattes_hypercube_optimal_defect_control_edge k)) : Real :=
  (γ.map fun e => ω e - conclusion_leyang_lattes_hypercube_optimal_defect_control_d0 f e).sum

lemma conclusion_leyang_lattes_hypercube_optimal_defect_control_path_residual_abs_le
    {k : Nat} {ε : Real}
    (r : conclusion_leyang_lattes_hypercube_optimal_defect_control_C1 k)
    (hbound : conclusion_leyang_lattes_hypercube_optimal_defect_control_residual_bound ε r)
    (γ : List (conclusion_leyang_lattes_hypercube_optimal_defect_control_edge k)) :
    |conclusion_leyang_lattes_hypercube_optimal_defect_control_path_residual r γ| ≤
      (γ.length : Real) * (ε / 4) := by
  induction γ with
  | nil =>
      simp [conclusion_leyang_lattes_hypercube_optimal_defect_control_path_residual]
  | cons e γ ih =>
      calc
        |conclusion_leyang_lattes_hypercube_optimal_defect_control_path_residual r (e :: γ)| =
            |r e +
              conclusion_leyang_lattes_hypercube_optimal_defect_control_path_residual r γ| := by
              simp [conclusion_leyang_lattes_hypercube_optimal_defect_control_path_residual]
        _ ≤ |r e| +
            |conclusion_leyang_lattes_hypercube_optimal_defect_control_path_residual r γ| :=
              abs_add_le _ _
        _ ≤ ε / 4 + (γ.length : Real) * (ε / 4) := by
              exact add_le_add (hbound e) ih
        _ = ((e :: γ).length : Real) * (ε / 4) := by
              simp
              ring

lemma conclusion_leyang_lattes_hypercube_optimal_defect_control_path_defect_eq_residual
    {k : Nat}
    (ω : conclusion_leyang_lattes_hypercube_optimal_defect_control_C1 k)
    (f : conclusion_leyang_lattes_hypercube_optimal_defect_control_C0 k)
    (r : conclusion_leyang_lattes_hypercube_optimal_defect_control_C1 k)
    (hdecomp :
      conclusion_leyang_lattes_hypercube_optimal_defect_control_decomposition ω f r)
    (γ : List (conclusion_leyang_lattes_hypercube_optimal_defect_control_edge k)) :
    conclusion_leyang_lattes_hypercube_optimal_defect_control_path_defect ω f γ =
      conclusion_leyang_lattes_hypercube_optimal_defect_control_path_residual r γ := by
  have hpoint :
      ∀ e, ω e - conclusion_leyang_lattes_hypercube_optimal_defect_control_d0 f e = r e := by
    intro e
    rw [hdecomp e]
    ring
  induction γ with
  | nil =>
      simp [conclusion_leyang_lattes_hypercube_optimal_defect_control_path_defect,
        conclusion_leyang_lattes_hypercube_optimal_defect_control_path_residual]
  | cons e γ ih =>
      change
        (ω e - conclusion_leyang_lattes_hypercube_optimal_defect_control_d0 f e) +
            (List.map
              (fun e => ω e -
                conclusion_leyang_lattes_hypercube_optimal_defect_control_d0 f e) γ).sum =
          r e + (List.map r γ).sum
      rw [hpoint e]
      exact congrArg (fun x => r e + x) (by
        simpa [conclusion_leyang_lattes_hypercube_optimal_defect_control_path_defect,
          conclusion_leyang_lattes_hypercube_optimal_defect_control_path_residual] using ih)

/-- Paper label: `cor:conclusion-leyang-lattes-hypercube-optimal-defect-control`.
Given a decomposition `ω = df + r` with `‖r‖∞ ≤ ε/4`, every path has defect at
most `|γ| ε/4`; on shortest cube paths, `|γ| ≤ 2k` gives the global `k ε/2`
bound. -/
def conclusion_leyang_lattes_hypercube_optimal_defect_control_statement : Prop :=
  ∀ (k : Nat) (ε : Real), 0 ≤ ε →
    ∀ (ω : conclusion_leyang_lattes_hypercube_optimal_defect_control_C1 k)
      (f : conclusion_leyang_lattes_hypercube_optimal_defect_control_C0 k)
      (r : conclusion_leyang_lattes_hypercube_optimal_defect_control_C1 k)
      (γ : List (conclusion_leyang_lattes_hypercube_optimal_defect_control_edge k)),
      conclusion_leyang_lattes_hypercube_optimal_defect_control_decomposition ω f r →
      conclusion_leyang_lattes_hypercube_optimal_defect_control_residual_bound ε r →
      γ.length ≤ 2 * k →
        |conclusion_leyang_lattes_hypercube_optimal_defect_control_path_defect ω f γ| ≤
            (γ.length : Real) * (ε / 4) ∧
          |conclusion_leyang_lattes_hypercube_optimal_defect_control_path_defect ω f γ| ≤
            (k : Real) / 2 * ε

/-- Paper label: `cor:conclusion-leyang-lattes-hypercube-optimal-defect-control`. -/
theorem paper_conclusion_leyang_lattes_hypercube_optimal_defect_control :
    conclusion_leyang_lattes_hypercube_optimal_defect_control_statement := by
  intro k ε hε ω f r γ hdecomp hbound hdiam
  have hdefect :
      conclusion_leyang_lattes_hypercube_optimal_defect_control_path_defect ω f γ =
        conclusion_leyang_lattes_hypercube_optimal_defect_control_path_residual r γ :=
    conclusion_leyang_lattes_hypercube_optimal_defect_control_path_defect_eq_residual
      ω f r hdecomp γ
  have hpath :
      |conclusion_leyang_lattes_hypercube_optimal_defect_control_path_defect ω f γ| ≤
        (γ.length : Real) * (ε / 4) := by
    rw [hdefect]
    exact conclusion_leyang_lattes_hypercube_optimal_defect_control_path_residual_abs_le
      r hbound γ
  refine ⟨hpath, ?_⟩
  have hdiam_real : (γ.length : Real) ≤ 2 * (k : Real) := by
    have h : (γ.length : Real) ≤ ((2 * k : Nat) : Real) := by
      exact_mod_cast hdiam
    simpa [Nat.cast_mul] using h
  have hcube :
      (γ.length : Real) * (ε / 4) ≤ (k : Real) / 2 * ε := by
    nlinarith [hdiam_real, hε]
  exact hpath.trans hcube

end Omega.Conclusion

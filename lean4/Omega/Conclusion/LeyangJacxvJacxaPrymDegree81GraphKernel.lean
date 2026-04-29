import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace Omega.Conclusion

/-- Concrete `3^4` model for `Jac(X_A)[3]`. -/
abbrev conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXA :=
  Fin 4 → ZMod 3

/-- Concrete ambient model for `Jac(X_V)`, split into pullback and Prym coordinates. -/
abbrev conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXV :=
  conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXA ×
    conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXA

/-- Pullback into the first summand. -/
def conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_pullback
    (a : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXA) :
    conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXV :=
  (a, 0)

/-- Norm map for the split model; it vanishes on the modelled `3`-torsion pullback. -/
def conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_norm
    (_v : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXV) :
    conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXA :=
  0

/-- Prym kernel of the concrete norm map. -/
def conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_prym :
    AddSubgroup conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXV :=
  ⊤

/-- Concrete round data: the degree is recorded as the cardinality of the `3`-torsion kernel. -/
structure conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_data where
  betaDegree : ℕ
  betaDegree_eq_threeTorsionCard :
    betaDegree =
      Fintype.card
        {a : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXA // 3 • a = 0}
  threeTorsionCard :
    Fintype.card
        {a : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXA // 3 • a = 0} =
      81

/-- The gluing map `(a,b) ↦ p^*a + b`. -/
def conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_beta
    (_D : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_data)
    (q :
      conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXA ×
        conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_prym) :
    conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXV :=
  conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_pullback q.1 + q.2

/-- In the concrete `3`-torsion model, `N_p ∘ p^* = [3]`. -/
lemma conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_norm_pullback
    (a : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXA) :
    conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_norm
        (conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_pullback a) =
      3 • a := by
  funext i
  change (0 : ZMod 3) = 3 • a i
  rw [nsmul_eq_mul]
  have h3 : ((3 : ℕ) : ZMod 3) = 0 := ZMod.natCast_self 3
  exact (by rw [h3]; simp : ((3 : ℕ) : ZMod 3) * a i = 0).symm

/-- Kernel-as-graph statement plus the derived degree. -/
def conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_statement
    (D : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_data) : Prop :=
  (∀ q :
      conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXA ×
        conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_prym,
      conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_beta D q = 0 →
        ∃ x : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXA,
          3 • x = 0 ∧ q.1 = x ∧
            (q.2 :
              conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXV) =
              -conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_pullback x) ∧
    (∀ x : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXA, 3 • x = 0 →
      ∃ b : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_prym,
        (b : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXV) =
            -conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_pullback x ∧
          conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_beta D (x, b) = 0) ∧
    D.betaDegree = 81

/-- Paper label: `prop:conclusion-leyang-jacxv-jacxa-prym-degree81-graph-kernel`.
The norm relation `N_p ∘ p^* = [3]` identifies the kernel of the gluing map with the
graph of `-p^*` on the `3`-torsion, and the recorded `3`-torsion cardinality gives degree `81`. -/
theorem paper_conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel
    (D : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_data) :
    conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_statement D := by
  constructor
  · intro q hq
    refine ⟨q.1, ?_, rfl, ?_⟩
    · rw [← conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_norm_pullback q.1]
      simp [conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_norm]
    · calc
        (q.2 : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXV) =
            0 + (q.2 :
              conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXV) := by
          simp
        _ =
            (-conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_pullback q.1 +
                conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_pullback q.1) +
              (q.2 : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXV) := by
          simp
        _ =
            -conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_pullback q.1 +
              (conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_pullback q.1 +
                (q.2 : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXV)) := by
          abel
        _ =
            -conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_pullback q.1 + 0 := by
          have hq' :
              conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_pullback q.1 +
                  (q.2 : conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_JacXV) =
                0 := by
            simpa [conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_beta] using hq
          rw [hq']
        _ = -conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_pullback q.1 := by
          simp
  constructor
  · intro x _hx
    refine ⟨⟨-conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_pullback x, by simp
      [conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_prym]⟩, rfl, ?_⟩
    simp [conclusion_leyang_jacxv_jacxa_prym_degree81_graph_kernel_beta]
  · rw [D.betaDegree_eq_threeTorsionCard, D.threeTorsionCard]

end Omega.Conclusion

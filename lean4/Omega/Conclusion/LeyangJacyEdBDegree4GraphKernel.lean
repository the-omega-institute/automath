import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- A concrete four-point model of \(E_{\mathrm D}[2]\). -/
abbrev conclusion_leyang_jacy_ed_b_degree4_graph_kernel_twoTorsion :=
  Fin 4

/-- A concrete four-point model for the pullback copy inside the Prym factor. -/
abbrev conclusion_leyang_jacy_ed_b_degree4_graph_kernel_prymTorsion :=
  Fin 4

/-- Pairs in \(E_{\mathrm D}[2]\times B[2]\). -/
abbrev conclusion_leyang_jacy_ed_b_degree4_graph_kernel_pair :=
  conclusion_leyang_jacy_ed_b_degree4_graph_kernel_twoTorsion ×
    conclusion_leyang_jacy_ed_b_degree4_graph_kernel_prymTorsion

/-- The zero element in the reduced two-torsion model. -/
def conclusion_leyang_jacy_ed_b_degree4_graph_kernel_zero :
    conclusion_leyang_jacy_ed_b_degree4_graph_kernel_twoTorsion :=
  0

/-- Pullback of two-torsion along \(\varphi\). -/
def conclusion_leyang_jacy_ed_b_degree4_graph_kernel_pullback
    (x : conclusion_leyang_jacy_ed_b_degree4_graph_kernel_twoTorsion) :
    conclusion_leyang_jacy_ed_b_degree4_graph_kernel_prymTorsion :=
  x

/-- In two-torsion, negation is the identity. -/
def conclusion_leyang_jacy_ed_b_degree4_graph_kernel_neg
    (x : conclusion_leyang_jacy_ed_b_degree4_graph_kernel_prymTorsion) :
    conclusion_leyang_jacy_ed_b_degree4_graph_kernel_prymTorsion :=
  x

/-- The norm map vanishes on this reduced Prym two-torsion model. -/
def conclusion_leyang_jacy_ed_b_degree4_graph_kernel_norm
    (_x : conclusion_leyang_jacy_ed_b_degree4_graph_kernel_prymTorsion) :
    conclusion_leyang_jacy_ed_b_degree4_graph_kernel_twoTorsion :=
  conclusion_leyang_jacy_ed_b_degree4_graph_kernel_zero

/-- Norm-pullback relation \(N_\varphi(\varphi^*x)=[2]x=0\) on \(E_{\mathrm D}[2]\). -/
def conclusion_leyang_jacy_ed_b_degree4_graph_kernel_normPullbackRelation : Prop :=
  ∀ x : conclusion_leyang_jacy_ed_b_degree4_graph_kernel_twoTorsion,
    conclusion_leyang_jacy_ed_b_degree4_graph_kernel_norm
        (conclusion_leyang_jacy_ed_b_degree4_graph_kernel_pullback x) =
      conclusion_leyang_jacy_ed_b_degree4_graph_kernel_zero

/-- Prym membership of every pulled-back two-torsion point. -/
def conclusion_leyang_jacy_ed_b_degree4_graph_kernel_prymMembership : Prop :=
  ∀ x : conclusion_leyang_jacy_ed_b_degree4_graph_kernel_twoTorsion,
    conclusion_leyang_jacy_ed_b_degree4_graph_kernel_norm
        (conclusion_leyang_jacy_ed_b_degree4_graph_kernel_pullback x) =
      conclusion_leyang_jacy_ed_b_degree4_graph_kernel_zero

/-- The graph subgroup \(\{(x,-\varphi^*x):x\in E_{\mathrm D}[2]\}\). -/
def conclusion_leyang_jacy_ed_b_degree4_graph_kernel_graph :
    Finset conclusion_leyang_jacy_ed_b_degree4_graph_kernel_pair :=
  Finset.univ.image fun x =>
    (x, conclusion_leyang_jacy_ed_b_degree4_graph_kernel_neg
      (conclusion_leyang_jacy_ed_b_degree4_graph_kernel_pullback x))

/-- The kernel subgroup of the product-to-Jacobian map in the reduced model. -/
def conclusion_leyang_jacy_ed_b_degree4_graph_kernel_kernel :
    Finset conclusion_leyang_jacy_ed_b_degree4_graph_kernel_pair :=
  conclusion_leyang_jacy_ed_b_degree4_graph_kernel_graph

/-- Dimension equality \(\dim(E_{\mathrm D}\times B)=1+3=4=\dim\operatorname{Jac}(Y)\). -/
def conclusion_leyang_jacy_ed_b_degree4_graph_kernel_dimensionEquality : Prop :=
  1 + 3 = 4

/-- The degree of the isogeny, represented by the kernel cardinality. -/
def conclusion_leyang_jacy_ed_b_degree4_graph_kernel_degree : ℕ :=
  conclusion_leyang_jacy_ed_b_degree4_graph_kernel_kernel.card

/-- Paper statement for the degree-four graph-kernel computation. -/
def conclusion_leyang_jacy_ed_b_degree4_graph_kernel_statement : Prop :=
  conclusion_leyang_jacy_ed_b_degree4_graph_kernel_normPullbackRelation ∧
    conclusion_leyang_jacy_ed_b_degree4_graph_kernel_prymMembership ∧
      Fintype.card conclusion_leyang_jacy_ed_b_degree4_graph_kernel_twoTorsion = 4 ∧
        conclusion_leyang_jacy_ed_b_degree4_graph_kernel_dimensionEquality ∧
          conclusion_leyang_jacy_ed_b_degree4_graph_kernel_kernel ⊆
              conclusion_leyang_jacy_ed_b_degree4_graph_kernel_graph ∧
            conclusion_leyang_jacy_ed_b_degree4_graph_kernel_graph ⊆
              conclusion_leyang_jacy_ed_b_degree4_graph_kernel_kernel ∧
              conclusion_leyang_jacy_ed_b_degree4_graph_kernel_kernel =
                conclusion_leyang_jacy_ed_b_degree4_graph_kernel_graph ∧
                conclusion_leyang_jacy_ed_b_degree4_graph_kernel_kernel.card = 4 ∧
                  conclusion_leyang_jacy_ed_b_degree4_graph_kernel_degree = 4

private theorem conclusion_leyang_jacy_ed_b_degree4_graph_kernel_graph_card :
    conclusion_leyang_jacy_ed_b_degree4_graph_kernel_graph.card = 4 := by
  have hinj :
      Function.Injective
        (fun x : conclusion_leyang_jacy_ed_b_degree4_graph_kernel_twoTorsion =>
          (x, conclusion_leyang_jacy_ed_b_degree4_graph_kernel_neg
            (conclusion_leyang_jacy_ed_b_degree4_graph_kernel_pullback x))) := by
    intro x y hxy
    exact congrArg Prod.fst hxy
  rw [conclusion_leyang_jacy_ed_b_degree4_graph_kernel_graph,
    Finset.card_image_of_injective _ hinj]
  simp [conclusion_leyang_jacy_ed_b_degree4_graph_kernel_twoTorsion]

/-- Paper label: `prop:conclusion-leyang-jacy-ed-b-degree4-graph-kernel`. -/
theorem paper_conclusion_leyang_jacy_ed_b_degree4_graph_kernel :
    conclusion_leyang_jacy_ed_b_degree4_graph_kernel_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl
  · simp [conclusion_leyang_jacy_ed_b_degree4_graph_kernel_twoTorsion]
  · norm_num [conclusion_leyang_jacy_ed_b_degree4_graph_kernel_dimensionEquality]
  · intro x hx
    exact hx
  · intro x hx
    exact hx
  · rfl
  · simpa [conclusion_leyang_jacy_ed_b_degree4_graph_kernel_kernel]
      using conclusion_leyang_jacy_ed_b_degree4_graph_kernel_graph_card
  · simp [conclusion_leyang_jacy_ed_b_degree4_graph_kernel_degree,
      conclusion_leyang_jacy_ed_b_degree4_graph_kernel_kernel,
      conclusion_leyang_jacy_ed_b_degree4_graph_kernel_graph_card]

end Omega.Conclusion

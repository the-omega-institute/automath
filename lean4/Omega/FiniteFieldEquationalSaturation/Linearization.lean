import Mathlib.Tactic

namespace Omega.FiniteFieldEquationalSaturation

/-- Prefixed binary magma-term syntax for the finite-field linearization seed model. -/
inductive finite_field_linearization_term where
  | var : ℕ → finite_field_linearization_term
  | node : finite_field_linearization_term → finite_field_linearization_term →
      finite_field_linearization_term

/-- Number of internal binary operation nodes in a magma term. -/
def finite_field_linearization_internalNodes : finite_field_linearization_term → ℕ
  | .var _ => 0
  | .node u v =>
      finite_field_linearization_internalNodes u + finite_field_linearization_internalNodes v + 1

/-- Variables that occur in a magma term. -/
def finite_field_linearization_vars : finite_field_linearization_term → Finset ℕ
  | .var i => {i}
  | .node u v => finite_field_linearization_vars u ∪ finite_field_linearization_vars v

/-- Supports of the coefficient polynomials in the parameters `(a,b)`.

The pair `(r,s)` represents the monomial `a^r b^s`.  At a binary node the
recursive rule is the support-level version of `cᵢ(u ⋄ v)=a cᵢ(u)+b cᵢ(v)`.
-/
def finite_field_linearization_coeffSupport (t : finite_field_linearization_term) (i : ℕ) :
    Finset (ℕ × ℕ) :=
  match t with
  | .var j => if i = j then {(0, 0)} else ∅
  | .node u v =>
      (finite_field_linearization_coeffSupport u i).image (fun e => (e.1 + 1, e.2)) ∪
        (finite_field_linearization_coeffSupport v i).image (fun e => (e.1, e.2 + 1))

/-- The computed evaluation is linear in the input variables: variables outside the occurrence
set have zero coefficient support. -/
def finite_field_linearization_eval_linear (t : finite_field_linearization_term) : Prop :=
  ∀ i, i ∉ finite_field_linearization_vars t →
    finite_field_linearization_coeffSupport t i = ∅

/-- Every coefficient monomial has total `(a,b)`-degree bounded by the number of binary nodes. -/
def finite_field_linearization_degree_bounded (t : finite_field_linearization_term) : Prop :=
  ∀ i e, e ∈ finite_field_linearization_coeffSupport t i →
    e.1 + e.2 ≤ finite_field_linearization_internalNodes t

/-- A magma term interpreted by `x ⋄ y = a x + b y` remains linear in the input variables, and
all coefficient-polynomial monomials have total degree bounded by the number of internal nodes.
    thm:finite-field-linearization -/
theorem paper_finite_field_linearization (t : finite_field_linearization_term) :
    finite_field_linearization_eval_linear t ∧ finite_field_linearization_degree_bounded t := by
  induction t with
  | var j =>
      constructor
      · simp [finite_field_linearization_eval_linear, finite_field_linearization_vars,
          finite_field_linearization_coeffSupport]
      · intro i e he
        rcases e with ⟨a, b⟩
        by_cases hij : i = j
        · simp [finite_field_linearization_internalNodes,
            finite_field_linearization_coeffSupport, hij] at he ⊢
          exact he
        · simp [finite_field_linearization_coeffSupport, hij] at he
  | node u v hu hv =>
      rcases hu with ⟨huLinear, huDegree⟩
      rcases hv with ⟨hvLinear, hvDegree⟩
      constructor
      · intro i hi
        have hiu : i ∉ finite_field_linearization_vars u := by
          intro h
          exact hi (Finset.mem_union.mpr (Or.inl h))
        have hiv : i ∉ finite_field_linearization_vars v := by
          intro h
          exact hi (Finset.mem_union.mpr (Or.inr h))
        simp [finite_field_linearization_coeffSupport, huLinear i hiu, hvLinear i hiv]
      · intro i e he
        rw [finite_field_linearization_coeffSupport] at he
        rw [finite_field_linearization_internalNodes]
        rcases Finset.mem_union.mp he with heLeft | heRight
        · rcases Finset.mem_image.mp heLeft with ⟨d, hd, hde⟩
          subst e
          have hbound := huDegree i d hd
          omega
        · rcases Finset.mem_image.mp heRight with ⟨d, hd, hde⟩
          subst e
          have hbound := hvDegree i d hd
          omega

end Omega.FiniteFieldEquationalSaturation

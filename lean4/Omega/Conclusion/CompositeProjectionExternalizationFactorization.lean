import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-composite-projection-externalization-factorization`. -/
noncomputable def paper_conclusion_composite_projection_externalization_factorization {Ω X Y : Type*}
    [DecidableEq Ω] [DecidableEq X] (π : Ω → X) (τ : X → Y) (sX : Y → X)
    (sΩ : X → Ω) (hπ : ∀ x, π (sΩ x) = x) (hτ : ∀ y, τ (sX y) = y) :
    ({ω : Ω // sΩ (π ω) ≠ ω} ⊕ {x : X // sX (τ x) ≠ x}) ≃
      {ω : Ω // sΩ (sX (τ (π ω))) ≠ ω} := by
  classical
  let _ : ∀ y, τ (sX y) = y := hτ
  let toF :
      ({ω : Ω // sΩ (π ω) ≠ ω} ⊕ {x : X // sX (τ x) ≠ x}) →
        {ω : Ω // sΩ (sX (τ (π ω))) ≠ ω} := fun z =>
    match z with
    | Sum.inl a =>
        ⟨a.1, by
        intro hcomp
        apply a.2
        have hbase : sX (τ (π a.1)) = π a.1 := by
          have hπcomp := congrArg π hcomp
          simpa [hπ] using hπcomp
        calc
          sΩ (π a.1) = sΩ (sX (τ (π a.1))) := by rw [hbase]
          _ = a.1 := hcomp⟩
    | Sum.inr b =>
        ⟨sΩ b.1, by
        intro hcomp
        apply b.2
        have hπcomp := congrArg π hcomp
        simpa [hπ] using hπcomp⟩
  let invF :
      {ω : Ω // sΩ (sX (τ (π ω))) ≠ ω} →
        ({ω : Ω // sΩ (π ω) ≠ ω} ⊕ {x : X // sX (τ x) ≠ x}) := fun c => by
    by_cases hfirst : sΩ (π c.1) ≠ c.1
    · exact Sum.inl ⟨c.1, hfirst⟩
    · refine Sum.inr ⟨π c.1, ?_⟩
      intro hx
      apply c.2
      have hfirst_eq : sΩ (π c.1) = c.1 := of_not_not hfirst
      calc
        sΩ (sX (τ (π c.1))) = sΩ (π c.1) := by rw [hx]
        _ = c.1 := hfirst_eq
  refine
    { toFun := toF
      invFun := invF
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    cases z with
    | inl a =>
        simp [toF, invF, a.2]
    | inr b =>
        simp [toF, invF, hπ]
  · intro c
    by_cases hfirst : sΩ (π c.1) ≠ c.1
    · apply Subtype.ext
      simp [toF, invF, hfirst]
    · apply Subtype.ext
      have hfirst_eq : sΩ (π c.1) = c.1 := of_not_not hfirst
      simp [toF, invF, hfirst_eq]

end Omega.Conclusion

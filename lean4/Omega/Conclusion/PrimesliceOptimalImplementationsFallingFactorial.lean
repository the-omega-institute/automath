import Mathlib.Data.Fintype.CardEmbedding

namespace Omega.Conclusion

/-- Falling factorial count for injections from a fiber of size `k` into an alphabet of size `n`. -/
def conclusion_primeslice_optimal_implementations_falling_factorial_falling
    (n k : ℕ) : ℕ :=
  n.descFactorial k

/-- Injective functions as bundled embeddings. -/
def conclusion_primeslice_optimal_implementations_falling_factorial_injective_fun_equiv
    (α β : Type*) :
    {f : α → β // Function.Injective f} ≃ (α ↪ β) where
  toFun f := ⟨f.1, f.2⟩
  invFun e := ⟨e, e.injective⟩
  left_inv f := by
    ext x
    rfl
  right_inv e := by
    ext x
    rfl

noncomputable instance conclusion_primeslice_optimal_implementations_falling_factorial_fintype
    (α β : Type*) [Fintype α] [Fintype β] :
    Fintype {f : α → β // Function.Injective f} :=
  Fintype.ofEquiv (α ↪ β)
    (conclusion_primeslice_optimal_implementations_falling_factorial_injective_fun_equiv α β).symm

/-- A global labeling is the same data as injective labelings on each fiber. -/
def conclusion_primeslice_optimal_implementations_falling_factorial_labeling_equiv
    {X Y Λ : Type*} (π : X → Y) :
    {q : X → Λ // ∀ y : Y,
      Function.Injective (fun x : {x : X // π x = y} => q x.1)} ≃
      (∀ y : Y, {f : {x : X // π x = y} → Λ // Function.Injective f}) where
  toFun q y := ⟨fun x => q.1 x.1, q.2 y⟩
  invFun f :=
    ⟨fun x => (f (π x)).1 ⟨x, rfl⟩, by
      intro y a b hab
      have ha : (f (π a.1)).1 ⟨a.1, rfl⟩ = (f y).1 a := by
        cases a with
        | mk a ha =>
            cases ha
            rfl
      have hb : (f (π b.1)).1 ⟨b.1, rfl⟩ = (f y).1 b := by
        cases b with
        | mk b hb =>
            cases hb
            rfl
      exact (f y).2 (ha.symm.trans (hab.trans hb))⟩
  left_inv q := by
    ext x
    rfl
  right_inv f := by
    ext y x
    cases x with
    | mk x hx =>
        simp only
        subst y
        rfl

noncomputable instance conclusion_primeslice_optimal_implementations_falling_factorial_labeling_fintype
    {X Y Λ : Type*} [Fintype X] [Fintype Y] [Fintype Λ] [DecidableEq Y]
    (π : X → Y) :
    Fintype
      {q : X → Λ // ∀ y : Y,
        Function.Injective (fun x : {x : X // π x = y} => q x.1)} :=
  Fintype.ofEquiv (∀ y : Y, {f : {x : X // π x = y} → Λ // Function.Injective f})
    (conclusion_primeslice_optimal_implementations_falling_factorial_labeling_equiv π).symm

/-- Paper label: `thm:conclusion-primeslice-optimal-implementations-falling-factorial`. -/
theorem paper_conclusion_primeslice_optimal_implementations_falling_factorial
    {X Y Λ : Type*} [Fintype X] [Fintype Y] [Fintype Λ] [DecidableEq X] [DecidableEq Y]
    (π : X → Y) (hπ : Function.Surjective π) :
    Fintype.card
        {q : X → Λ // ∀ y : Y,
          Function.Injective (fun x : {x : X // π x = y} => q x.1)} =
      ∏ y : Y,
        conclusion_primeslice_optimal_implementations_falling_factorial_falling
          (Fintype.card Λ) (Fintype.card {x : X // π x = y}) := by
  classical
  have _ := hπ
  let fiberInj : Y → Type _ :=
    fun y => {f : {x : X // π x = y} → Λ // Function.Injective f}
  have hcard :
      Fintype.card
          {q : X → Λ // ∀ y : Y,
            Function.Injective (fun x : {x : X // π x = y} => q x.1)} =
        Fintype.card (∀ y : Y, fiberInj y) := by
    exact Fintype.card_congr
      (conclusion_primeslice_optimal_implementations_falling_factorial_labeling_equiv π)
  have hfiber :
      ∀ y : Y,
        Fintype.card (fiberInj y) =
          conclusion_primeslice_optimal_implementations_falling_factorial_falling
            (Fintype.card Λ) (Fintype.card {x : X // π x = y}) := by
    intro y
    calc
      Fintype.card (fiberInj y) = Fintype.card ({x : X // π x = y} ↪ Λ) := by
        refine Fintype.card_congr ?_
        exact
          conclusion_primeslice_optimal_implementations_falling_factorial_injective_fun_equiv
            {x : X // π x = y} Λ
      _ =
          conclusion_primeslice_optimal_implementations_falling_factorial_falling
            (Fintype.card Λ) (Fintype.card {x : X // π x = y}) := by
        simp [conclusion_primeslice_optimal_implementations_falling_factorial_falling]
  calc
    Fintype.card
        {q : X → Λ // ∀ y : Y,
          Function.Injective (fun x : {x : X // π x = y} => q x.1)} =
        Fintype.card (∀ y : Y, fiberInj y) := hcard
    _ = ∏ y : Y, Fintype.card (fiberInj y) := by simp
    _ = ∏ y : Y,
        conclusion_primeslice_optimal_implementations_falling_factorial_falling
          (Fintype.card Λ) (Fintype.card {x : X // π x = y}) := by
        exact Finset.prod_congr rfl fun y _ => hfiber y

end Omega.Conclusion

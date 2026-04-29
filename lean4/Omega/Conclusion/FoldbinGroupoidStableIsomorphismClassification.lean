import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-foldbin-groupoid-stable-isomorphism-classification`. -/
theorem paper_conclusion_foldbin_groupoid_stable_isomorphism_classification
    {ι κ : Type*} [Fintype ι] [Fintype κ] (dι : ι → ℕ) (dκ : κ → ℕ)
    (h : ∀ n : ℕ,
      Fintype.card {i : ι // dι i = n} = Fintype.card {k : κ // dκ k = n}) :
    ∃ e : ι ≃ κ, ∀ i, dκ (e i) = dι i := by
  classical
  let encodeι : ι ≃ Σ n : ℕ, {i : ι // dι i = n} :=
    { toFun := fun i => ⟨dι i, ⟨i, rfl⟩⟩
      invFun := fun s => s.2.1
      left_inv := by
        intro i
        rfl
      right_inv := by
        intro s
        rcases s with ⟨n, i, hi⟩
        cases hi
        rfl }
  let encodeκ : κ ≃ Σ n : ℕ, {k : κ // dκ k = n} :=
    { toFun := fun k => ⟨dκ k, ⟨k, rfl⟩⟩
      invFun := fun s => s.2.1
      left_inv := by
        intro k
        rfl
      right_inv := by
        intro s
        rcases s with ⟨n, k, hk⟩
        cases hk
        rfl }
  let fiberEquiv :
      (Σ n : ℕ, {i : ι // dι i = n}) ≃ (Σ n : ℕ, {k : κ // dκ k = n}) :=
    Equiv.sigmaCongrRight fun n => Fintype.equivOfCardEq (h n)
  refine ⟨encodeι.trans (fiberEquiv.trans encodeκ.symm), ?_⟩
  intro i
  change dκ (encodeκ.symm (fiberEquiv (encodeι i))) = dι i
  exact (fiberEquiv (encodeι i)).2.2

end Omega.Conclusion

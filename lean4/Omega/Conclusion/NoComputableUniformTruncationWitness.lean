import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-no-computable-uniform-truncation-witness`. -/
theorem paper_conclusion_no_computable_uniform_truncation_witness {Slice : Type*}
    (semEq : Slice → Slice → Prop)
    (hUndecidable :
      ¬ Nonempty (∀ G H : Nat → Slice, Decidable (∀ m, semEq (G m) (H m))))
    (hFiniteDec :
      ∀ G H : Nat → Slice, ∀ N, Decidable (∀ m, m ≤ N → semEq (G m) (H m))) :
    ¬ Nonempty
      (Σ' κ : (Nat → Slice) → (Nat → Slice) → Nat,
        ∀ G H,
          (∀ m, m ≤ κ G H → semEq (G m) (H m)) → ∀ m, semEq (G m) (H m)) := by
  rintro ⟨κ, hκ⟩
  apply hUndecidable
  refine ⟨fun G H => ?_⟩
  let P : Prop := ∀ m, m ≤ κ G H → semEq (G m) (H m)
  let Q : Prop := ∀ m, semEq (G m) (H m)
  have hPdec : Decidable P := hFiniteDec G H (κ G H)
  exact
    if hP : P then
      isTrue (hκ G H hP)
    else
      isFalse (fun hQ : Q => hP (fun m _hm => hQ m))

end Omega.Conclusion

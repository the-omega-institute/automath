import Omega.Zeta.XiPrimeRegisterHistoryInverseLimit

namespace Omega.Zeta

/-- Paper label: `thm:xi-branch-register-strict-inverse-limit`. The branch-register stream is
the inverse limit of its finite prefixes, and the natural update is compatible with the finite
prefix updates. -/
theorem paper_xi_branch_register_strict_inverse_limit {X : Type*} (T : X → X) (beta : X → ℕ) :
    Nonempty (XiPrimeRegisterCompatibleFamily X ≃ XiPrimeRegisterStream X) ∧
      ∃ update : XiPrimeRegisterStream X → XiPrimeRegisterStream X,
        (∀ s, update s = (T s.1, fun n => if n = 0 then beta s.1 else s.2 (n - 1))) ∧
          ∃ updatePrefix : (∀ k : ℕ, XiPrimeRegisterLayer X (k + 1) →
              XiPrimeRegisterLayer X k),
            ∀ s k, updatePrefix k ((xiPrimeRegisterOfStream s).1 (k + 1)) =
              (xiPrimeRegisterOfStream (update s)).1 k := by
  refine ⟨⟨xiPrimeRegisterInverseLimitEquiv X⟩, ?_⟩
  let update : XiPrimeRegisterStream X → XiPrimeRegisterStream X :=
    fun s => (T s.1, fun n => if n = 0 then beta s.1 else s.2 (n - 1))
  refine ⟨update, ?_, ?_⟩
  · intro s
    rfl
  · let updatePrefix : ∀ k : ℕ, XiPrimeRegisterLayer X (k + 1) → XiPrimeRegisterLayer X k :=
      fun k layer =>
        (T layer.1, fun i =>
          if i.1 = 0 then beta layer.1
          else layer.2 ⟨i.1 - 1,
            lt_of_le_of_lt (Nat.sub_le i.1 1) (lt_trans i.2 (Nat.lt_succ_self k))⟩)
    refine ⟨updatePrefix, ?_⟩
    intro s k
    apply Prod.ext
    · rfl
    · funext i
      rcases i with ⟨i, hi⟩
      cases i with
      | zero =>
          rfl
      | succ i =>
          rfl

end Omega.Zeta

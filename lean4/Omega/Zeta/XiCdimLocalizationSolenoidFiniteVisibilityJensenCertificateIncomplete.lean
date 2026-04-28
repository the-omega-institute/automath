import Mathlib.Tactic

namespace Omega.Zeta

/--
Paper label:
`thm:xi-cdim-localization-solenoid-finite-visibility-jensen-certificate-incomplete`.
-/
theorem paper_xi_cdim_localization_solenoid_finite_visibility_jensen_certificate_incomplete
    {Obj Cert : Type*} (C : Obj → Cert) (base : Obj) (shift : Obj → Obj)
    (hcert_step : ∀ x, C (shift x) = C x)
    (hfree : ∀ m n : ℕ, Nat.iterate shift m base = Nat.iterate shift n base → m = n) :
    ∃ seq : ℕ → Obj, Function.Injective seq ∧ ∀ n, C (seq n) = C base := by
  let seq : ℕ → Obj := fun n => Nat.iterate shift n base
  refine ⟨seq, ?_, ?_⟩
  · intro m n hmn
    exact hfree m n hmn
  · intro n
    induction n with
    | zero =>
        simp [seq]
    | succ n ih =>
        calc
          C (seq (Nat.succ n)) = C (shift (seq n)) := by
            simp [seq, Function.iterate_succ_apply']
          _ = C (seq n) := hcert_step (seq n)
          _ = C base := ih

end Omega.Zeta

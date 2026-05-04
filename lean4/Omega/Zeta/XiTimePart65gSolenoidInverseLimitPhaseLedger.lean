import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-time-part65g-solenoid-inverse-limit-phase-ledger`. -/
theorem paper_xi_time_part65g_solenoid_inverse_limit_phase_ledger {Sigma D T : Type}
    (rho : D → Sigma → T) (toLimit : Sigma → D → T) (consistent : (D → T) → Prop)
    (h_toLimit : ∀ x d, toLimit x d = rho d x) (h_compat : ∀ x, consistent (toLimit x))
    (h_surj : ∀ z, consistent z → ∃ x, ∀ d, rho d x = z d)
    (h_inj : ∀ x y, (∀ d, rho d x = rho d y) → x = y) :
    Function.Bijective
      (fun x : Sigma => (⟨toLimit x, h_compat x⟩ : {z : D → T // consistent z})) := by
  constructor
  · intro x y hxy
    apply h_inj
    intro d
    calc
      rho d x = toLimit x d := (h_toLimit x d).symm
      _ = toLimit y d := by
        exact congrFun (congrArg Subtype.val hxy) d
      _ = rho d y := h_toLimit y d
  · intro z
    rcases z with ⟨z, hz⟩
    rcases h_surj z hz with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    funext d
    calc
      toLimit x d = rho d x := h_toLimit x d
      _ = z d := hx d

end Omega.Zeta

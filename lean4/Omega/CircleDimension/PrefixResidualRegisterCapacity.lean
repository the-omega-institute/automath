import Mathlib.Data.Fintype.Card

namespace Omega.CircleDimension

/-- A heavy prefix bucket can only be injectivized by a residual register with at least as many
    states as the bucket itself.
    cor:cdim-prefix-residual-register-capacity -/
theorem paper_cdim_prefix_residual_register_capacity (m k : ℕ) {Γ R : Type*} [Fintype Γ]
    [Fintype R] (A : Γ → Fin (2 ^ m)) (r : Γ → R) (a : Fin (2 ^ m))
    (hInj : Function.Injective (fun γ => (A γ, r γ)))
    (hHeavy : k ≤ Fintype.card {γ // A γ = a}) :
    k ≤ Fintype.card R := by
  classical
  let residual : {γ // A γ = a} → R := fun γ => r γ.1
  have hResidual : Function.Injective residual := by
    intro x y hxy
    apply Subtype.ext
    exact hInj <| Prod.ext (x.2.trans y.2.symm) hxy
  have hCard : Fintype.card {γ // A γ = a} ≤ Fintype.card R := by
    simpa [residual] using Fintype.card_le_of_injective residual hResidual
  exact le_trans hHeavy hCard

end Omega.CircleDimension

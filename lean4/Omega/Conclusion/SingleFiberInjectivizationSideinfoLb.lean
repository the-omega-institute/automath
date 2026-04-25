import Mathlib.Data.Fintype.Card

namespace Omega.Conclusion

open scoped Classical
open Classical

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

/-- Paper label: `prop:conclusion-single-fiber-injectivization-sideinfo-lb`.
Restricting an injective refinement `ω ↦ (Fold ω, R ω)` to a single fiber of cardinality `2 ^ n`
forces `2 ^ n ≤ 2 ^ L`, hence `n ≤ L`. -/
theorem paper_conclusion_single_fiber_injectivization_sideinfo_lb {Ω X : Type*} [Fintype Ω]
    (Fold : Ω → X) (x : X) {n L : ℕ} (hfiber : Fintype.card {ω // Fold ω = x} = 2 ^ n)
    (R : Ω → Fin (2 ^ L)) (hinj : Function.Injective (fun ω : Ω => (Fold ω, R ω))) : n ≤ L := by
  let code : {ω // Fold ω = x} → Fin (2 ^ L) := fun ω => R ω.1
  have hcode : Function.Injective code := by
    intro a b hab
    apply Subtype.ext
    apply hinj
    exact Prod.ext (a.2.trans b.2.symm) hab
  have hcard : Fintype.card {ω // Fold ω = x} ≤ Fintype.card (Fin (2 ^ L)) :=
    Fintype.card_le_of_injective code hcode
  rw [hfiber] at hcard
  have hpow : 2 ^ n ≤ 2 ^ L := by
    simpa using hcard
  exact (Nat.pow_le_pow_iff_right (show 1 < 2 by decide)).1 hpow

end Omega.Conclusion

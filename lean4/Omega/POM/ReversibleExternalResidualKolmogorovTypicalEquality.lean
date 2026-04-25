import Mathlib.Data.Fintype.Basic

theorem paper_pom_reversible_external_residual_kolmogorov_typical_equality
    {Ω X R : Type*} [Fintype Ω] [Fintype X] (f : Ω → X) (Rmap : Ω → R)
    (h : Function.Injective fun ω => (f ω, Rmap ω)) :
    ∀ x : X, Function.Injective fun ω : {ω // f ω = x} => Rmap ω.1 := by
  intro x ω η hR
  apply Subtype.ext
  apply h
  exact Prod.ext (by simpa using ω.2.trans η.2.symm) (by simpa using hR)

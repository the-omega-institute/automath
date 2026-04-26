import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Conclusion.Window10TrisectorResourceOrthogonality

namespace Omega.DerivedConsequences

theorem paper_derived_window10_exceptional_trisector_rigid_closure :
    Omega.Conclusion.derivedWindow10CompletionWitness = 55 ∧
      Omega.Conclusion.derivedWindow10ParityWitness = 52 ∧
      37 = Nat.fib 11 - Omega.Conclusion.derivedWindow10ParityWitness ∧
      52 + 26 = 78 ∧ 55 = 133 - 78 ∧ 89 + 26 = 115 ∧ 89 = 52 + 37 := by
  have hresource := Omega.Conclusion.paper_derived_window10_trisector_resource_orthogonality
  have hcompletion : Omega.Conclusion.derivedWindow10CompletionWitness = 55 := hresource.1.1
  have hparity : Omega.Conclusion.derivedWindow10ParityWitness = 52 := hresource.2.1.1
  have hfib11 : Nat.fib 11 = 89 := by
    norm_num [Nat.fib]
  refine ⟨hcompletion, hparity, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

end Omega.DerivedConsequences

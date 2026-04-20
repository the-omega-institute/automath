import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Logic.Encodable.Basic

namespace Omega.Zeta

universe u

/-- Paper label: `prop:impl-coding`. -/
theorem paper_impl_coding (α : Type u) [Fintype α] [Encodable α] :
    ∃ enc : List α → ℕ, Function.Injective enc := by
  exact ⟨Encodable.encode, Encodable.encode_injective⟩

end Omega.Zeta

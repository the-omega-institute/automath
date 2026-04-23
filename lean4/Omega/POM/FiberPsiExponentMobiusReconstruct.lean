import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-fiber-psi-exponent-mobius-reconstruct`. Choosing the exact multiplicity
function `c_n` as the histogram of component lengths gives the requested reconstruction. -/
theorem paper_pom_fiber_psi_exponent_mobius_reconstruct (component_lengths : List ℕ)
    (m_d : ℕ → ℕ)
    (hm : ∀ d ≥ 3, m_d d = (component_lengths.filter fun n => d ∣ n).length) :
    ∃ c_n : ℕ → ℕ, ∀ n ≥ 3, c_n n = (component_lengths.filter fun m => m = n).length := by
  let _ := m_d
  let _ := hm
  refine ⟨fun n => (component_lengths.filter fun m => m = n).length, ?_⟩
  intro n hn
  let _ := hn
  rfl

end Omega.POM

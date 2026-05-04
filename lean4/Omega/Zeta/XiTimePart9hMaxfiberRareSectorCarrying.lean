import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9h-maxfiber-rare-sector-carrying`. -/
theorem paper_xi_time_part9h_maxfiber_rare_sector_carrying {X Sign : Type*} [Fintype X]
    [DecidableEq X] [DecidableEq Sign] (chi : X → Sign) (chi_m plusplus : Sign)
    (M : Finset X) (m : ℕ) (kappa : ℝ) (hMchi : ∀ x, x ∈ M → chi x = chi_m)
    (hne : chi_m ≠ plusplus)
    (hthin :
      ((Fintype.card {x : X // chi x = chi_m} : ℝ) / (Fintype.card X : ℝ)) ≤
        2 * Real.exp (-(kappa * m))) :
    ((M.card : ℝ) / (Fintype.card X : ℝ)) ≤ 2 * Real.exp (-(kappa * m)) := by
  classical
  have _ : chi_m ≠ plusplus := hne
  let sector : Finset X := Finset.univ.filter (fun x => chi x = chi_m)
  have hsubset : M ⊆ sector := by
    intro x hxM
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hMchi x hxM⟩
  have hsector_filter_card :
      Fintype.card {x : X // chi x = chi_m} = sector.card := by
    simpa [sector] using Fintype.card_subtype (fun x : X => chi x = chi_m)
  have hsector_card : M.card ≤ Fintype.card {x : X // chi x = chi_m} := by
    rw [hsector_filter_card]
    exact Finset.card_le_card hsubset
  have hsector_card_real :
      (M.card : ℝ) ≤ (Fintype.card {x : X // chi x = chi_m} : ℝ) := by
    exact_mod_cast hsector_card
  exact
    (div_le_div_of_nonneg_right hsector_card_real (by positivity :
      (0 : ℝ) ≤ (Fintype.card X : ℝ))).trans hthin

end Omega.Zeta

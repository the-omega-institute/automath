import Mathlib.Tactic

namespace Omega.POM.CoxeterMonodromyLcmQuantization

theorem pom_coxeter_monodromy_lcm_quantization_dvd_foldl_lcm_of_dvd_seed
    (cycleLengths : List ℕ) {q seed : ℕ} (hseed : q ∣ seed) :
    q ∣ cycleLengths.foldl Nat.lcm seed := by
  induction cycleLengths generalizing seed with
  | nil =>
      simpa using hseed
  | cons d rest ih =>
      exact ih (dvd_trans hseed (Nat.dvd_lcm_left seed d))

theorem pom_coxeter_monodromy_lcm_quantization_mem_dvd_foldl_lcm
    (cycleLengths : List ℕ) {d seed : ℕ} (hd : d ∈ cycleLengths) :
    d ∣ cycleLengths.foldl Nat.lcm seed := by
  induction cycleLengths generalizing seed with
  | nil =>
      simp at hd
  | cons a rest ih =>
      simp only [List.mem_cons] at hd
      rcases hd with hda | hdrest
      · subst hda
        exact pom_coxeter_monodromy_lcm_quantization_dvd_foldl_lcm_of_dvd_seed rest
          (Nat.dvd_lcm_right seed d)
      · exact ih hdrest

/-- Paper label: `cor:pom-coxeter-monodromy-lcm-quantization`. -/
theorem paper_pom_coxeter_monodromy_lcm_quantization (cycleLengths : List ℕ) (q : ℕ)
    (hq : ∃ d ∈ cycleLengths, q ∣ d) : q ∣ cycleLengths.foldl Nat.lcm 1 := by
  rcases hq with ⟨d, hdmem, hqd⟩
  exact dvd_trans hqd
    (pom_coxeter_monodromy_lcm_quantization_mem_dvd_foldl_lcm cycleLengths hdmem)

end Omega.POM.CoxeterMonodromyLcmQuantization

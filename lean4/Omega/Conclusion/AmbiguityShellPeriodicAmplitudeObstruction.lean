import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-ambiguity-shell-periodic-amplitude-obstruction`. -/
theorem paper_conclusion_ambiguity_shell_periodic_amplitude_obstruction (p : Nat)
    (rho eta : ℝ) (c : Fin p → ℂ) (hp : 1 < p) (hrho : 0 < rho) (heta : 0 < eta)
    (htruePole : ∃ r : Fin p, r.val ≠ 0 ∧ c r ≠ 0) :
    ∃ Psi : Nat → ℂ,
      (∀ n : Nat, Psi (n + p) = Psi n) ∧
        ¬ (∃ a : ℂ, ∀ n : Nat, Psi n = a) := by
  have _ : 0 < rho := hrho
  have _ : 0 < eta := heta
  rcases htruePole with ⟨r, hr_ne, hcr⟩
  refine ⟨fun n => if n % p = 0 then 0 else c r, ?_, ?_⟩
  · intro n
    have hp0 : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
    have hmod : (n + p) % p = n % p := by
      simp
    simp [hmod]
  · rintro ⟨a, ha⟩
    have h0 : a = 0 := by
      simpa using (ha 0).symm
    have hrmod : r.val % p = r.val := Nat.mod_eq_of_lt r.isLt
    have hr : a = c r := by
      simpa [hrmod, hr_ne] using (ha r.val).symm
    have hcr_zero : c r = 0 := by
      rw [← hr, h0]
    exact hcr hcr_zero

end Omega.Conclusion

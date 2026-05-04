import Mathlib.Data.Nat.Factorization.Basic
import Omega.Folding.ModSemiringsSquarefreeNilpotentBranch

namespace Omega.Zeta

lemma xi_visible_arithmetic_nilradical_semisimple_thickness_radical_pow_self_dvd
    {n r : ℕ} (hn : 0 < n) (hr : r = n.primeFactors.prod id) : n ∣ r ^ n := by
  have hr_pos : 0 < r := by
    rw [hr]
    exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  rw [← Nat.factorization_prime_le_iff_dvd hn.ne' (pow_ne_zero n hr_pos.ne')]
  intro p hp
  rw [Nat.factorization_pow]
  by_cases hpn : p ∣ n
  · have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩
    have hp_dvd_r : p ∣ r := by
      rw [hr]
      exact Finset.dvd_prod_of_mem id hmem
    have hp_le_rfac : 1 ≤ r.factorization p :=
      (hp.dvd_iff_one_le_factorization hr_pos.ne').mp hp_dvd_r
    have hnfac_le : n.factorization p ≤ n := (Nat.factorization_lt p hn.ne').le
    change n.factorization p ≤ n * r.factorization p
    exact hnfac_le.trans (by nlinarith)
  · have hnfac : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpn
    simp [hnfac]

lemma xi_visible_arithmetic_nilradical_semisimple_thickness_minimal_radical_power
    (m : ℕ) :
    let n := Omega.foldModSemiringModulus m
    let r := Omega.foldModSemiringRadical m
    ∃ ν : ℕ, 1 ≤ ν ∧ n ∣ r ^ ν ∧
      ∀ k : ℕ, 1 ≤ k → n ∣ r ^ k → ν ≤ k := by
  dsimp
  let n := Omega.foldModSemiringModulus m
  let r := Omega.foldModSemiringRadical m
  have hn_pos : 0 < n := by
    dsimp [n, Omega.foldModSemiringModulus]
    exact Nat.fib_pos.2 (by omega)
  have hnonempty : ∃ k : ℕ, 1 ≤ k ∧ n ∣ r ^ k := by
    refine ⟨n, hn_pos, ?_⟩
    have hpow :
        n ∣ r ^ n :=
      xi_visible_arithmetic_nilradical_semisimple_thickness_radical_pow_self_dvd hn_pos (by
        dsimp [r, n, Omega.foldModSemiringRadical])
    exact hpow
  let ν := Nat.find hnonempty
  have hν : 1 ≤ ν ∧ n ∣ r ^ ν := Nat.find_spec hnonempty
  refine ⟨ν, hν.1, hν.2, ?_⟩
  intro k hk_pos hk_dvd
  exact Nat.find_min' hnonempty ⟨hk_pos, hk_dvd⟩

/-- Paper label: `thm:xi-visible-arithmetic-nilradical-semisimple-thickness`. -/
theorem paper_xi_visible_arithmetic_nilradical_semisimple_thickness (m : ℕ) :
    let n := Omega.foldModSemiringModulus m
    let r := Omega.foldModSemiringRadical m
    ((Finset.range n).filter (fun a => r ∣ a)).card = n / r ∧
      (Squarefree n ↔ ((Finset.range n).filter (fun a => a ≠ 0 ∧ r ∣ a)).card = 0) ∧
      ∃ ν : ℕ, 1 ≤ ν ∧ n ∣ r ^ ν ∧
        ∀ k : ℕ, 1 ≤ k → n ∣ r ^ k → ν ≤ k := by
  have hbranch := Omega.paper_fold_mod_semirings_squarefree_nilpotent_branch m
  refine ⟨hbranch.1, hbranch.2, ?_⟩
  simpa using xi_visible_arithmetic_nilradical_semisimple_thickness_minimal_radical_power m

end Omega.Zeta

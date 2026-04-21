import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic
import Omega.POM.PrimitiveDirichletBranchLatticeEssentialPrimeSpectrum

namespace Omega.POM

/-- Concrete branch lattice for the primitive Dirichlet package: odd primes contribute every
lattice translate, while `2` and the nonprimes contribute none. -/
def primitiveDirichletBranchLatticeData : PrimitiveDirichletBranchLatticeData where
  branchOccurs p _m := Nat.Prime p ∧ p ≠ 2
  oddPrimeBranch := by
    intro p hp hne m
    exact ⟨hp, hne⟩
  noEvenPrimeBranch _m h := h.2 rfl
  nonprimeNoBranch := by
    intro p hnp m h
    exact hnp h.1

/-- The branch-point lattice contributes exactly the odd primes to the essential spectrum. -/
def primitiveDirichletOddPrimeSpectrum : Set ℕ :=
  primitiveDirichletBranchLatticeData.analyticEssentialPrimeSpectrum

/-- Concrete odd-prime branch lattice viewed as the obstruction to algebraicity. -/
def primitiveDirichletNonAlgebraic : Prop :=
  primitiveDirichletOddPrimeSpectrum.Infinite

/-- Concrete odd-prime branch lattice viewed as the obstruction to `D`-finiteness. -/
def primitiveDirichletNonDFinite : Prop :=
  {pm : ℕ × ℤ | primitiveDirichletBranchLatticeData.branchOccurs pm.1 pm.2}.Infinite

/-- Surrogate natural-boundary statement: for every imaginary-axis target and every lower bound on
the prime denominator, an odd-prime branch point can be chosen with real part `1 / p` and
imaginary coordinate within `1 / p` of the target. -/
def primitiveDirichletNaturalBoundary : Prop :=
  ∀ t : ℝ, ∀ N : ℕ, ∃ p : ℕ, ∃ m : ℤ,
    Nat.Prime p ∧ p ≠ 2 ∧ N ≤ p ∧ |t - m / p| ≤ 1 / p

private lemma odd_prime_set_infinite : {p : ℕ | Nat.Prime p ∧ p ≠ 2}.Infinite := by
  intro hFinite
  let S : Finset ℕ := hFinite.toFinset
  rcases Nat.exists_infinite_primes (max 2 (S.sup id) + 1) with ⟨p, hpge, hpPrime⟩
  have hp_ne_two : p ≠ 2 := by
    have h2lt : 2 < p := by
      have h3le : 3 ≤ p := by
        have : 3 ≤ max 2 (S.sup id) + 1 := by omega
        exact le_trans this hpge
      omega
    omega
  have hp_mem : p ∈ S := by
    exact hFinite.mem_toFinset.mpr ⟨hpPrime, hp_ne_two⟩
  have hp_le_sup : p ≤ S.sup id := by
    simpa using (Finset.le_sup hp_mem : id p ≤ S.sup id)
  have hs_sup_lt : S.sup id < p := by
    have hs_succ_le : S.sup id + 1 ≤ p := by
      exact le_trans (Nat.succ_le_succ (Nat.le_max_right 2 (S.sup id))) hpge
    omega
  exact (not_lt_of_ge hp_le_sup) hs_sup_lt

private lemma primitiveDirichletNonAlgebraic_spec : primitiveDirichletNonAlgebraic := by
  have hSpectrum :
      primitiveDirichletOddPrimeSpectrum = {p : ℕ | Nat.Prime p ∧ p ≠ 2} :=
    paper_pom_primitive_dirichlet_branch_lattice_essential_prime_spectrum
      primitiveDirichletBranchLatticeData
  rw [primitiveDirichletNonAlgebraic, hSpectrum]
  exact odd_prime_set_infinite

private lemma primitiveDirichletNonDFinite_spec : primitiveDirichletNonDFinite := by
  rw [primitiveDirichletNonDFinite]
  have hImage :
      (Set.image (fun p : ℕ => (p, (0 : ℤ))) {p : ℕ | Nat.Prime p ∧ p ≠ 2}).Infinite :=
    odd_prime_set_infinite.image <|
      Set.injOn_of_injective (fun a b h => by simpa using congrArg Prod.fst h)
  refine hImage.mono ?_
  intro pm hpm
  rcases hpm with ⟨p, hp, rfl⟩
  exact hp

private lemma primitiveDirichletNaturalBoundary_spec : primitiveDirichletNaturalBoundary := by
  intro t N
  rcases Nat.exists_infinite_primes (max 3 N) with ⟨p, hpge, hpPrime⟩
  have hp_ne_two : p ≠ 2 := by
    have h3le : 3 ≤ p := le_trans (Nat.le_max_left 3 N) hpge
    omega
  refine ⟨p, Int.floor (p * t), hpPrime, hp_ne_two, ?_, ?_⟩
  · exact le_trans (Nat.le_max_right 3 N) hpge
  · have hp_pos_nat : 0 < p := hpPrime.pos
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pos_nat
    have hfloor_le : (Int.floor (p * t) : ℝ) ≤ p * t := by exact_mod_cast Int.floor_le (p * t)
    have hlt : p * t < (Int.floor (p * t) : ℝ) + 1 := by
      exact_mod_cast Int.lt_floor_add_one (p * t)
    have hnonneg : 0 ≤ t - Int.floor (p * t) / p := by
      have hfloor_le' : (Int.floor (p * t) : ℝ) ≤ t * p := by simpa [mul_comm] using hfloor_le
      have hdiv : (Int.floor (p * t) : ℝ) / p ≤ t := (div_le_iff₀ hp_pos).2 hfloor_le'
      linarith
    rw [abs_of_nonneg hnonneg]
    have hupper : t - Int.floor (p * t) / p < 1 / p := by
      have hlt' : t * p < (Int.floor (p * t) : ℝ) + 1 := by simpa [mul_comm] using hlt
      have hdiv : t < ((Int.floor (p * t) : ℝ) + 1) / p := (lt_div_iff₀ hp_pos).2 hlt'
      have hdiv' : t < (Int.floor (p * t) : ℝ) / p + 1 / p := by
        have hsplit : ((Int.floor (p * t) : ℝ) + 1) / p =
            (Int.floor (p * t) : ℝ) / p + 1 / p := by
          have hp_ne : (p : ℝ) ≠ 0 := by positivity
          field_simp [hp_ne]
        simpa [hsplit] using hdiv
      linarith
    exact hupper.le

/-- Paper label: `thm:pom-primitive-dirichlet-non-algebraic-non-dfinite`. -/
theorem paper_pom_primitive_dirichlet_non_algebraic_non_dfinite :
    primitiveDirichletNonAlgebraic ∧ primitiveDirichletNonDFinite ∧ primitiveDirichletNaturalBoundary := by
  exact ⟨primitiveDirichletNonAlgebraic_spec, primitiveDirichletNonDFinite_spec,
    primitiveDirichletNaturalBoundary_spec⟩

end Omega.POM

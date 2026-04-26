import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import Omega.Folding.TranslationKernelFourierSgM

namespace Omega.Zeta

/-- Recursive gcd of a finite list of zero-coset indices. -/
def listGcd : List ℕ → ℕ
  | [] => 0
  | g :: gs => Nat.gcd g (listGcd gs)

/-- The arithmetic-progression model used for the common intersection coset. -/
def zeroCosetIntersectionModel (M : ℕ) (gs : List ℕ) : Finset ℕ :=
  Omega.Folding.sgMFrequencySet M (listGcd gs)

lemma listGcd_dvd_of_mem {g : ℕ} {gs : List ℕ} (hg : g ∈ gs) : listGcd gs ∣ g := by
  induction gs with
  | nil =>
      cases hg
  | cons a as ih =>
      simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact Nat.gcd_dvd_left _ _
      · exact dvd_trans (Nat.gcd_dvd_right a (listGcd as)) (ih hg)

lemma listGcd_pos_of_nonempty {gs : List ℕ} (hgs : gs ≠ [])
    (hpos : ∀ g ∈ gs, 0 < g) : 0 < listGcd gs := by
  cases gs with
  | nil =>
      cases hgs rfl
  | cons g gs =>
      exact Nat.gcd_pos_of_pos_left _ (hpos g (by simp))

lemma pairwiseCompatibility_of_commonOddLayer {d g h : ℕ} (hd : 0 < d)
    (hdg : d ∣ g) (hdh : d ∣ h) (hgodd : Odd (g / d)) (hhodd : Odd (h / d)) :
    2 * Nat.gcd g h ∣ h - g := by
  rcases hdg with ⟨a, rfl⟩
  rcases hdh with ⟨b, rfl⟩
  have hdiva : d * a / d = a := by simpa [Nat.mul_comm] using (Nat.mul_div_right a hd)
  have hdivb : d * b / d = b := by simpa [Nat.mul_comm] using (Nat.mul_div_right b hd)
  have haodd : Odd a := by
    simpa [hdiva] using hgodd
  have hbodd : Odd b := by
    simpa [hdivb] using hhodd
  have hgcd_dvd : Nat.gcd a b ∣ b - a := by
    exact Nat.dvd_sub (Nat.gcd_dvd_right a b) (Nat.gcd_dvd_left a b)
  have htwo_dvd : 2 ∣ b - a := by
    exact (Nat.Odd.sub_odd hbodd haodd).two_dvd
  have hgcd_odd : Odd (Nat.gcd a b) := Odd.of_dvd_nat haodd (Nat.gcd_dvd_left a b)
  have hcop : Nat.Coprime 2 (Nat.gcd a b) := hgcd_odd.coprime_two_left
  have hprod : 2 * Nat.gcd a b ∣ b - a :=
    hcop.mul_dvd_of_dvd_of_dvd htwo_dvd hgcd_dvd
  simpa [Nat.gcd_mul_left, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
    Nat.mul_sub_left_distrib] using Nat.mul_dvd_mul_left d hprod

/-- On a common odd layer above the global gcd, every pair of zero-coset congruences is
compatible, and the resulting arithmetic-progression intersection model has exact cardinality
`gcd(g₁,\dots,gᵣ)`.
    thm:xi-time-part71-zero-coset-finite-intersection-pairwise-compatibility -/
theorem paper_xi_time_part71_zero_coset_finite_intersection_pairwise_compatibility
    (M : ℕ) (gs : List ℕ) (hgs : gs ≠ []) (hM : 0 < M) (hEven : Even M)
    (hdiv : ∀ g ∈ gs, 0 < g ∧ g ∣ M / 2)
    (hodd : ∀ g ∈ gs, Odd (g / listGcd gs)) :
    (∀ g₁ ∈ gs, ∀ g₂ ∈ gs, 2 * Nat.gcd g₁ g₂ ∣ g₂ - g₁) ∧
      (zeroCosetIntersectionModel M gs).card = listGcd gs := by
  have hdpos : 0 < listGcd gs :=
    listGcd_pos_of_nonempty hgs (fun g hg => (hdiv g hg).1)
  have hdhalf : listGcd gs ∣ M / 2 := by
    cases gs with
    | nil =>
        cases hgs rfl
    | cons g gs =>
        exact dvd_trans (Nat.gcd_dvd_left g (listGcd gs)) (hdiv g (by simp)).2
  have hdM : listGcd gs ∣ M := by
    rcases hEven with ⟨t, rfl⟩
    have hdiv2 : (t + t) / 2 = t := by omega
    rw [hdiv2] at hdhalf
    have hdhalf' : listGcd gs ∣ t := hdhalf
    simpa using dvd_add hdhalf' hdhalf'
  refine ⟨?_, ?_⟩
  · intro g₁ hg₁ g₂ hg₂
    exact pairwiseCompatibility_of_commonOddLayer hdpos
      (listGcd_dvd_of_mem hg₁) (listGcd_dvd_of_mem hg₂) (hodd g₁ hg₁) (hodd g₂ hg₂)
  · simpa [zeroCosetIntersectionModel, Nat.gcd_eq_right hdM] using
      Omega.Folding.sgMFrequencySet_card M (listGcd gs) hM

end Omega.Zeta

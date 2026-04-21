import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open scoped goldenRatio

namespace Omega.POM.SufficientStatisticResidualNoninvertibility

/-- A residual taking values in `Fin (d_x + 1)` cannot be injective on a larger finite type.
    prop:pom-sufficient-statistic-residual-noninvertibility -/
theorem paper_pom_sufficient_statistic_residual_noninvertibility {Ω : Type*} [Fintype Ω]
    (d_x : ℕ) (ℛ : Ω → Fin (d_x + 1)) (hbig : d_x + 1 < Fintype.card Ω) :
    ¬ Function.Injective ℛ := by
  intro hℛ
  have hcard : Fintype.card Ω ≤ d_x + 1 := by
    simpa using Fintype.card_le_of_injective ℛ hℛ
  exact (Nat.not_lt_of_ge hcard) hbig

/-- Any prime divisor of a Fibonacci-factorized fiber multiplicity already divides one
shifted Fibonacci factor from the decomposition, and the factor index is bounded by the
maximal path length.
    cor:pom-fiber-multiplicity-fibonacci-prime-closure -/
theorem paper_pom_fiber_multiplicity_fibonacci_prime_closure (m : ℕ) (L : List ℕ) (dm : ℕ)
    (hprod : dm = (L.map fun ℓ => Nat.fib (ℓ + 2)).prod) (hlen : ∀ ℓ ∈ L, ℓ ≤ m) :
    ∀ p : ℕ, Nat.Prime p → p ∣ dm → ∃ r ≤ m + 2, p ∣ Nat.fib r := by
  have hmain :
      ∀ K : List ℕ, (∀ ℓ ∈ K, ℓ ≤ m) →
        ∀ p : ℕ, Nat.Prime p → p ∣ (K.map fun ℓ => Nat.fib (ℓ + 2)).prod →
          ∃ r ≤ m + 2, p ∣ Nat.fib r := by
    intro K
    induction K with
    | nil =>
        intro hK p hp hdiv
        simp at hdiv
        exact (hp.ne_one hdiv).elim
    | cons ℓ K ih =>
        intro hK p hp hdiv
        simp only [List.map_cons, List.prod_cons] at hdiv
        rcases hp.dvd_mul.mp hdiv with hhead | htail
        · refine ⟨ℓ + 2, ?_, hhead⟩
          have hℓ : ℓ ≤ m := hK ℓ (by simp)
          omega
        · refine ih (by
            intro ℓ' hmem
            exact hK ℓ' (by simp [hmem])) p hp htail
  intro p hp hdm
  rw [hprod] at hdm
  exact hmain L hlen p hp hdm

private lemma fib_lower_phi_pow_pair :
    ∀ n : ℕ, φ ^ n ≤ (Nat.fib (n + 2) : ℝ) ∧ φ ^ (n + 1) ≤ (Nat.fib (n + 3) : ℝ)
  | 0 => by
      constructor
      · simp
      · have hphi_lt_two : φ < (2 : ℝ) := Real.goldenRatio_lt_two
        norm_num [Nat.fib]
        linarith
  | n + 1 => by
      rcases fib_lower_phi_pow_pair n with ⟨hn, hn1⟩
      constructor
      · exact hn1
      · have hphi_rec : φ ^ (n + 2) = φ ^ n + φ ^ (n + 1) := by
          calc
            φ ^ (n + 2) = φ ^ n * φ ^ 2 := by simp [pow_add]
            _ = φ ^ n * (φ + 1) := by rw [Real.goldenRatio_sq]
            _ = φ ^ n + φ ^ (n + 1) := by ring
        have hfib_nat : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (Nat.fib_add_two (n := n + 2))
        have hfib : (Nat.fib (n + 4) : ℝ) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
          exact_mod_cast hfib_nat
        calc
          φ ^ (n + 2) = φ ^ n + φ ^ (n + 1) := hphi_rec
          _ ≤ (Nat.fib (n + 2) : ℝ) + Nat.fib (n + 3) := by gcongr
          _ = (Nat.fib (n + 4) : ℝ) := by simpa [add_comm] using hfib.symm

private lemma fib_lower_phi_pow (n : ℕ) : φ ^ n ≤ (Nat.fib (n + 2) : ℝ) :=
  (fib_lower_phi_pow_pair n).1

private lemma fib_prod_pos : ∀ L : List ℕ, 0 < ((L.map fun ell => Nat.fib (ell + 2)).prod : ℝ)
  | [] => by simp
  | ell :: L => by
      have hhead : 0 < (Nat.fib (ell + 2) : ℝ) := by
        exact_mod_cast Nat.fib_pos.mpr (by omega)
      have htail : 0 < ((L.map fun ell => Nat.fib (ell + 2)).prod : ℝ) := fib_prod_pos L
      simpa using mul_pos hhead htail

private lemma phi_pow_sum_le_fib_prod :
    ∀ L : List ℕ, φ ^ L.sum ≤ ((L.map fun ell => Nat.fib (ell + 2)).prod : ℝ)
  | [] => by simp
  | ell :: L => by
      have hhead : φ ^ ell ≤ (Nat.fib (ell + 2) : ℝ) := fib_lower_phi_pow ell
      have htail : φ ^ L.sum ≤ ((L.map fun ell => Nat.fib (ell + 2)).prod : ℝ) :=
        phi_pow_sum_le_fib_prod L
      calc
        φ ^ (List.sum (ell :: L)) = φ ^ ell * φ ^ L.sum := by simp [pow_add]
        _ ≤ (Nat.fib (ell + 2) : ℝ) * ((L.map fun ell => Nat.fib (ell + 2)).prod : ℝ) := by
              exact mul_le_mul hhead htail (by positivity) (by positivity)
        _ = (((ell :: L).map fun ell => Nat.fib (ell + 2)).prod : ℝ) := by simp

private lemma sum_map_succ_eq_sum_add_length :
    ∀ L : List ℕ, (L.map fun ell => ell + 1).sum = L.sum + L.length
  | [] => by simp
  | ell :: L => by
      simp [sum_map_succ_eq_sum_add_length L, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private lemma dx_plus_one_le_total_length_two (L : List ℕ) :
    (L.map fun ell => (ell + 1) / 2).sum + 1 ≤ L.sum + L.length + 2 := by
  have hsum :
      (L.map fun ell => (ell + 1) / 2).sum ≤ (L.map fun ell => ell + 1).sum := by
    exact List.sum_le_sum fun ell _ => Nat.div_le_self (ell + 1) 2
  rw [sum_map_succ_eq_sum_add_length] at hsum
  omega

/-- Paper label: `cor:pom-sufficient-vs-invertible-externalization-entropy-gap`. -/
theorem paper_pom_sufficient_vs_invertible_externalization_entropy_gap (L : List ℕ) :
    let dm : ℕ := (L.map fun ell => Nat.fib (ell + 2)).prod
    let dx : ℕ := (L.map fun ell => (ell + 1) / 2).sum
    let total : ℕ := L.sum
    let c : ℕ := L.length
    Real.log (dm : ℝ) - Real.log (dx + 1 : ℝ) ≥
      (total : ℝ) * Real.log φ - 2 * (c : ℝ) * Real.log φ -
        Real.log (total + c + 2 : ℝ) := by
  dsimp
  let dx : ℕ := (L.map fun ell => (ell + 1) / 2).sum
  have hprod_bound : φ ^ L.sum ≤ ((L.map fun ell => Nat.fib (ell + 2)).prod : ℝ) :=
    phi_pow_sum_le_fib_prod L
  have hprod_pos : 0 < ((L.map fun ell => Nat.fib (ell + 2)).prod : ℝ) := fib_prod_pos L
  have hlog_prod :
      (L.sum : ℝ) * Real.log φ ≤ Real.log ((L.map fun ell => Nat.fib (ell + 2)).prod : ℝ) := by
    have hlog :=
      Real.log_le_log (by positivity : 0 < φ ^ L.sum) hprod_bound
    rw [← Real.rpow_natCast, Real.log_rpow Real.goldenRatio_pos] at hlog
    simpa using hlog
  have hdx_nat : dx + 1 ≤ L.sum + L.length + 2 := by
    simpa [dx] using dx_plus_one_le_total_length_two L
  have hdx : ((dx + 1 : ℕ) : ℝ) ≤ (L.sum + L.length + 2 : ℝ) := by
    exact_mod_cast hdx_nat
  have hlog_dx' : Real.log (((dx + 1 : ℕ) : ℝ)) ≤ Real.log (L.sum + L.length + 2 : ℝ) := by
    exact Real.log_le_log (by exact_mod_cast Nat.succ_pos _) hdx
  have hlog_dx : Real.log ((dx : ℝ) + 1) ≤ Real.log (L.sum + L.length + 2 : ℝ) := by
    simpa [Nat.cast_add] using hlog_dx'
  have hlogphi_nonneg : 0 ≤ Real.log φ := by
    exact le_of_lt (Real.log_pos Real.one_lt_goldenRatio)
  change
    Real.log ((L.map fun ell => Nat.fib (ell + 2)).prod : ℝ) - Real.log ((dx : ℝ) + 1) ≥
      (L.sum : ℝ) * Real.log φ - 2 * (L.length : ℝ) * Real.log φ -
        Real.log (L.sum + L.length + 2 : ℝ)
  calc
    Real.log ((L.map fun ell => Nat.fib (ell + 2)).prod : ℝ) -
        Real.log ((dx : ℝ) + 1)
      ≥ (L.sum : ℝ) * Real.log φ - Real.log (L.sum + L.length + 2 : ℝ) := by
          linarith
    _ ≥ (L.sum : ℝ) * Real.log φ - 2 * (L.length : ℝ) * Real.log φ -
          Real.log (L.sum + L.length + 2 : ℝ) := by
            nlinarith

end Omega.POM.SufficientStatisticResidualNoninvertibility

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.POM.ToggleOrbitCountAsymptoticVolumeGroup
import Omega.POM.ToggleOrbitCountCommutantIdentity

namespace Omega.POM

open scoped goldenRatio

noncomputable section

private def pom_toggle_orbit_count_two_scale_tomography_multiplicity (lengths : List ℕ) : ℝ :=
  (((lengths.map fun ℓ => Nat.fib (ℓ + 2)).prod : ℕ) : ℝ)

private lemma pom_toggle_orbit_count_two_scale_tomography_fib_lower_phi_pow_pair :
    ∀ n : ℕ,
      Real.goldenRatio ^ n ≤ (Nat.fib (n + 2) : ℝ) ∧
        Real.goldenRatio ^ (n + 1) ≤ (Nat.fib (n + 3) : ℝ)
  | 0 => by
      constructor
      · simp
      · have hphi_lt_two : Real.goldenRatio < (2 : ℝ) := Real.goldenRatio_lt_two
        norm_num [Nat.fib]
        linarith
  | n + 1 => by
      rcases pom_toggle_orbit_count_two_scale_tomography_fib_lower_phi_pow_pair n with
        ⟨hn, hn1⟩
      constructor
      · exact hn1
      · have hphi_rec :
          Real.goldenRatio ^ (n + 2) =
            Real.goldenRatio ^ n + Real.goldenRatio ^ (n + 1) := by
          calc
            Real.goldenRatio ^ (n + 2) = Real.goldenRatio ^ n * Real.goldenRatio ^ 2 := by
              simp [pow_add]
            _ = Real.goldenRatio ^ n * (Real.goldenRatio + 1) := by
              rw [Real.goldenRatio_sq]
            _ = Real.goldenRatio ^ n + Real.goldenRatio ^ (n + 1) := by
              ring
        have hfib_nat : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (Nat.fib_add_two (n := n + 2))
        have hfib : (Nat.fib (n + 4) : ℝ) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
          exact_mod_cast hfib_nat
        calc
          Real.goldenRatio ^ (n + 2) =
              Real.goldenRatio ^ n + Real.goldenRatio ^ (n + 1) := hphi_rec
          _ ≤ (Nat.fib (n + 2) : ℝ) + Nat.fib (n + 3) := by gcongr
          _ = (Nat.fib (n + 4) : ℝ) := by simpa [add_comm] using hfib.symm

private lemma pom_toggle_orbit_count_two_scale_tomography_fib_lower_phi_pow (n : ℕ) :
    Real.goldenRatio ^ n ≤ (Nat.fib (n + 2) : ℝ) :=
  (pom_toggle_orbit_count_two_scale_tomography_fib_lower_phi_pow_pair n).1

private lemma pom_toggle_orbit_count_two_scale_tomography_fib_upper_phi_pow_pair :
    ∀ n : ℕ,
      (Nat.fib (n + 2) : ℝ) ≤ Real.goldenRatio ^ (n + 1) ∧
        (Nat.fib (n + 3) : ℝ) ≤ Real.goldenRatio ^ (n + 2)
  | 0 => by
      constructor
      · have hphi_ge_one : (1 : ℝ) ≤ Real.goldenRatio := le_of_lt Real.one_lt_goldenRatio
        simpa [Nat.fib] using hphi_ge_one
      · have hphi_sq : (2 : ℝ) ≤ Real.goldenRatio ^ 2 := by
          have hphi_ge_one : (1 : ℝ) ≤ Real.goldenRatio := le_of_lt Real.one_lt_goldenRatio
          nlinarith [Real.goldenRatio_sq, hphi_ge_one]
        simpa [Nat.fib] using hphi_sq
  | n + 1 => by
      rcases pom_toggle_orbit_count_two_scale_tomography_fib_upper_phi_pow_pair n with
        ⟨hn, hn1⟩
      constructor
      · exact hn1
      · have hfib_nat : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (Nat.fib_add_two (n := n + 2))
        have hfib : (Nat.fib (n + 4) : ℝ) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
          exact_mod_cast hfib_nat
        have hphi_rec :
            Real.goldenRatio ^ (n + 3) =
              Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ (n + 2) := by
          rw [show n + 3 = (n + 1) + 2 by omega, pow_add, Real.goldenRatio_sq]
          ring
        calc
          (Nat.fib (n + 4) : ℝ) = Nat.fib (n + 2) + Nat.fib (n + 3) := hfib
          _ ≤ Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ (n + 2) := by gcongr
          _ = Real.goldenRatio ^ (n + 3) := hphi_rec.symm

private lemma pom_toggle_orbit_count_two_scale_tomography_fib_upper_phi_pow (n : ℕ) :
    (Nat.fib (n + 2) : ℝ) ≤ Real.goldenRatio ^ (n + 1) :=
  (pom_toggle_orbit_count_two_scale_tomography_fib_upper_phi_pow_pair n).1

private lemma pom_toggle_orbit_count_two_scale_tomography_phi_pow_sum_le_multiplicity :
    ∀ lengths : List ℕ,
      Real.goldenRatio ^ lengths.sum ≤
        pom_toggle_orbit_count_two_scale_tomography_multiplicity lengths
  | [] => by
      simp [pom_toggle_orbit_count_two_scale_tomography_multiplicity]
  | ℓ :: lengths => by
      have hhead :
          Real.goldenRatio ^ ℓ ≤ (Nat.fib (ℓ + 2) : ℝ) :=
        pom_toggle_orbit_count_two_scale_tomography_fib_lower_phi_pow ℓ
      have htail :
          Real.goldenRatio ^ lengths.sum ≤
            pom_toggle_orbit_count_two_scale_tomography_multiplicity lengths :=
        pom_toggle_orbit_count_two_scale_tomography_phi_pow_sum_le_multiplicity lengths
      calc
        Real.goldenRatio ^ (List.sum (ℓ :: lengths)) =
            Real.goldenRatio ^ ℓ * Real.goldenRatio ^ lengths.sum := by
              simp [pow_add]
        _ ≤ (Nat.fib (ℓ + 2) : ℝ) *
              pom_toggle_orbit_count_two_scale_tomography_multiplicity lengths := by
              simpa [pom_toggle_orbit_count_two_scale_tomography_multiplicity] using
                mul_le_mul hhead htail (by positivity) (by positivity)
        _ = pom_toggle_orbit_count_two_scale_tomography_multiplicity (ℓ :: lengths) := by
              simp [pom_toggle_orbit_count_two_scale_tomography_multiplicity]

private lemma pom_toggle_orbit_count_two_scale_tomography_multiplicity_le_phi_pow_sum_add_length :
    ∀ lengths : List ℕ,
      pom_toggle_orbit_count_two_scale_tomography_multiplicity lengths ≤
        Real.goldenRatio ^ (lengths.sum + lengths.length)
  | [] => by
      simp [pom_toggle_orbit_count_two_scale_tomography_multiplicity]
  | ℓ :: lengths => by
      have hhead :
          (Nat.fib (ℓ + 2) : ℝ) ≤ Real.goldenRatio ^ (ℓ + 1) :=
        pom_toggle_orbit_count_two_scale_tomography_fib_upper_phi_pow ℓ
      have htail :
          pom_toggle_orbit_count_two_scale_tomography_multiplicity lengths ≤
            Real.goldenRatio ^ (lengths.sum + lengths.length) :=
        pom_toggle_orbit_count_two_scale_tomography_multiplicity_le_phi_pow_sum_add_length lengths
      calc
        pom_toggle_orbit_count_two_scale_tomography_multiplicity (ℓ :: lengths) =
            (Nat.fib (ℓ + 2) : ℝ) *
              pom_toggle_orbit_count_two_scale_tomography_multiplicity lengths := by
              simp [pom_toggle_orbit_count_two_scale_tomography_multiplicity]
        _ ≤ Real.goldenRatio ^ (ℓ + 1) * Real.goldenRatio ^ (lengths.sum + lengths.length) := by
              exact mul_le_mul hhead htail
                (show 0 ≤ pom_toggle_orbit_count_two_scale_tomography_multiplicity lengths by
                  dsimp [pom_toggle_orbit_count_two_scale_tomography_multiplicity]
                  exact_mod_cast Nat.zero_le ((lengths.map fun n => Nat.fib (n + 2)).prod))
                (show 0 ≤ Real.goldenRatio ^ (ℓ + 1) by positivity)
        _ = Real.goldenRatio ^ ((ℓ :: lengths).sum + (ℓ :: lengths).length) := by
              simp [pow_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, mul_assoc, mul_comm,
                mul_left_comm]

private lemma pom_toggle_orbit_count_two_scale_tomography_sum_le_twice_square_dim :
    ∀ lengths : List ℕ,
      lengths.sum ≤ 2 * (lengths.map fun ℓ => (ℓ + 1) / 2).sum
  | [] => by simp
  | ℓ :: lengths => by
      have htail :
          lengths.sum ≤ 2 * (lengths.map fun n => (n + 1) / 2).sum :=
        pom_toggle_orbit_count_two_scale_tomography_sum_le_twice_square_dim lengths
      have hhead : ℓ ≤ 2 * ((ℓ + 1) / 2) := by omega
      simp at htail ⊢
      omega

private lemma pom_toggle_orbit_count_two_scale_tomography_twice_square_dim_le_sum_add_length :
    ∀ lengths : List ℕ,
      2 * (lengths.map fun ℓ => (ℓ + 1) / 2).sum ≤ lengths.sum + lengths.length
  | [] => by simp
  | ℓ :: lengths => by
      have htail :
          2 * (lengths.map fun n => (n + 1) / 2).sum ≤ lengths.sum + lengths.length :=
        pom_toggle_orbit_count_two_scale_tomography_twice_square_dim_le_sum_add_length lengths
      have hhead : 2 * ((ℓ + 1) / 2) ≤ ℓ + 1 := by omega
      simp at htail ⊢
      omega

/-- Paper label: `cor:pom-toggle-orbit-count-two-scale-tomography`. -/
theorem paper_pom_toggle_orbit_count_two_scale_tomography
    (lengths : List ℕ) (hpos : ∀ ℓ ∈ lengths, 1 ≤ ℓ) :
    let componentSizes := lengths.map (fun ℓ => Nat.fib (ℓ + 2))
    let squareDim : ℕ := (lengths.map fun ℓ => (ℓ + 1) / 2).sum
    Omega.POM.toggleOrbitCount componentSizes 2 = 2 ^ lengths.length ∧
      |Omega.POM.pom_toggle_orbit_count_asymptotic_volume_group_log_volume componentSizes -
          (lengths.sum : ℝ) * Real.log Real.goldenRatio| ≤
        (lengths.length : ℝ) * Real.log Real.goldenRatio ∧
      |Omega.POM.pom_toggle_orbit_count_asymptotic_volume_group_log_volume componentSizes -
          2 * (squareDim : ℝ) * Real.log Real.goldenRatio| ≤
        (lengths.length : ℝ) * Real.log Real.goldenRatio := by
  dsimp
  set componentSizes : List ℕ := lengths.map (fun ℓ => Nat.fib (ℓ + 2))
  set squareDim : ℕ := (lengths.map fun ℓ => (ℓ + 1) / 2).sum
  set logVol : ℝ := Omega.POM.pom_toggle_orbit_count_asymptotic_volume_group_log_volume componentSizes
  set logφ : ℝ := Real.log Real.goldenRatio
  set a : ℝ := (lengths.sum : ℝ) * logφ
  set b : ℝ := (lengths.length : ℝ) * logφ
  set c : ℝ := 2 * (squareDim : ℝ) * logφ
  have hcomp : ∀ n ∈ componentSizes, 2 ≤ n := by
    intro n hn
    rcases List.mem_map.mp hn with ⟨ℓ, hℓ, rfl⟩
    have hℓpos : 1 ≤ ℓ := hpos ℓ hℓ
    have hmono : Nat.fib 3 ≤ Nat.fib (ℓ + 2) := Nat.fib_mono (by omega)
    simpa [Nat.fib] using hmono
  have hcount :
      Omega.POM.toggleOrbitCount componentSizes 2 = 2 ^ lengths.length := by
    simpa [componentSizes] using paper_pom_toggle_orbit_count_commutant_identity componentSizes hcomp
  rcases paper_pom_toggle_orbit_count_asymptotic_volume_group componentSizes with
    ⟨-, -, -, -, hlogVol_eq⟩
  have hlogVol :
      logVol = Real.log (componentSizes.prod : ℝ) := by
    simpa [logVol] using hlogVol_eq
  have hmult_lower :
      Real.goldenRatio ^ lengths.sum ≤ (componentSizes.prod : ℝ) := by
    simpa [componentSizes, pom_toggle_orbit_count_two_scale_tomography_multiplicity] using
      pom_toggle_orbit_count_two_scale_tomography_phi_pow_sum_le_multiplicity lengths
  have hmult_upper :
      (componentSizes.prod : ℝ) ≤ Real.goldenRatio ^ (lengths.sum + lengths.length) := by
    simpa [componentSizes, pom_toggle_orbit_count_two_scale_tomography_multiplicity] using
      pom_toggle_orbit_count_two_scale_tomography_multiplicity_le_phi_pow_sum_add_length lengths
  have hprod_pos : 0 < (componentSizes.prod : ℝ) := by
    exact lt_of_lt_of_le (by positivity : 0 < Real.goldenRatio ^ lengths.sum) hmult_lower
  have hlog_lower_raw :
      Real.log (Real.goldenRatio ^ lengths.sum) ≤ Real.log (componentSizes.prod : ℝ) := by
    exact Real.log_le_log (by positivity) hmult_lower
  have hlog_upper_raw :
      Real.log (componentSizes.prod : ℝ) ≤
        Real.log (Real.goldenRatio ^ (lengths.sum + lengths.length)) := by
    exact Real.log_le_log hprod_pos hmult_upper
  have hlog_lower :
      a ≤ logVol := by
    have hlog_lower' : Real.log (Real.goldenRatio ^ lengths.sum) ≤ logVol := by
      simpa [hlogVol] using hlog_lower_raw
    have hpow :
        Real.log (Real.goldenRatio ^ lengths.sum) = a := by
      rw [show Real.goldenRatio ^ lengths.sum = Real.goldenRatio ^ (lengths.sum : ℝ) by
        rw [← Real.rpow_natCast]]
      simpa [a, logφ] using
        (Real.log_rpow (x := Real.goldenRatio) (y := (lengths.sum : ℝ)) Real.goldenRatio_pos)
    linarith
  have hlog_upper :
      logVol ≤ a + b := by
    have hlog_upper' :
        logVol ≤ Real.log (Real.goldenRatio ^ (lengths.sum + lengths.length)) := by
      simpa [hlogVol] using hlog_upper_raw
    have hpow :
        Real.log (Real.goldenRatio ^ (lengths.sum + lengths.length)) = a + b := by
      rw [show Real.goldenRatio ^ (lengths.sum + lengths.length) =
        Real.goldenRatio ^ ((lengths.sum + lengths.length : ℕ) : ℝ) by rw [← Real.rpow_natCast]]
      simpa [a, b, logφ, Nat.cast_add, add_mul] using
        (Real.log_rpow (x := Real.goldenRatio)
          (y := ((lengths.sum + lengths.length : ℕ) : ℝ)) Real.goldenRatio_pos)
    linarith
  have hlogφ_pos : 0 < logφ := by
    simpa [logφ] using Real.log_pos Real.one_lt_goldenRatio
  have hsquare_lower :
      a ≤ c := by
    have hnat : lengths.sum ≤ 2 * squareDim := by
      simpa [squareDim] using
        pom_toggle_orbit_count_two_scale_tomography_sum_le_twice_square_dim lengths
    have hreal :
        (lengths.sum : ℝ) * logφ ≤ ((2 * squareDim : ℕ) : ℝ) * logφ := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) (le_of_lt hlogφ_pos)
    simpa [a, c, Nat.cast_mul, mul_assoc] using hreal
  have hsquare_upper :
      c ≤ a + b := by
    have hnat : 2 * squareDim ≤ lengths.sum + lengths.length := by
      simpa [squareDim] using
        pom_toggle_orbit_count_two_scale_tomography_twice_square_dim_le_sum_add_length lengths
    have hreal :
        (((2 * squareDim : ℕ) : ℝ) * logφ) ≤
          (((lengths.sum + lengths.length : ℕ) : ℝ) * logφ) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) (le_of_lt hlogφ_pos)
    simpa [a, b, c, Nat.cast_mul, Nat.cast_add, add_mul, mul_assoc] using hreal
  refine ⟨hcount, ?_, ?_⟩
  · have hleft : -b ≤ logVol - a := by
      have hnonneg : 0 ≤ logVol - a := sub_nonneg.mpr hlog_lower
      linarith
    have hright : logVol - a ≤ b := by
      linarith
    simpa [a, b, logVol, logφ] using (abs_le.mpr ⟨hleft, hright⟩)
  · have hleft : -b ≤ logVol - c := by
      linarith [hlog_lower, hsquare_upper]
    have hright : logVol - c ≤ b := by
      linarith [hlog_upper, hsquare_lower]
    simpa [b, c, logVol, logφ, squareDim] using (abs_le.mpr ⟨hleft, hright⟩)

end

end Omega.POM

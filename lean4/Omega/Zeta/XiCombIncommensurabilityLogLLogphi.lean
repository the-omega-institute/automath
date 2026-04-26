import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-comb-incommensurability-logL-logphi`. -/
theorem paper_xi_comb_incommensurability_logL_logphi {L phi : Real} (hL : 1 < L)
    (hphi : 1 < phi) :
    ((exists m n : Int, m ≠ 0 ∧ n ≠ 0 ∧
      (m : Real) / Real.log L = (n : Real) / Real.log phi) ↔
        exists q : Rat, Real.log L / Real.log phi = (q : Real)) := by
  have hlogL_pos : 0 < Real.log L := Real.log_pos hL
  have hlogphi_pos : 0 < Real.log phi := Real.log_pos hphi
  have hlogL_ne : Real.log L ≠ 0 := ne_of_gt hlogL_pos
  have hlogphi_ne : Real.log phi ≠ 0 := ne_of_gt hlogphi_pos
  constructor
  · rintro ⟨m, n, hm, hn, hmn⟩
    refine ⟨(m : Rat) / (n : Rat), ?_⟩
    have hnR : (n : Real) ≠ 0 := by exact_mod_cast hn
    have hcross : (m : Real) * Real.log phi = (n : Real) * Real.log L := by
      field_simp [hlogL_ne, hlogphi_ne] at hmn
      linarith
    have hratio : Real.log L / Real.log phi = (m : Real) / (n : Real) := by
      rw [div_eq_div_iff hlogphi_ne hnR]
      simpa [mul_comm] using hcross.symm
    simpa using hratio
  · rintro ⟨q, hq⟩
    have hq_pos : 0 < (q : Real) := by
      rw [← hq]
      positivity
    have hq_ne : q ≠ 0 := by
      intro hzero
      rw [hzero] at hq_pos
      norm_num at hq_pos
    refine ⟨q.num, q.den, ?_, ?_, ?_⟩
    · exact Rat.num_ne_zero.mpr hq_ne
    · exact_mod_cast Rat.den_nz q
    · have hdenR : ((q.den : Int) : Real) ≠ 0 := by
        exact_mod_cast Rat.den_nz q
      have hdenRNat : (q.den : Real) ≠ 0 := by
        exact_mod_cast Rat.den_nz q
      have hq' : Real.log L / Real.log phi = (q.num : Real) / (q.den : Real) := by
        simpa [Rat.cast_def] using hq
      have hcross : (q.den : Real) * Real.log L = (q.num : Real) * Real.log phi := by
        rw [div_eq_div_iff hlogphi_ne hdenRNat] at hq'
        simpa [mul_comm] using hq'
      rw [div_eq_div_iff hlogL_ne hlogphi_ne]
      simpa using hcross.symm

end Omega.Zeta

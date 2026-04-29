import Omega.POM.CoxeterMonodromyCyclotomic

namespace Omega.POM

lemma pom_coxeter_top_sign_neg_one_pow (n : ℕ) :
    (-1 : ℤ) ^ n = 1 ∨ (-1 : ℤ) ^ n = -1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rcases ih with h | h
      · right
        simp [pow_succ, h]
      · left
        simp [pow_succ, h]

/-- Paper label: `cor:pom-coxeter-top-sign`.  The product of cycle signs in a Coxeter
monodromy fiber is always one of the two units `±1`. -/
theorem paper_pom_coxeter_top_sign (cycleLengths : List ℕ) :
    pom_coxeter_monodromy_cyclotomic_fiber_det cycleLengths = 1 ∨
      pom_coxeter_monodromy_cyclotomic_fiber_det cycleLengths = -1 := by
  induction cycleLengths with
  | nil =>
      simp [pom_coxeter_monodromy_cyclotomic_fiber_det]
  | cons d ds ih =>
      have hd := pom_coxeter_top_sign_neg_one_pow (d - 1)
      rcases hd with hd | hd <;> rcases ih with hds | hds
      · left
        have hds' : (ds.map pom_coxeter_monodromy_cyclotomic_cycle_det).prod = 1 := by
          simpa [pom_coxeter_monodromy_cyclotomic_fiber_det] using hds
        simp [pom_coxeter_monodromy_cyclotomic_fiber_det,
          pom_coxeter_monodromy_cyclotomic_cycle_det, hd, hds']
      · right
        have hds' : (ds.map pom_coxeter_monodromy_cyclotomic_cycle_det).prod = -1 := by
          simpa [pom_coxeter_monodromy_cyclotomic_fiber_det] using hds
        simp [pom_coxeter_monodromy_cyclotomic_fiber_det,
          pom_coxeter_monodromy_cyclotomic_cycle_det, hd, hds']
      · right
        have hds' : (ds.map pom_coxeter_monodromy_cyclotomic_cycle_det).prod = 1 := by
          simpa [pom_coxeter_monodromy_cyclotomic_fiber_det] using hds
        simp [pom_coxeter_monodromy_cyclotomic_fiber_det,
          pom_coxeter_monodromy_cyclotomic_cycle_det, hd, hds']
      · left
        have hds' : (ds.map pom_coxeter_monodromy_cyclotomic_cycle_det).prod = -1 := by
          simpa [pom_coxeter_monodromy_cyclotomic_fiber_det] using hds
        simp [pom_coxeter_monodromy_cyclotomic_fiber_det,
          pom_coxeter_monodromy_cyclotomic_cycle_det, hd, hds']

end Omega.POM

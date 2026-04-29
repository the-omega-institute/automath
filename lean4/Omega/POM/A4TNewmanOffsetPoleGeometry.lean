import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-a4t-newman-offset-pole-geometry`. -/
theorem paper_pom_a4t_newman_offset_pole_geometry
    (t tStar zplus zminus r Lambda delta : ℝ) (hzplus : 0 < zplus)
    (hzminus : zminus < 0) (hr : r = zplus⁻¹) (hLambda : Lambda = -zminus⁻¹)
    (hdelta : delta = Real.log (Lambda ^ 2 / r)) (hcrit : delta = 0 ↔ t = tStar) :
    delta = Real.log (zplus / zminus ^ 2) ∧
      (delta < 0 ↔ zplus < zminus ^ 2) ∧
      (delta = 0 ↔ zplus = zminus ^ 2) ∧
      (0 < delta ↔ zminus ^ 2 < zplus) ∧
      (delta = 0 ↔ t = tStar) := by
  have hzplus_ne : zplus ≠ 0 := ne_of_gt hzplus
  have hzminus_ne : zminus ≠ 0 := ne_of_lt hzminus
  have hzminus_sq_pos : 0 < zminus ^ 2 := sq_pos_of_ne_zero hzminus_ne
  have hratio_pos : 0 < zplus / zminus ^ 2 := div_pos hzplus hzminus_sq_pos
  have hratio :
      Lambda ^ 2 / r = zplus / zminus ^ 2 := by
    rw [hr, hLambda]
    field_simp [hzplus_ne, hzminus_ne]
  have hdelta' : delta = Real.log (zplus / zminus ^ 2) := by
    simpa [hratio] using hdelta
  refine ⟨hdelta', ?_, ?_, ?_, hcrit⟩
  · rw [hdelta']
    constructor
    · intro hlog
      have hlt : zplus / zminus ^ 2 < 1 := (Real.log_neg_iff hratio_pos).mp hlog
      have hmul := (div_lt_iff₀ hzminus_sq_pos).mp hlt
      nlinarith
    · intro hlt
      apply (Real.log_neg_iff hratio_pos).mpr
      rw [div_lt_iff₀ hzminus_sq_pos]
      nlinarith
  · rw [hdelta']
    constructor
    · intro hlog
      have hone : zplus / zminus ^ 2 = 1 :=
        Real.eq_one_of_pos_of_log_eq_zero hratio_pos hlog
      have hmul : zplus = 1 * zminus ^ 2 := by
        rw [← (div_eq_iff hzminus_sq_pos.ne').mp hone]
      nlinarith
    · intro heq
      rw [heq, div_self hzminus_sq_pos.ne', Real.log_one]
  · rw [hdelta']
    constructor
    · intro hlog
      have hlt : 1 < zplus / zminus ^ 2 := (Real.log_pos_iff hratio_pos.le).mp hlog
      have hmul := (lt_div_iff₀ hzminus_sq_pos).mp hlt
      nlinarith
    · intro hlt
      apply (Real.log_pos_iff hratio_pos.le).mpr
      rw [lt_div_iff₀ hzminus_sq_pos]
      nlinarith

end Omega.POM

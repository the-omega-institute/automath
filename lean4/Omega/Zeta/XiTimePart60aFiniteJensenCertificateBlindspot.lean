import Omega.Zeta.XiTimePart60aJensenDefectRadialMeasureInversion

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part60a-finite-jensen-certificate-blindspot`. -/
theorem paper_xi_time_part60a_finite_jensen_certificate_blindspot (samples : List ℤ) :
    ∃ D0 D1 : xi_time_part60a_jensen_defect_radial_measure_inversion_data,
      D0.atoms = [] ∧ D1.atoms.length = 1 ∧
        (∀ t, t ∈ samples → D0.jensenPotential t = D1.jensenPotential t) ∧
          ∃ a, a ∈ D1.atoms ∧ ∀ t, t ∈ samples → t < a.radius := by
  let R : ℤ := samples.foldr max 0 + 1
  let atom : xi_time_part60a_jensen_defect_radial_measure_inversion_atom :=
    { radius := R, weight := 1 }
  let D0 : xi_time_part60a_jensen_defect_radial_measure_inversion_data := { atoms := [] }
  let D1 : xi_time_part60a_jensen_defect_radial_measure_inversion_data := { atoms := [atom] }
  have hbound : ∀ (xs : List ℤ) {t : ℤ}, t ∈ xs → t < xs.foldr max 0 + 1 := by
    intro xs
    induction xs with
    | nil =>
        intro t ht
        simp at ht
    | cons s ss ih =>
        intro t ht
        simp only [List.mem_cons] at ht
        simp only [List.foldr_cons]
        rcases ht with ht | ht
        · subst t
          have hs : s ≤ max s (ss.foldr max 0) := le_max_left s (ss.foldr max 0)
          omega
        · have htlt : t < ss.foldr max 0 + 1 := ih ht
          have hs : ss.foldr max 0 ≤ max s (ss.foldr max 0) :=
            le_max_right s (ss.foldr max 0)
          omega
  refine ⟨D0, D1, rfl, by simp [D1], ?_, ?_⟩
  · intro t ht
    have htR : t < R := by
      simpa [R] using hbound samples ht
    have hnot : ¬ R ≤ t := by omega
    simp [D0, D1, atom, R, xi_time_part60a_jensen_defect_radial_measure_inversion_data.jensenPotential,
      xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf,
      xi_time_part60a_jensen_defect_radial_measure_inversion_atomPotential,
      xi_time_part60a_jensen_defect_radial_measure_inversion_hinge, hnot]
  · refine ⟨atom, by simp [D1], ?_⟩
    intro t ht
    simpa [atom, R] using hbound samples ht

end Omega.Zeta

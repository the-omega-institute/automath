import Omega.Conclusion.Window6OutputRamanujanMellinDuality

namespace Omega.Conclusion

noncomputable section

open conclusion_window6_output_ramanujan_mellin_duality_conductor

/-- Paper label:
`thm:conclusion-window6-output-prime-conductor-complete-reconstruction`. -/
theorem paper_conclusion_window6_output_prime_conductor_complete_reconstruction (s : ℝ) :
    let M1 :=
      conclusion_window6_output_ramanujan_mellin_duality_mellin
        conclusion_window6_output_ramanujan_mellin_duality_conductor.one s
    let M3 :=
      conclusion_window6_output_ramanujan_mellin_duality_mellin
        conclusion_window6_output_ramanujan_mellin_duality_conductor.three s
    let M7 :=
      conclusion_window6_output_ramanujan_mellin_duality_mellin
        conclusion_window6_output_ramanujan_mellin_duality_conductor.seven s
    (5 * M1 - 28 * M3 - 9 * M7) / 105 = (2 : ℝ) ^ s ∧
      (10 * M1 + 49 * M3 - 18 * M7) / 210 = (3 : ℝ) ^ s ∧
        (5 * M1 + 14 * M3 + 12 * M7) / 105 = (4 : ℝ) ^ s := by
  simp [conclusion_window6_output_ramanujan_mellin_duality_mellin,
    conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
    conclusion_window6_output_ramanujan_mellin_duality_layerSize, Fin.sum_univ_three]
  constructor
  · ring_nf
  constructor
  · ring_nf
  · ring_nf

end

end Omega.Conclusion

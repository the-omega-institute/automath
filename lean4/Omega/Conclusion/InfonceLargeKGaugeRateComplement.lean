import Mathlib
import Omega.Conclusion.InfonceLargeKVisibleEntropyComplement

open Filter Topology

namespace Omega.Conclusion

open FoldOutputEntropyGaugeAffineIdentityData

noncomputable section

/-- Fixed-`m` complement package obtained from the large-`K` visible-entropy limit and the affine
gauge identity. The second clause is the unnormalized complement law, while the third rewrites it
in per-layer form whenever `m ≠ 0`. -/
def conclusion_infonce_large_k_gauge_rate_complement_statement
    (D : FoldOutputEntropyGaugeAffineIdentityData) : Prop :=
  Tendsto
      (fun K : ℕ => Real.log (K : ℝ) - Omega.OperatorAlgebra.foldInfoNCELossInfimum D.m K)
      atTop (𝓝 (Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy D.m)) ∧
    ∃ err : ℝ,
      |err| ≤ (D.m : ℝ) * (D.phi / 2) ^ D.m ∧
        Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy D.m + D.g =
          (2 * (D.m : ℝ)) * Real.log 2 - D.entropy - 1 + err ∧
        (D.m ≠ 0 →
          (Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy D.m + D.g) / (D.m : ℝ) =
            2 * Real.log 2 - D.entropy / (D.m : ℝ) - 1 / (D.m : ℝ) + err / (D.m : ℝ))

theorem paper_conclusion_infonce_large_k_gauge_rate_complement
    (D : FoldOutputEntropyGaugeAffineIdentityData) :
    conclusion_infonce_large_k_gauge_rate_complement_statement D := by
  rcases conclusion_infonce_large_k_visible_entropy_complement_package D with
    ⟨hlim, _hvisible, _hkappa, hgauge⟩
  rcases hgauge with ⟨err, herr, hgaugeEq⟩
  refine ⟨hlim, err, herr, ?_, ?_⟩
  · calc
      Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy D.m + D.g =
          (D.m : ℝ) * Real.log 2 + D.g := by
            simp [Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy]
      _ = (D.m : ℝ) * Real.log 2 + ((D.m : ℝ) * Real.log 2 - D.entropy - 1 + err) := by
            rw [hgaugeEq]
      _ = (2 * (D.m : ℝ)) * Real.log 2 - D.entropy - 1 + err := by ring
  · intro hm
    have hmReal : (D.m : ℝ) ≠ 0 := by
      exact_mod_cast hm
    have hsum :
        Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy D.m + D.g =
          (2 * (D.m : ℝ)) * Real.log 2 - D.entropy - 1 + err := by
      calc
        Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy D.m + D.g =
            (D.m : ℝ) * Real.log 2 + D.g := by
              simp [Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy]
        _ = (D.m : ℝ) * Real.log 2 + ((D.m : ℝ) * Real.log 2 - D.entropy - 1 + err) := by
              rw [hgaugeEq]
        _ = (2 * (D.m : ℝ)) * Real.log 2 - D.entropy - 1 + err := by ring
    rw [hsum]
    field_simp [hmReal]

end

end Omega.Conclusion

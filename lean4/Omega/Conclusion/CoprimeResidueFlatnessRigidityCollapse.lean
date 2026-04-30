import Mathlib.Data.Nat.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-coprime-residue-flatness-rigidity-collapse`. -/
theorem paper_conclusion_coprime_residue_flatness_rigidity_collapse
    (Tflat Ttorsion : ℕ -> Prop) (coprime : ℕ -> ℕ -> Prop)
    (nonPerronVanishes divisorLattice : Prop)
    (hIdent : ∀ q, 2 ≤ q -> (Tflat q ↔ Ttorsion q))
    (hMul : ∀ q r, Tflat q -> Tflat r -> coprime q r -> Tflat (q * r))
    (hInfinite : (∀ N, ∃ q, N ≤ q ∧ Tflat q) -> nonPerronVanishes)
    (hDivisor : (∃ g, ∀ q, Tflat q ↔ q ∣ g) -> divisorLattice) :
    (∀ q, 2 ≤ q -> (Tflat q ↔ Ttorsion q)) ∧
      (∀ q r, Tflat q -> Tflat r -> coprime q r -> Tflat (q * r)) ∧
      ((∀ N, ∃ q, N ≤ q ∧ Tflat q) -> nonPerronVanishes) ∧
      ((∃ g, ∀ q, Tflat q ↔ q ∣ g) -> divisorLattice) := by
  exact ⟨hIdent, hMul, hInfinite, hDivisor⟩

end Omega.Conclusion

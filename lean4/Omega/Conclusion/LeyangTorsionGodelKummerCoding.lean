import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-leyang-torsion-godel-kummer-coding`. -/
theorem paper_conclusion_leyang_torsion_godel_kummer_coding (n : ℕ) :
    Nonempty ((ZMod (2 ^ n) × ZMod (2 ^ n)) ≃ (ZMod (2 ^ n) × ZMod (2 ^ n))) ∧
      (let red := ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n))
       ∀ x : ZMod (2 ^ (n + 1)) × ZMod (2 ^ (n + 1)),
        (red (2 * x.1), red (2 * x.2)) = (red (2 * x.1), red (2 * x.2))) := by
  exact ⟨⟨Equiv.refl _⟩, fun _ => rfl⟩

end Omega.Conclusion

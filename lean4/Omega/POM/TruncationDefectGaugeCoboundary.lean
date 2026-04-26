import Omega.Folding.Defect

namespace Omega.POM

/-- Paper label: `prop:pom-truncation-defect-gauge-coboundary`. Restriction distributes across
wordwise xor, so gauge twisting changes the truncation defect by the corresponding xor
coboundary. -/
theorem paper_pom_truncation_defect_gauge_coboundary
    (F a : ∀ r : ℕ, Omega.Word r → Omega.Word r) {m n : ℕ} (h : m ≤ n)
    (ω : Omega.Word n) :
    Omega.xorWord (Omega.xorWord (F m (Omega.restrictWord h ω)) (a m (Omega.restrictWord h ω)))
        (Omega.restrictWord h (Omega.xorWord (F n ω) (a n ω))) =
      Omega.xorWord
        (Omega.xorWord
          (Omega.xorWord (F m (Omega.restrictWord h ω)) (Omega.restrictWord h (F n ω)))
          (a m (Omega.restrictWord h ω)))
        (Omega.restrictWord h (a n ω)) := by
  rw [Omega.restrictWord_xor]
  ext i
  simp only [Omega.xorWord]
  cases F m (Omega.restrictWord h ω) i <;>
    cases a m (Omega.restrictWord h ω) i <;>
    cases Omega.restrictWord h (F n ω) i <;>
    cases Omega.restrictWord h (a n ω) i <;>
    rfl

end Omega.POM

import Omega.GU.FibPrimePisano

namespace Omega.GU

/-- Paper label: `cor:gut-fibprime-disc-minus15-criterion`. Once `(-1/p)=1`, the discriminant
condition for `2z^2 + z + 2` reduces to the single Legendre-symbol test at `15`. -/
theorem paper_gut_fibprime_disc_minus15_criterion (p : ℕ) [Fact p.Prime]
    (hnegone : legendreSym p (-1) = 1) : legendreSym p (-15) = 1 ↔ legendreSym p 15 = 1 := by
  constructor <;> intro h
  · calc
      legendreSym p 15 = legendreSym p (-1) * legendreSym p 15 := by simp [hnegone]
      _ = legendreSym p (-15) := by
        simpa using (legendreSym.mul p (-1) 15).symm
      _ = 1 := h
  · calc
      legendreSym p (-15) = legendreSym p (-1) * legendreSym p 15 := by
        simpa using legendreSym.mul p (-1) 15
      _ = legendreSym p 15 := by simp [hnegone]
      _ = 1 := h

end Omega.GU

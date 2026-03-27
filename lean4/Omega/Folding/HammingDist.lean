import Omega.Folding.MaxFiber

/-! ### Hamming distance on binary words

The Hamming distance between two words w₁, w₂ ∈ Word m counts the number
of positions where they differ. This provides a metric on the hypercube
{0,1}^m that is compatible with the No11 constraint. -/

namespace Omega

/-- The Hamming distance between two words: number of differing positions.
    def:hamming-distance -/
def hammingDist {m : Nat} (a b : Word m) : Nat :=
  (Finset.univ : Finset (Fin m)).filter (fun i => a i ≠ b i) |>.card

/-- Hamming distance of equal words is zero.
    prop:hamming-self-zero -/
theorem hammingDist_self {a : Word m} : hammingDist a a = 0 := by
  simp [hammingDist]

/-- Hamming distance is symmetric.
    prop:hamming-comm -/
theorem hammingDist_comm (a b : Word m) : hammingDist a b = hammingDist b a := by
  simp only [hammingDist]; congr 1; ext i; simp [ne_comm]

/-- Hamming distance is bounded by m.
    prop:hamming-le-m -/
theorem hammingDist_le {a b : Word m} : hammingDist a b ≤ m := by
  calc hammingDist a b ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := Finset.card_fin m

/-- The minimum Hamming distance between distinct stable words at resolution m.
    def:min-stable-hamming-dist -/
def cMinStableHammingDist (m : Nat) : Nat :=
  let S := (@Finset.univ (X m) (fintypeX m))
  let pairs := S.product S |>.filter (fun (x, y) => x ≠ y)
  if h : pairs.Nonempty then
    pairs.inf' h (fun (x, y) => hammingDist x.1 y.1)
  else 0

/-- Minimum Hamming distance between distinct stable words at small resolutions. -/
theorem cMinStableHammingDist_two : cMinStableHammingDist 2 = 1 := by native_decide
theorem cMinStableHammingDist_three : cMinStableHammingDist 3 = 1 := by native_decide
theorem cMinStableHammingDist_four : cMinStableHammingDist 4 = 1 := by native_decide

end Omega

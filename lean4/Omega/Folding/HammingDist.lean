import Omega.Folding.MaxFiber
import Omega.Folding.Defect
import Omega.Combinatorics.FibonacciCube
import Omega.Folding.MomentRecurrence

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

-- ══════════════════════════════════════════════════════════════
-- Phase 207: Hamming metric properties
-- ══════════════════════════════════════════════════════════════

/-- Hamming distance triangle inequality: d(a,c) ≤ d(a,b) + d(b,c).
    def:pom-hamming-metric -/
theorem hammingDist_triangle (a b c : Word m) :
    hammingDist a c ≤ hammingDist a b + hammingDist b c := by
  unfold hammingDist
  calc (Finset.univ.filter (fun i => a i ≠ c i)).card
      ≤ (Finset.univ.filter (fun i => a i ≠ b i) ∪
         Finset.univ.filter (fun i => b i ≠ c i)).card := by
        apply Finset.card_le_card
        intro i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        intro hac
        by_contra h
        push_neg at h
        exact hac (h.1.symm ▸ h.2)
    _ ≤ (Finset.univ.filter (fun i => a i ≠ b i)).card +
        (Finset.univ.filter (fun i => b i ≠ c i)).card :=
      Finset.card_union_le _ _

/-- Hamming distance = popcount of XOR.
    def:pom-defect-xor-metric -/
theorem hammingDist_eq_popcount_xor (a b : Word m) :
    hammingDist a b = popcount (xorWord a b) := by
  unfold hammingDist popcount wordSupport
  congr 1
  apply Finset.filter_congr
  intro i _
  simp only [xorWord_apply]
  cases a i <;> cases b i <;> simp

/-- Hamming distance is zero iff words are equal (non-degeneracy).
    def:pom-hamming-metric -/
theorem hammingDist_eq_zero_iff {a b : Word m} :
    hammingDist a b = 0 ↔ a = b := by
  constructor
  · intro h
    unfold hammingDist at h
    rw [Finset.card_eq_zero] at h
    funext i
    by_contra hne
    have : i ∈ Finset.univ.filter (fun j => a j ≠ b j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    rw [h] at this; simp at this
  · intro h; rw [h]; exact hammingDist_self

-- ══════════════════════════════════════════════════════════════
-- Phase 208: Complement distance
-- ══════════════════════════════════════════════════════════════

/-- d(w, complement w) = m. Every bit flipped.
    prop:fold-fiber-count-reciprocity -/
theorem hammingDist_complement (w : Word m) :
    hammingDist w (complement w) = m := by
  unfold hammingDist
  have h : Finset.univ.filter (fun i : Fin m => w i ≠ complement w i) = Finset.univ := by
    ext i; simp [complement]
  rw [h, Finset.card_univ, Fintype.card_fin]

-- ══════════════════════════════════════════════════════════════
-- Phase 221: Hamming distance bounded by popcount sum
-- ══════════════════════════════════════════════════════════════

/-- Hamming distance ≤ sum of popcounts: d(a,b) ≤ popcount(a) + popcount(b).
    If both a[i]=false and b[i]=false then a[i]=b[i], so differing positions are
    contained in support(a) ∪ support(b).
    thm:pom-hamming-popcount-bound -/
theorem hammingDist_le_popcount_add (a b : Word m) :
    hammingDist a b ≤ popcount a + popcount b := by
  unfold hammingDist popcount wordSupport
  calc (Finset.univ.filter (fun i => a i ≠ b i)).card
      ≤ (Finset.univ.filter (fun i : Fin m => a i = true) ∪
         Finset.univ.filter (fun i : Fin m => b i = true)).card := by
        apply Finset.card_le_card
        intro i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        intro hne
        cases ha : a i <;> cases hb : b i <;> simp_all
    _ ≤ (Finset.univ.filter (fun i : Fin m => a i = true)).card +
        (Finset.univ.filter (fun i : Fin m => b i = true)).card :=
      Finset.card_union_le _ _

-- ══════════════════════════════════════════════════════════════
-- Phase 230: Hamming distance from all-false = popcount
-- ══════════════════════════════════════════════════════════════

/-- d(allFalse, w) = popcount(w). thm:pom-fibcube-eccentricity-closed-form -/
theorem hammingDist_allFalse_eq_popcount (w : Word m) :
    hammingDist (fun _ => false) w = popcount w := by
  simp only [hammingDist, popcount, wordSupport]
  congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases w i <;> simp

end Omega

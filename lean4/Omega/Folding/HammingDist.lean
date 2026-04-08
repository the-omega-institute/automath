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

-- ══════════════════════════════════════════════════════════════
-- Phase R11: Fibonacci cube diameter
-- ══════════════════════════════════════════════════════════════

/-- The even-indexed alternating word: 101010... -/
def alternatingEven (m : Nat) : Word m := fun i => decide (i.val % 2 = 0)

/-- The odd-indexed alternating word: 010101... -/
def alternatingOdd (m : Nat) : Word m := fun i => decide (i.val % 2 = 1)

/-- alternatingEven has no adjacent 11 pattern.
    thm:pom-fibcube-eccentricity-closed-form -/
theorem no11_alternatingEven (m : Nat) : No11 (alternatingEven m) := by
  intro i hi hi1
  simp only [alternatingEven, get] at hi hi1
  split at hi <;> split at hi1 <;> simp_all
  omega

/-- alternatingOdd has no adjacent 11 pattern.
    thm:pom-fibcube-eccentricity-closed-form -/
theorem no11_alternatingOdd (m : Nat) : No11 (alternatingOdd m) := by
  intro i hi hi1
  simp only [alternatingOdd, get] at hi hi1
  split at hi <;> split at hi1 <;> simp_all
  omega

/-- Hamming distance between alternatingEven and alternatingOdd is m.
    thm:pom-fibcube-eccentricity-closed-form -/
theorem hammingDist_alternating (m : Nat) :
    hammingDist (alternatingEven m) (alternatingOdd m) = m := by
  simp only [hammingDist, alternatingEven, alternatingOdd]
  have : Finset.univ.filter (fun i : Fin m =>
      decide (i.val % 2 = 0) ≠ decide (i.val % 2 = 1)) = Finset.univ := by
    ext i; simp; omega
  rw [this, Finset.card_univ, Fintype.card_fin]

/-- The Fibonacci cube Γ_m has diameter m (achieved by alternating words).
    thm:pom-fibcube-eccentricity-closed-form -/
theorem fibcubeDiam_eq (m : Nat) (_hm : 1 ≤ m) :
    ∃ (a b : X m), hammingDist a.1 b.1 = m :=
  ⟨⟨alternatingEven m, no11_alternatingEven m⟩,
   ⟨alternatingOdd m, no11_alternatingOdd m⟩,
   hammingDist_alternating m⟩

/-- Hamming distance decomposes under snoc.
    thm:pom-fibcube-eccentricity-closed-form -/
theorem hammingDist_snoc (a c : Word m) (b1 b2 : Bool) :
    hammingDist (snoc a b1) (snoc c b2) =
    hammingDist a c + if b1 = b2 then 0 else 1 := by
  simp only [hammingDist]
  -- Use Fin.lastCases-style split: positions < m use truncation, position m uses last bit
  -- Split filter into {i < m} and {i = m}
  have hsplit : (Finset.univ : Finset (Fin (m + 1))).filter
      (fun i => snoc a b1 i ≠ snoc c b2 i) =
    (Finset.univ.filter (fun i : Fin (m + 1) => i.val < m ∧ snoc a b1 i ≠ snoc c b2 i)) ∪
    (Finset.univ.filter (fun i : Fin (m + 1) => i.val = m ∧ snoc a b1 i ≠ snoc c b2 i)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h
      by_cases hi : i.val < m
      · left; exact ⟨hi, h⟩
      · right; exact ⟨by omega, h⟩
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
  rw [hsplit, Finset.card_union_of_disjoint (by
    apply Finset.disjoint_filter.mpr; intro i _ ⟨h1, _⟩ ⟨h2, _⟩; omega)]
  congr 1
  · -- Positions < m: snoc a b1 i = a ⟨i, _⟩ and snoc c b2 i = c ⟨i, _⟩
    -- Map Fin m → Fin (m+1) via castSucc
    rw [show (Finset.univ.filter (fun i : Fin (m + 1) =>
        i.val < m ∧ snoc a b1 i ≠ snoc c b2 i)) =
      (Finset.univ.filter (fun j : Fin m => a j ≠ c j)).map (Fin.castSuccEmb (n := m)) from by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
          Fin.castSuccEmb]
        constructor
        · intro ⟨him, hne⟩
          exact ⟨⟨i.val, him⟩, by simp [snoc, him] at hne; exact hne, Fin.ext rfl⟩
        · rintro ⟨j, hj, rfl⟩; exact ⟨j.isLt, by simp [snoc, j.isLt, hj]⟩]
    exact Finset.card_map _
  · -- Position m: b1 ≠ b2 iff last bits differ
    by_cases hb : b1 = b2
    · simp only [hb, ite_true]
      apply Finset.card_eq_zero.mpr
      simp only [Finset.filter_eq_empty_iff]
      intro i _; simp only [not_and]; intro him
      simp [snoc, show ¬i.val < m from by omega]
    · simp only [hb, ite_false]
      have : (Finset.univ.filter (fun i : Fin (m + 1) =>
          i.val = m ∧ snoc a b1 i ≠ snoc c b2 i)) = {⟨m, by omega⟩} := by
        apply Finset.ext; intro i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro ⟨him, _⟩; exact Fin.ext him
        · intro h; subst h; exact ⟨rfl, by simp [snoc, hb]⟩
      rw [this, Finset.card_singleton]

-- ══════════════════════════════════════════════════════════════
-- Phase R56: Defect triangle inequality
-- ══════════════════════════════════════════════════════════════

/-- Popcount of xor is bounded by sum of popcounts.
    lem:popcount-xor-triangle -/
theorem popcount_xorWord_le (a b : Word m) :
    popcount (xorWord a b) ≤ popcount a + popcount b := by
  rw [← hammingDist_eq_popcount_xor]
  exact hammingDist_le_popcount_add a b

/-- Restricting a word cannot increase its popcount.
    lem:popcount-restrict-le -/
theorem popcount_restrictWord_le (h : m ≤ n) (w : Word n) :
    popcount (restrictWord h w) ≤ popcount w := by
  simp only [popcount_eq_count_true]
  set embed := fun i : Fin m => (⟨i.1, Nat.lt_of_lt_of_le i.2 h⟩ : Fin n)
  set S := Finset.univ.filter (fun i : Fin m => restrictWord h w i = true)
  set T := Finset.univ.filter (fun i : Fin n => w i = true)
  have hinj : Function.Injective embed := by
    intro a b hab
    simp only [embed, Fin.mk.injEq] at hab
    exact Fin.ext hab
  have hsub : S.image embed ⊆ T := by
    intro j hj
    simp only [S, T, embed, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    obtain ⟨i, hi, rfl⟩ := hj
    exact hi
  calc S.card = (S.image embed).card := (Finset.card_image_of_injective S hinj).symm
    _ ≤ T.card := Finset.card_le_card hsub

/-- Global defect triangle inequality: the defect across a composite resolution gap
    is bounded by the sum of defects at each level.
    prop:fold-defect-triangle -/
theorem globalDefect_triangle (hmk : m ≤ k) (hkn : k ≤ n) (ω : Word n) :
    popcount (globalDefect (Nat.le_trans hmk hkn) ω)
    ≤ popcount (globalDefect hmk (restrictWord hkn ω))
      + popcount (globalDefect hkn ω) := by
  rw [globalDefect_compose hmk hkn ω]
  calc popcount (xorWord (globalDefect hmk (restrictWord hkn ω))
          (restrictWord hmk (globalDefect hkn ω)))
      ≤ popcount (globalDefect hmk (restrictWord hkn ω))
        + popcount (restrictWord hmk (globalDefect hkn ω)) :=
          popcount_xorWord_le _ _
    _ ≤ popcount (globalDefect hmk (restrictWord hkn ω))
        + popcount (globalDefect hkn ω) := by
          apply Nat.add_le_add_left
          exact popcount_restrictWord_le hmk _

/-- Paper: defect cocycle package combining xor decomposition and popcount inequality.
    prop:fold-defect-cocycle -/
theorem paper_fold_defect_cocycle (hmk : m ≤ k) (hkn : k ≤ n) (ω : Word n) :
    globalDefect (Nat.le_trans hmk hkn) ω =
      xorWord (globalDefect hmk (restrictWord hkn ω))
        (restrictWord hmk (globalDefect hkn ω)) ∧
    popcount (globalDefect (Nat.le_trans hmk hkn) ω) ≤
      popcount (globalDefect hmk (restrictWord hkn ω)) + popcount (globalDefect hkn ω) := by
  exact ⟨globalDefect_compose hmk hkn ω, globalDefect_triangle hmk hkn ω⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R60
-- ══════════════════════════════════════════════════════════════

/-- Popcount of complement plus popcount equals word length.
    prop:pom-popcount-complement -/
theorem popcount_complement (w : Word m) :
    popcount (complement w) + popcount w = m := by
  unfold complement
  exact popcount_not w

-- ══════════════════════════════════════════════════════════════
-- Phase R132: Hamming weight distribution of X_6
-- ══════════════════════════════════════════════════════════════

/-- Hamming weight layer count at resolution m.
    cor:fold6-weyl-two-orbit-compression -/
def cHammingWeightLayer (m k : Nat) : Nat :=
  (@Finset.univ (X m) (fintypeX m)).filter (fun x => popcount x.1 = k) |>.card

/-- cor:fold6-weyl-two-orbit-compression -/
theorem cHammingWeightLayer_6_0 : cHammingWeightLayer 6 0 = 1 := by native_decide
/-- cor:fold6-weyl-two-orbit-compression -/
theorem cHammingWeightLayer_6_1 : cHammingWeightLayer 6 1 = 6 := by native_decide
/-- cor:fold6-weyl-two-orbit-compression -/
theorem cHammingWeightLayer_6_2 : cHammingWeightLayer 6 2 = 10 := by native_decide
/-- cor:fold6-weyl-two-orbit-compression -/
theorem cHammingWeightLayer_6_3 : cHammingWeightLayer 6 3 = 4 := by native_decide

/-- X_6 Hamming weight distribution: layers of size 1,6,10,4 (popcount 0..3).
    No11 constraint limits popcount to at most ⌊(m+1)/2⌋ = 3 for m=6.
    cor:fold6-weyl-two-orbit-compression -/
theorem X6_hammingWeight_distribution :
    cHammingWeightLayer 6 0 = 1 ∧ cHammingWeightLayer 6 1 = 6 ∧
    cHammingWeightLayer 6 2 = 10 ∧ cHammingWeightLayer 6 3 = 4 :=
  ⟨cHammingWeightLayer_6_0, cHammingWeightLayer_6_1,
   cHammingWeightLayer_6_2, cHammingWeightLayer_6_3⟩

/-- Hamming weight layer sum = |X_6| = 21.
    cor:fold6-weyl-two-orbit-compression -/
theorem X6_hammingWeight_total :
    cHammingWeightLayer 6 0 + cHammingWeightLayer 6 1 +
    cHammingWeightLayer 6 2 + cHammingWeightLayer 6 3 = 21 := by
  rw [cHammingWeightLayer_6_0, cHammingWeightLayer_6_1,
    cHammingWeightLayer_6_2, cHammingWeightLayer_6_3]

/-- Paper: cor:fold6-weyl-two-orbit-compression (Hamming distribution) -/
theorem paper_X6_hammingWeight_distribution :
    cHammingWeightLayer 6 0 = 1 ∧ cHammingWeightLayer 6 1 = 6 ∧
    cHammingWeightLayer 6 2 = 10 ∧ cHammingWeightLayer 6 3 = 4 :=
  X6_hammingWeight_distribution

/-- cMinStableHammingDist 5 = 1.
    def:min-stable-hamming-dist -/
theorem cMinStableHammingDist_five : cMinStableHammingDist 5 = 1 := by native_decide

/-- cMinStableHammingDist 6 = 1.
    def:min-stable-hamming-dist -/
theorem cMinStableHammingDist_six : cMinStableHammingDist 6 = 1 := by native_decide

/-- cMinStableHammingDist 7 = 1.
    def:min-stable-hamming-dist -/
theorem cMinStableHammingDist_seven : cMinStableHammingDist 7 = 1 := by native_decide

/-- cMinStableHammingDist 8 = 1.
    def:min-stable-hamming-dist -/
theorem cMinStableHammingDist_eight : cMinStableHammingDist 8 = 1 := by native_decide

/-- Paper package: minimum stable Hamming distance is constant 1 for m = 2..8.
    def:min-stable-hamming-dist -/
theorem paper_cMinStableHammingDist_constant_one_2_to_8 :
    cMinStableHammingDist 2 = 1 ∧
    cMinStableHammingDist 3 = 1 ∧
    cMinStableHammingDist 4 = 1 ∧
    cMinStableHammingDist 5 = 1 ∧
    cMinStableHammingDist 6 = 1 ∧
    cMinStableHammingDist 7 = 1 ∧
    cMinStableHammingDist 8 = 1 :=
  ⟨cMinStableHammingDist_two, cMinStableHammingDist_three, cMinStableHammingDist_four,
   cMinStableHammingDist_five, cMinStableHammingDist_six,
   cMinStableHammingDist_seven, cMinStableHammingDist_eight⟩

end Omega

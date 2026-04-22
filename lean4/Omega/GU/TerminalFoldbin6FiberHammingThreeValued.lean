import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6MinReturnDelay

namespace Omega.GU

open scoped symmDiff

/-- The support set of the `6`-bit binary expansion attached to a natural number. -/
def terminal_foldbin6_fiber_hamming_three_valued_support (n : Nat) : Finset (Fin 6) :=
  Omega.wordSupport (Omega.intToWord 6 n)

/-- The preimage set of a window-`6` BinFold fiber. -/
def terminal_foldbin6_fiber_hamming_three_valued_preimages (x : Omega.X 6) : Finset Nat :=
  (Finset.range 64).filter fun n => Omega.cBinFold 6 n = x

/-- The family of supports carried by a window-`6` BinFold fiber. -/
def terminal_foldbin6_fiber_hamming_three_valued_supports (x : Omega.X 6) :
    Finset (Finset (Fin 6)) :=
  (terminal_foldbin6_fiber_hamming_three_valued_preimages x).image
    terminal_foldbin6_fiber_hamming_three_valued_support

private lemma terminal_foldbin6_fiber_hamming_three_valued_values (x : Omega.X 6) :
    Omega.cBinFiberMinHamming 6 x = 2 ∨
      Omega.cBinFiberMinHamming 6 x = 3 ∨
      Omega.cBinFiberMinHamming 6 x = 5 := by
  let s2 : Finset (Omega.X 6) := (@Finset.univ (Omega.X 6) (Omega.fintypeX 6)).filter
    (fun y => Omega.cBinFiberMinHamming 6 y = 2)
  let s3 : Finset (Omega.X 6) := (@Finset.univ (Omega.X 6) (Omega.fintypeX 6)).filter
    (fun y => Omega.cBinFiberMinHamming 6 y = 3)
  let s5 : Finset (Omega.X 6) := (@Finset.univ (Omega.X 6) (Omega.fintypeX 6)).filter
    (fun y => Omega.cBinFiberMinHamming 6 y = 5)
  have hs23 : Disjoint s2 s3 := by
    rw [Finset.disjoint_left]
    intro y hy2 hy3
    simp only [s2, s3, Finset.mem_filter, Finset.mem_univ, true_and] at hy2 hy3
    simp [hy2] at hy3
  have hs25 : Disjoint s2 s5 := by
    rw [Finset.disjoint_left]
    intro y hy2 hy5
    simp only [s2, s5, Finset.mem_filter, Finset.mem_univ, true_and] at hy2 hy5
    simp [hy2] at hy5
  have hs35 : Disjoint s3 s5 := by
    rw [Finset.disjoint_left]
    intro y hy3 hy5
    simp only [s3, s5, Finset.mem_filter, Finset.mem_univ, true_and] at hy3 hy5
    simp [hy3] at hy5
  have hs235 : Disjoint (s2 ∪ s3) s5 := by
    rw [Finset.disjoint_left]
    intro y hy23 hy5
    rcases Finset.mem_union.mp hy23 with hy2 | hy3
    · exact (Finset.disjoint_left.mp hs25 hy2) hy5
    · exact (Finset.disjoint_left.mp hs35 hy3) hy5
  have hs2 : s2.card = 13 := by
    change Omega.cBinFiberMinHammingHist 6 2 = 13
    exact Omega.binFiber6_minHamming_hist_2
  have hs3 : s3.card = 6 := by
    change Omega.cBinFiberMinHammingHist 6 3 = 6
    exact Omega.binFiber6_minHamming_hist_3
  have hs5 : s5.card = 2 := by
    change Omega.cBinFiberMinHammingHist 6 5 = 2
    exact Omega.binFiber6_minHamming_hist_5
  have hcard : ((s2 ∪ s3) ∪ s5).card = Fintype.card (Omega.X 6) := by
    calc
      ((s2 ∪ s3) ∪ s5).card = (s2 ∪ s3).card + s5.card := Finset.card_union_of_disjoint hs235
      _ = s2.card + s3.card + s5.card := by rw [Finset.card_union_of_disjoint hs23]
      _ = 13 + 6 + 2 := by rw [hs2, hs3, hs5]
      _ = Fintype.card (Omega.X 6) := by
            rw [Omega.X.card_eq_fib]
            native_decide
  have hsubset : ((s2 ∪ s3) ∪ s5) ⊆ (Finset.univ : Finset (Omega.X 6)) := by
    intro y hy
    simp
  have hunion : ((s2 ∪ s3) ∪ s5) = (Finset.univ : Finset (Omega.X 6)) := by
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [Finset.card_univ, ← hcard]
  have hx : x ∈ ((s2 ∪ s3) ∪ s5) := by
    rw [hunion]
    simp
  rcases Finset.mem_union.mp hx with hx23 | hx5
  · rcases Finset.mem_union.mp hx23 with hx2 | hx3
    · exact Or.inl ((Finset.mem_filter.mp hx2).2)
    · exact Or.inr <| Or.inl ((Finset.mem_filter.mp hx3).2)
  · exact Or.inr <| Or.inr ((Finset.mem_filter.mp hx5).2)

private theorem terminal_foldbin6_fiber_hamming_three_valued_support_injective_on_range64
    {a b : Nat} (ha : a < 64) (hb : b < 64)
    (hab :
      terminal_foldbin6_fiber_hamming_three_valued_support a =
        terminal_foldbin6_fiber_hamming_three_valued_support b) :
    a = b := by
  have hword : Omega.intToWord 6 a = Omega.intToWord 6 b := by
    calc
      Omega.intToWord 6 a =
          Omega.indSetToWord
            (terminal_foldbin6_fiber_hamming_three_valued_support a) := by
              symm
              exact Omega.indSetToWord_wordSupport (Omega.intToWord 6 a)
      _ =
          Omega.indSetToWord
            (terminal_foldbin6_fiber_hamming_three_valued_support b) := by
              rw [hab]
      _ = Omega.intToWord 6 b := by
            exact Omega.indSetToWord_wordSupport (Omega.intToWord 6 b)
  have hbounded :
      ∀ m n : Fin 64, Omega.intToWord 6 m.1 = Omega.intToWord 6 n.1 → m = n := by
    native_decide
  exact Fin.ext_iff.mp (hbounded ⟨a, ha⟩ ⟨b, hb⟩ hword)

private theorem terminal_foldbin6_fiber_hamming_three_valued_hamming_eq_symmDiff_card (a b : Nat) :
    Omega.hammingDist (Omega.intToWord 6 a) (Omega.intToWord 6 b) =
      ((terminal_foldbin6_fiber_hamming_three_valued_support a) ∆
        (terminal_foldbin6_fiber_hamming_three_valued_support b)).card := by
  have hset :
      (Finset.univ.filter
          (fun i : Fin 6 => Omega.intToWord 6 a i ≠ Omega.intToWord 6 b i)) =
        (terminal_foldbin6_fiber_hamming_three_valued_support a) ∆
          (terminal_foldbin6_fiber_hamming_three_valued_support b) := by
    ext i
    simp [terminal_foldbin6_fiber_hamming_three_valued_support, Omega.wordSupport,
      Finset.mem_symmDiff]
    cases Omega.intToWord 6 a i <;> cases Omega.intToWord 6 b i <;> simp
  simpa [Omega.hammingDist] using congrArg Finset.card hset

private lemma terminal_foldbin6_fiber_hamming_three_valued_compl_card_le_one
    (s : Finset (Fin 6)) (hs : 5 ≤ s.card) : (Finset.univ \ s).card ≤ 1 := by
  have hcard :
      (Finset.univ \ s).card + s.card = Fintype.card (Fin 6) := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
  have hfin : Fintype.card (Fin 6) = 6 := by
    simp
  omega

private lemma terminal_foldbin6_fiber_hamming_three_valued_symmDiff_subset_compl_union
    (s t : Finset (Fin 6)) : s ∆ t ⊆ (Finset.univ \ s) ∪ (Finset.univ \ t) := by
  intro i hi
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
  simp only [Finset.mem_symmDiff] at hi
  rcases hi with h | h <;> simp [h.2]

private lemma terminal_foldbin6_fiber_hamming_three_valued_symmDiff_card_le_two
    (s t : Finset (Fin 6)) (hs : 5 ≤ s.card) (ht : 5 ≤ t.card) : (s ∆ t).card ≤ 2 := by
  have hs' := terminal_foldbin6_fiber_hamming_three_valued_compl_card_le_one s hs
  have ht' := terminal_foldbin6_fiber_hamming_three_valued_compl_card_le_one t ht
  calc
    (s ∆ t).card ≤ ((Finset.univ \ s) ∪ (Finset.univ \ t)).card := by
      exact Finset.card_le_card
        (terminal_foldbin6_fiber_hamming_three_valued_symmDiff_subset_compl_union s t)
    _ ≤ (Finset.univ \ s).card + (Finset.univ \ t).card := Finset.card_union_le _ _
    _ ≤ 1 + 1 := by omega
    _ = 2 := by norm_num

private lemma terminal_foldbin6_fiber_hamming_three_valued_translate_symmDiff
    (a b c : Finset (Fin 6)) : (a ∆ b) ∆ (a ∆ c) = b ∆ c := by
  calc
    (a ∆ b) ∆ (a ∆ c) = b ∆ (a ∆ (a ∆ c)) := by
      rw [symmDiff_comm a b, symmDiff_assoc]
    _ = b ∆ c := by
      rw [symmDiff_symmDiff_cancel_left]

private theorem terminal_foldbin6_fiber_hamming_three_valued_delta5_implies_twofold
    (C : Finset (Finset (Fin 6))) (hC_two : 2 ≤ C.card)
    (hpair : ∀ s ∈ C, ∀ t ∈ C, s ≠ t → 5 ≤ (s ∆ t).card) :
    C.card = 2 := by
  have hC_le_two : C.card ≤ 2 := by
    by_contra hC_not_le_two
    have hC_three : 2 < C.card := by
      omega
    rcases (Finset.two_lt_card.mp hC_three) with ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
    have hab5 : 5 ≤ (a ∆ b).card := hpair a ha b hb hab
    have hac5 : 5 ≤ (a ∆ c).card := hpair a ha c hc hac
    have hsmall :
        ((a ∆ b) ∆ (a ∆ c)).card ≤ 2 :=
      terminal_foldbin6_fiber_hamming_three_valued_symmDiff_card_le_two (a ∆ b) (a ∆ c) hab5 hac5
    have hsmall' : (b ∆ c).card ≤ 2 := by
      simpa [terminal_foldbin6_fiber_hamming_three_valued_translate_symmDiff a b c] using hsmall
    have hbc5 : 5 ≤ (b ∆ c).card := hpair b hb c hc hbc
    omega
  exact le_antisymm hC_le_two hC_two

/-- Paper label: `thm:terminal-foldbin6-fiber-hamming-three-valued`. -/
theorem paper_terminal_foldbin6_fiber_hamming_three_valued (x : Omega.X 6) :
    Omega.cBinFiberMinHamming 6 x ∈ ({2, 3, 5} : Finset Nat) ∧
      (Omega.cBinFiberMinHamming 6 x = 5 →
        (((Finset.range 64).filter fun n => Omega.cBinFold 6 n = x).card = 2)) := by
  refine ⟨?_, ?_⟩
  · rcases terminal_foldbin6_fiber_hamming_three_valued_values x with h2 | h3 | h5
    · simp [h2]
    · simp [h3]
    · simp [h5]
  · intro hx5
    let P := terminal_foldbin6_fiber_hamming_three_valued_preimages x
    let C := terminal_foldbin6_fiber_hamming_three_valued_supports x
    have hcardC : C.card = P.card := by
      dsimp [C, terminal_foldbin6_fiber_hamming_three_valued_supports]
      rw [Finset.card_image_of_injOn]
      intro a ha b hb hab
      exact terminal_foldbin6_fiber_hamming_three_valued_support_injective_on_range64
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
    have hP_two : 2 ≤ P.card := by
      have hmult : Omega.cBinFiberMult 6 x = P.card := by
        dsimp [P, terminal_foldbin6_fiber_hamming_three_valued_preimages]
        simp [Omega.cBinFiberMult]
      by_contra hlt
      have hsmall : P.card = 0 ∨ P.card = 1 := by omega
      rcases hsmall with hzero | hone
      · have hxmem :
            x ∈ ((@Finset.univ (Omega.X 6) (Omega.fintypeX 6)).filter
              (fun y => Omega.cBinFiberMult 6 y = 0)) := by
          simp [hmult, hzero]
        have hpos :
            0 < ((@Finset.univ (Omega.X 6) (Omega.fintypeX 6)).filter
              (fun y => Omega.cBinFiberMult 6 y = 0)).card := by
          exact Finset.card_pos.mpr ⟨x, hxmem⟩
        have hhist : ((@Finset.univ (Omega.X 6) (Omega.fintypeX 6)).filter
            (fun y => Omega.cBinFiberMult 6 y = 0)).card = 0 := by
          simpa [Omega.cBinFiberHist] using Omega.cBinFiberHist_6_0
        omega
      · have hxmem :
            x ∈ ((@Finset.univ (Omega.X 6) (Omega.fintypeX 6)).filter
              (fun y => Omega.cBinFiberMult 6 y = 1)) := by
          simp [hmult, hone]
        have hpos :
            0 < ((@Finset.univ (Omega.X 6) (Omega.fintypeX 6)).filter
              (fun y => Omega.cBinFiberMult 6 y = 1)).card := by
          exact Finset.card_pos.mpr ⟨x, hxmem⟩
        have hhist : ((@Finset.univ (Omega.X 6) (Omega.fintypeX 6)).filter
            (fun y => Omega.cBinFiberMult 6 y = 1)).card = 0 := by
          simpa [Omega.cBinFiberHist] using Omega.cBinFiberHist_6_1
        omega
    have hC_two : 2 ≤ C.card := by
      simpa [hcardC] using hP_two
    have hpair :
        ∀ s ∈ C, ∀ t ∈ C, s ≠ t → 5 ≤ (s ∆ t).card := by
      intro s hs t ht hst
      rcases Finset.mem_image.mp hs with ⟨a, haP, rfl⟩
      rcases Finset.mem_image.mp ht with ⟨b, hbP, rfl⟩
      have ha64 : a < 64 := Finset.mem_range.mp (Finset.mem_filter.mp haP).1
      have hb64 : b < 64 := Finset.mem_range.mp (Finset.mem_filter.mp hbP).1
      have habne : a ≠ b := by
        intro hab
        apply hst
        simp [hab]
      have hsame : Omega.cBinFold 6 a = Omega.cBinFold 6 b := by
        exact (Finset.mem_filter.mp haP).2.trans ((Finset.mem_filter.mp hbP).2.symm)
      let a' : Fin 64 := ⟨a, ha64⟩
      let b' : Fin 64 := ⟨b, hb64⟩
      have hminle :
          Omega.cBinFiberMinHamming 6 x ≤
            Omega.hammingDist (Omega.intToWord 6 a) (Omega.intToWord 6 b) := by
        have hdist :=
          terminalFoldbin6_endpoint_hamming_ge_fiber_min (start := a') (finish := b')
            (by simpa [a', b'] using hsame)
            (by
              intro hab
              apply habne
              exact Fin.ext_iff.mp hab)
        simpa [a', b', (Finset.mem_filter.mp haP).2] using hdist
      have hdist_ge : 5 ≤ Omega.hammingDist (Omega.intToWord 6 a) (Omega.intToWord 6 b) := by
        rw [← hx5]
        exact hminle
      simpa [terminal_foldbin6_fiber_hamming_three_valued_hamming_eq_symmDiff_card a b] using
        hdist_ge
    have hC_card : C.card = 2 :=
      terminal_foldbin6_fiber_hamming_three_valued_delta5_implies_twofold C hC_two hpair
    simpa [P, C, hcardC] using hC_card

end Omega.GU

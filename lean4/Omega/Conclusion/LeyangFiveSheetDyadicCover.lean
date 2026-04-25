import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-level model for the Lee--Yang five-sheet dyadic tower.  Each level is
identified with a sheet in `Fin 5` and a length-`n` alphabet of four dyadic choices. -/
structure conclusion_leyang_five_sheet_dyadic_cover_Data where
  Level : ℕ → Type
  levelFintype : ∀ n, Fintype (Level n)
  truncate : ∀ {m n : ℕ}, m ≤ n → Level n → Level m
  sheetEquiv : ∀ n : ℕ, Level n ≃ Fin 5 × (Fin n → Fin 4)
  truncate_compatible :
    ∀ {m n : ℕ} (h : m ≤ n) (a : Level n),
      sheetEquiv m (truncate h a) =
        ((sheetEquiv n a).1, fun i => (sheetEquiv n a).2 (Fin.castLE h i))

namespace conclusion_leyang_five_sheet_dyadic_cover_Data

/-- One sheet in a finite Lee--Yang level. -/
def sheet (D : conclusion_leyang_five_sheet_dyadic_cover_Data) (n : ℕ) (i : Fin 5) :
    Set (D.Level n) :=
  {a | (D.sheetEquiv n a).1 = i}

/-- The five finite sheets cover each level, and the sheet containing a point is unique. -/
def fiveSheetDisjointCover (D : conclusion_leyang_five_sheet_dyadic_cover_Data) : Prop :=
  ∀ n (a : D.Level n), ∃! i : Fin 5, a ∈ D.sheet n i

/-- The finite degree formula for the five sheets over a two-dimensional dyadic layer. -/
def degreeFormula (D : conclusion_leyang_five_sheet_dyadic_cover_Data) : Prop :=
  ∀ n, letI := D.levelFintype n; Fintype.card (D.Level n) = 5 * 4 ^ n

/-- Transition maps restrict dyadic prefixes and preserve the sheet coordinate. -/
def transitionCompatible (D : conclusion_leyang_five_sheet_dyadic_cover_Data) : Prop :=
  ∀ {m n : ℕ} (h : m ≤ n) (a : D.Level n),
    D.sheetEquiv m (D.truncate h a) =
      ((D.sheetEquiv n a).1, fun i => (D.sheetEquiv n a).2 (Fin.castLE h i))

/-- Dyadic prefix restriction. -/
def dyadicRestrict {m n : ℕ} (h : m ≤ n) (w : Fin n → Fin 4) : Fin m → Fin 4 :=
  fun i => w (Fin.castLE h i)

/-- The inverse limit of the Lee--Yang finite branch tower. -/
def branchInverseLimit (D : conclusion_leyang_five_sheet_dyadic_cover_Data) :=
  {a : ∀ n : ℕ, D.Level n // ∀ m n : ℕ, (h : m ≤ n) → D.truncate h (a n) = a m}

/-- The inverse limit of the two-dimensional dyadic prefix system. -/
def TateModule (_D : conclusion_leyang_five_sheet_dyadic_cover_Data) :=
  {w : ∀ n : ℕ, Fin n → Fin 4 //
    ∀ m n : ℕ, (h : m ≤ n) → dyadicRestrict h (w n) = w m}

/-- The inverse-limit branch object is five copies of the dyadic Tate module. -/
def inverseLimitFiveCopies (D : conclusion_leyang_five_sheet_dyadic_cover_Data) : Prop :=
  Nonempty (D.branchInverseLimit ≃ Fin 5 × D.TateModule)

/-- The finite-level sheet splittings induce the five-copy inverse-limit decomposition. -/
def branchInverseLimitEquiv
    (D : conclusion_leyang_five_sheet_dyadic_cover_Data) :
    D.branchInverseLimit ≃ Fin 5 × D.TateModule where
  toFun a :=
    let dyadicFamily : ∀ n : ℕ, Fin n → Fin 4 := fun n => (D.sheetEquiv n (a.1 n)).2
    let hdyadic :
        ∀ m n : ℕ, (h : m ≤ n) → dyadicRestrict h (dyadicFamily n) = dyadicFamily m := by
      intro m n h
      calc
        dyadicRestrict h (dyadicFamily n)
            = (D.sheetEquiv m (D.truncate h (a.1 n))).2 := by
                simpa [dyadicFamily, dyadicRestrict] using
                  (congrArg Prod.snd (D.truncate_compatible h (a.1 n))).symm
        _ = (D.sheetEquiv m (a.1 m)).2 := by rw [a.2 m n h]
    ((D.sheetEquiv 0 (a.1 0)).1, ⟨dyadicFamily, hdyadic⟩)
  invFun y :=
    ⟨fun n => (D.sheetEquiv n).symm (y.1, y.2.1 n), by
      intro m n h
      apply (D.sheetEquiv m).injective
      calc
        D.sheetEquiv m (D.truncate h ((D.sheetEquiv n).symm (y.1, y.2.1 n)))
            = (y.1, dyadicRestrict h (y.2.1 n)) := by
                simpa [dyadicRestrict] using D.truncate_compatible h ((D.sheetEquiv n).symm
                  (y.1, y.2.1 n))
        _ = (y.1, y.2.1 m) := by rw [y.2.2 m n h]
        _ = D.sheetEquiv m ((D.sheetEquiv m).symm (y.1, y.2.1 m)) := by
              symm
              exact (D.sheetEquiv m).apply_symm_apply (y.1, y.2.1 m)⟩
  left_inv a := by
    apply Subtype.ext
    funext n
    apply (D.sheetEquiv n).injective
    have hsheet :
        (D.sheetEquiv 0 (a.1 0)).1 = (D.sheetEquiv n (a.1 n)).1 := by
      have hcompat := D.truncate_compatible (Nat.zero_le n) (a.1 n)
      rw [a.2 0 n (Nat.zero_le n)] at hcompat
      exact congrArg Prod.fst hcompat
    simp [hsheet]
  right_inv y := by
    rcases y with ⟨sheet, w⟩
    apply Prod.ext
    · simp
    · apply Subtype.ext
      funext n
      funext i
      simp

end conclusion_leyang_five_sheet_dyadic_cover_Data

open conclusion_leyang_five_sheet_dyadic_cover_Data

/-- Paper label: `thm:conclusion-leyang-five-sheet-dyadic-cover`.  The finite sheet
equivalences give the disjoint five-sheet cover and degree formula, their compatibility gives
the transition law, and the same equivalences pass to the inverse limit. -/
theorem paper_conclusion_leyang_five_sheet_dyadic_cover
    (D : conclusion_leyang_five_sheet_dyadic_cover_Data) :
    D.fiveSheetDisjointCover ∧ D.degreeFormula ∧ D.transitionCompatible ∧
      D.inverseLimitFiveCopies := by
  refine ⟨?_, ?_, D.truncate_compatible, ⟨D.branchInverseLimitEquiv⟩⟩
  · intro n a
    refine ⟨(D.sheetEquiv n a).1, rfl, ?_⟩
    intro j hj
    exact hj.symm
  · intro n
    letI := D.levelFintype n
    calc
      Fintype.card (D.Level n) = Fintype.card (Fin 5 × (Fin n → Fin 4)) :=
        Fintype.card_congr (D.sheetEquiv n)
      _ = 5 * 4 ^ n := by simp

end Omega.Conclusion

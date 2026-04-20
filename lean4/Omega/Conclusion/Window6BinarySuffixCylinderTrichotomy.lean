import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.Conclusion

/-- The complete `X₆` catalog, ordered by stable value. -/
def window6All : Finset (Omega.X 6) :=
  {Omega.X.ofNat 6 0, Omega.X.ofNat 6 1, Omega.X.ofNat 6 2, Omega.X.ofNat 6 4, Omega.X.ofNat 6 5,
    Omega.X.ofNat 6 8, Omega.X.ofNat 6 9, Omega.X.ofNat 6 10, Omega.X.ofNat 6 16,
    Omega.X.ofNat 6 17, Omega.X.ofNat 6 18, Omega.X.ofNat 6 20, Omega.X.ofNat 6 21,
    Omega.X.ofNat 6 32, Omega.X.ofNat 6 33, Omega.X.ofNat 6 34, Omega.X.ofNat 6 36,
    Omega.X.ofNat 6 37, Omega.X.ofNat 6 40, Omega.X.ofNat 6 41, Omega.X.ofNat 6 42}

/-- The binary multiplicity-`d` layer inside `X₆`. -/
def window6BinaryLayer (d : ℕ) : Finset (Omega.X 6) :=
  window6All.filter (fun x => Omega.cBinFiberMult 6 x = d)

private def i0 : Fin 6 := ⟨0, by decide⟩
private def i1 : Fin 6 := ⟨1, by decide⟩
private def i2 : Fin 6 := ⟨2, by decide⟩
private def i3 : Fin 6 := ⟨3, by decide⟩
private def i4 : Fin 6 := ⟨4, by decide⟩
private def i5 : Fin 6 := ⟨5, by decide⟩

/-- The rigid `X₄,01` suffix cylinder inside `X₆`. -/
def window6X4Suffix01 : Finset (Omega.X 6) :=
  window6All.filter (fun x => x.1 i4 = false ∧ x.1 i5 = true)

/-- The nonzero `X₃,010` suffix cylinder inside `X₆`. -/
def window6X3NonzeroSuffix010 : Finset (Omega.X 6) :=
  window6All.filter fun x =>
    x.1 i3 = false ∧ x.1 i4 = true ∧ x.1 i5 = false ∧
      ¬ (x.1 i0 = false ∧ x.1 i1 = false ∧ x.1 i2 = false)

/-- The `X₄,00` suffix cylinder inside `X₆`. -/
def window6X4Suffix00 : Finset (Omega.X 6) :=
  window6All.filter (fun x => x.1 i4 = false ∧ x.1 i5 = false)

/-- The exceptional word `000010`. -/
def window6ExceptionalWord : Omega.X 6 :=
  ⟨fun i => decide (i = i4), by
    intro i hi hi1
    by_cases hlt : i < 6
    · interval_cases i <;> simp [Omega.get, i4] at hi hi1
    · simp [Omega.get, hlt] at hi⟩

/-- The `X₅,0` suffix cylinder inside `X₆`. -/
def window6X5Suffix0 : Finset (Omega.X 6) :=
  window6All.filter (fun x => x.1 i5 = false)

/-- Paper-facing window-6 binary suffix-cylinder trichotomy. The binary BinFold layers are the
explicit suffix cylinders `X₄,01`, `(X₃ \ {000}),010`, and `X₄,00` plus the exceptional word
`000010`; moreover `X₆` splits as `X₅,0 ⊔ X₄,01`.
    thm:conclusion-window6-binary-suffix-cylinder-trichotomy -/
theorem paper_conclusion_window6_binary_suffix_cylinder_trichotomy :
    window6BinaryLayer 2 = window6X4Suffix01 ∧
      window6BinaryLayer 3 = window6X3NonzeroSuffix010 ∧
      window6BinaryLayer 4 = window6X4Suffix00 ∪ {window6ExceptionalWord} ∧
      Disjoint window6X5Suffix0 window6X4Suffix01 ∧
      window6X5Suffix0 ∪ window6X4Suffix01 = window6All := by
  native_decide

end Omega.Conclusion

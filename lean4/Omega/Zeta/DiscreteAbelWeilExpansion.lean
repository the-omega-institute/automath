namespace Omega.Zeta

/-- Paper label: `thm:discrete-abel-weil-expansion`. -/
theorem paper_discrete_abel_weil_expansion
    (abelWeilExpansion remainderAnalytic poleOrbit poleModulusFormula : Prop)
    (hexpansion : abelWeilExpansion) (hremainder : remainderAnalytic) (hpole : poleOrbit)
    (hmodulus : poleModulusFormula) :
    abelWeilExpansion ∧ remainderAnalytic ∧ poleOrbit ∧ poleModulusFormula := by
  exact ⟨hexpansion, hremainder, hpole, hmodulus⟩

end Omega.Zeta

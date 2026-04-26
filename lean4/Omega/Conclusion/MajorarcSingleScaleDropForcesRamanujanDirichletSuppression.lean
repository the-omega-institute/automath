namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-majorarc-single-scale-drop-forces-ramanujan-dirichlet-suppression`.
Packages a single-scale spectral drop with its Ramanujan, Dirichlet, and cyclotomic consequences. -/
theorem paper_conclusion_majorarc_single_scale_drop_forces_ramanujan_dirichlet_suppression
    (singleScaleDrop ramanujanSuppression dirichletSuppression cyclotomicSpecialization : Prop)
    (hDrop : singleScaleDrop) (hRam : singleScaleDrop → ramanujanSuppression)
    (hDir : singleScaleDrop → dirichletSuppression)
    (hCyclo : ramanujanSuppression → cyclotomicSpecialization) :
    singleScaleDrop ∧ ramanujanSuppression ∧ dirichletSuppression ∧ cyclotomicSpecialization := by
  refine ⟨hDrop, hRam hDrop, hDir hDrop, hCyclo (hRam hDrop)⟩

end Omega.Conclusion

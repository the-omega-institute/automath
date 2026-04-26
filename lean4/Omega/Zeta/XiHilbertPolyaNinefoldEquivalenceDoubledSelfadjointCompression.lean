namespace Omega.Zeta

/-- Paper label: `thm:xi-hilbert-polya-ninefold-equivalence-doubled-selfadjoint-compression`. -/
theorem paper_xi_hilbert_polya_ninefold_equivalence_doubled_selfadjoint_compression
    (rh roots_interval roots_unit cayley_real caratheodory toeplitz_psd herglotz cmv_unitary
      doubled_selfadjoint : Prop)
    (h12 : rh ↔ roots_interval) (h23 : roots_interval ↔ roots_unit)
    (h34 : roots_unit ↔ cayley_real) (h35 : roots_unit ↔ caratheodory)
    (h56 : caratheodory ↔ toeplitz_psd) (h57 : caratheodory ↔ herglotz)
    (h38 : roots_unit ↔ cmv_unitary) (h29 : roots_interval ↔ doubled_selfadjoint) :
    (rh ↔ roots_interval) ∧ (rh ↔ roots_unit) ∧ (rh ↔ cayley_real) ∧
      (rh ↔ caratheodory) ∧ (rh ↔ toeplitz_psd) ∧ (rh ↔ herglotz) ∧
        (rh ↔ cmv_unitary) ∧ (rh ↔ doubled_selfadjoint) := by
  refine ⟨h12, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h12.trans h23
  · exact h12.trans (h23.trans h34)
  · exact h12.trans (h23.trans h35)
  · exact h12.trans ((h23.trans h35).trans h56)
  · exact h12.trans ((h23.trans h35).trans h57)
  · exact h12.trans (h23.trans h38)
  · exact h12.trans h29

end Omega.Zeta

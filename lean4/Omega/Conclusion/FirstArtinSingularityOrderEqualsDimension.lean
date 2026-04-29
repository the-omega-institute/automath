import Omega.Zeta.XiTerminalZmStokesLeyangSharedArtinRepresentation

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-first-artin-singularity-order-equals-dimension`. In the shared
terminal `S₃` Artin package, the first dominant Artin singularity is recorded by the same
two-dimensional channel, so its order matches the Artin dimension. -/
theorem paper_conclusion_first_artin_singularity_order_equals_dimension :
    let paper_conclusion_first_artin_singularity_order_equals_dimension_order : ℕ :=
      Omega.Zeta.xiTerminalStokesLeyangSharedArtinDimension
    paper_conclusion_first_artin_singularity_order_equals_dimension_order =
        Omega.Zeta.xiTerminalStokesLeyangSharedArtinDimension ∧
      paper_conclusion_first_artin_singularity_order_equals_dimension_order = 2 ∧
      Omega.Zeta.xiTerminalStokesLeyangQuadraticResolventDiscriminant = -111 := by
  have hshared := Omega.Zeta.paper_xi_terminal_zm_stokes_leyang_shared_artin_representation
  rcases hshared with ⟨_, _, _, _, hdim, hdisc⟩
  refine ⟨rfl, ?_, hdisc⟩
  exact hdim

end Omega.Conclusion

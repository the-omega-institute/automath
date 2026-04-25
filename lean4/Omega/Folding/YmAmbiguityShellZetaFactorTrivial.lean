import Omega.Folding.YmAmbiguityShellDag

namespace Omega.Folding

/-- Paper-facing wrapper: once the ambiguity shell is nilpotent, the determinant reduction and
    zeta-closure readout force the ambiguity-shell factor to be trivial.
    thm:Ym-ambiguity-shell-zeta-factor-trivial -/
theorem paper_Ym_ambiguity_shell_zeta_factor_trivial {m : Nat} (hm : 3 <= m)
    (ambNilpotent detReduction edgeZetaEquality intrinsicZetaClosed : Prop)
    (h_nil : ambNilpotent) (h_det : ambNilpotent -> detReduction)
    (h_edge : detReduction -> edgeZetaEquality)
    (h_closed : edgeZetaEquality -> intrinsicZetaClosed) :
    detReduction ∧ edgeZetaEquality ∧ intrinsicZetaClosed := by
  have hpack : ambNilpotent ∧ detReduction ∧ edgeZetaEquality :=
    paper_Ym_ambiguity_shell_dag_wrapper m ambNilpotent detReduction edgeZetaEquality hm
      h_nil h_det (fun hnil => h_edge (h_det hnil))
  rcases hpack with ⟨_, hdet, hedge⟩
  exact ⟨hdet, hedge, h_closed hedge⟩

/-- Lowercase paper-label spelling for the ambiguity-shell zeta factor wrapper.
    thm:Ym-ambiguity-shell-zeta-factor-trivial -/
theorem paper_ym_ambiguity_shell_zeta_factor_trivial {m : Nat} (hm : 3 <= m)
    (ambNilpotent detReduction edgeZetaEquality intrinsicZetaClosed : Prop)
    (h_nil : ambNilpotent) (h_det : ambNilpotent -> detReduction)
    (h_edge : detReduction -> edgeZetaEquality)
    (h_closed : edgeZetaEquality -> intrinsicZetaClosed) :
    detReduction ∧ edgeZetaEquality ∧ intrinsicZetaClosed := by
  exact paper_Ym_ambiguity_shell_zeta_factor_trivial hm ambNilpotent detReduction
    edgeZetaEquality intrinsicZetaClosed h_nil h_det h_edge h_closed

end Omega.Folding

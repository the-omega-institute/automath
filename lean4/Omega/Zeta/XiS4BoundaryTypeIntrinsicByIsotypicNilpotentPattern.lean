import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-s4-boundary-type-intrinsic-by-isotypic-nilpotent-pattern`. -/
theorem paper_xi_s4_boundary_type_intrinsic_by_isotypic_nilpotent_pattern {Boundary : Type}
    (boundaryType : Boundary → Fin 3) (t_eps t_rho2 t_rho3 : Boundary → ℕ)
    (N_eps N_rho2 N_rho3 : Boundary → Prop)
    (h_eps : ∀ b, N_eps b ↔ t_eps b ≠ 0)
    (h_rho2 : ∀ b, N_rho2 b ↔ t_rho2 b ≠ 0)
    (h_rho3 : ∀ b, N_rho3 b ↔ t_rho3 b ≠ 0)
    (h_types : ∀ b,
      (boundaryType b = 0 ↔ t_rho2 b = 2 ∧ t_rho3 b = 0 ∧ t_eps b = 0) ∧
      (boundaryType b = 1 ↔ t_rho3 b = 3 ∧ t_eps b = 0) ∧
      (boundaryType b = 2 ↔ t_eps b = 1 ∧ t_rho2 b = 0 ∧ t_rho3 b = 0)) :
    ∀ b, (boundaryType b = 0 ↔ N_rho2 b ∧ ¬ N_rho3 b ∧ ¬ N_eps b) ∧
      (boundaryType b = 1 ↔ N_rho3 b ∧ ¬ N_eps b) ∧
      (boundaryType b = 2 ↔ N_eps b ∧ ¬ N_rho2 b ∧ ¬ N_rho3 b) := by
  intro b
  rcases h_types b with ⟨h0, h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hb0
      rcases h0.mp hb0 with ⟨hr2, hr3, heps⟩
      refine ⟨?_, ?_, ?_⟩
      · exact (h_rho2 b).mpr (by simp [hr2])
      · intro hn
        exact (h_rho3 b).mp hn (by simp [hr3])
      · intro hn
        exact (h_eps b).mp hn (by simp [heps])
    · rintro ⟨_, hn3, hneps⟩
      generalize hbt : boundaryType b = c
      fin_cases c
      · rfl
      · have htr3 : t_rho3 b = 3 := (h1.mp hbt).1
        exact False.elim (hn3 ((h_rho3 b).mpr (by simp [htr3])))
      · have hteps : t_eps b = 1 := (h2.mp hbt).1
        exact False.elim (hneps ((h_eps b).mpr (by simp [hteps])))
  · constructor
    · intro hb1
      rcases h1.mp hb1 with ⟨hr3, heps⟩
      refine ⟨?_, ?_⟩
      · exact (h_rho3 b).mpr (by simp [hr3])
      · intro hn
        exact (h_eps b).mp hn (by simp [heps])
    · rintro ⟨hn3, hneps⟩
      generalize hbt : boundaryType b = c
      fin_cases c
      · have htr3 : t_rho3 b = 0 := (h0.mp hbt).2.1
        exact False.elim ((h_rho3 b).mp hn3 (by simp [htr3]))
      · rfl
      · have hteps : t_eps b = 1 := (h2.mp hbt).1
        exact False.elim (hneps ((h_eps b).mpr (by simp [hteps])))
  · constructor
    · intro hb2
      rcases h2.mp hb2 with ⟨heps, hr2, hr3⟩
      refine ⟨?_, ?_, ?_⟩
      · exact (h_eps b).mpr (by simp [heps])
      · intro hn
        exact (h_rho2 b).mp hn (by simp [hr2])
      · intro hn
        exact (h_rho3 b).mp hn (by simp [hr3])
    · rintro ⟨hneps, hn2, _⟩
      generalize hbt : boundaryType b = c
      fin_cases c
      · have hr2 : t_rho2 b = 2 := (h0.mp hbt).1
        exact False.elim (hn2 ((h_rho2 b).mpr (by simp [hr2])))
      · have hteps : t_eps b = 0 := (h1.mp hbt).2
        exact False.elim ((h_eps b).mp hneps (by simp [hteps]))
      · rfl

end Omega.Zeta

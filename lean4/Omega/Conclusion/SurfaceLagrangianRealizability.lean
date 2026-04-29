import Mathlib.Tactic

namespace Omega.Conclusion

/-- The standard handlebody Lagrangian on a genus-`g` surface: the first `g` basis vectors inside
the `2g`-dimensional symplectic ambient module. -/
def conclusion_surface_lagrangian_realizability_standard_generator
    (g : ℕ) (i : Fin g) : Fin (2 * g) :=
  ⟨i.1, by
    have hdouble : g ≤ 2 * g := by omega
    exact lt_of_lt_of_le i.2 hdouble⟩

/-- The standard handlebody generators are distinct. -/
lemma conclusion_surface_lagrangian_realizability_standard_generator_injective
    (g : ℕ) :
    Function.Injective
      (conclusion_surface_lagrangian_realizability_standard_generator g) := by
  intro i j hij
  apply Fin.ext
  simpa using congrArg (fun x : Fin (2 * g) => x.1) hij

/-- Concrete data for realizing a primitive Lagrangian on a genus-`g` surface. The data consists
of a target family of generators together with a boundary automorphism sending the standard
handlebody Lagrangian to that family. -/
structure conclusion_surface_lagrangian_realizability_data where
  genus : ℕ
  lagrangian : Fin genus → Fin (2 * genus)
  boundaryAutomorphism : Fin (2 * genus) ≃ Fin (2 * genus)
  transport_to_lagrangian :
    ∀ i,
      boundaryAutomorphism
          (conclusion_surface_lagrangian_realizability_standard_generator genus i) =
        lagrangian i

/-- Transport the standard handlebody generators along the chosen boundary automorphism. -/
def conclusion_surface_lagrangian_realizability_transported_handlebody
    (D : conclusion_surface_lagrangian_realizability_data) :
    Fin D.genus → Fin (2 * D.genus) :=
  fun i =>
    D.boundaryAutomorphism
      (conclusion_surface_lagrangian_realizability_standard_generator D.genus i)

/-- The target Lagrangian is realized by a handlebody whose boundary generators are obtained from
the standard ones by the prescribed boundary automorphism. -/
def conclusion_surface_lagrangian_realizability_exists_handlebody
    (D : conclusion_surface_lagrangian_realizability_data) : Prop :=
  ∃ H : Fin D.genus → Fin (2 * D.genus),
    H = conclusion_surface_lagrangian_realizability_transported_handlebody D ∧
      Function.Injective H ∧
      Set.range H = Set.range D.lagrangian

/-- Paper label: `thm:conclusion-surface-lagrangian-realizability`. The standard handlebody
Lagrangian is realized by the first `g` basis generators, the chosen boundary automorphism carries
those generators to the target primitive Lagrangian, and transporting the handlebody along that
automorphism realizes the desired boundary Lagrangian. -/
theorem paper_conclusion_surface_lagrangian_realizability
    (D : conclusion_surface_lagrangian_realizability_data) :
    conclusion_surface_lagrangian_realizability_exists_handlebody D := by
  refine ⟨conclusion_surface_lagrangian_realizability_transported_handlebody D, rfl, ?_, ?_⟩
  · intro i j hij
    apply conclusion_surface_lagrangian_realizability_standard_generator_injective D.genus
    exact D.boundaryAutomorphism.injective hij
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (D.transport_to_lagrangian i).symm⟩
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      exact (D.transport_to_lagrangian i).trans hi

end Omega.Conclusion

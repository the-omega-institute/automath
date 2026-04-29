import Mathlib.Data.Int.Basic

namespace Omega.POM

/-- Paper label: `cor:pom-schur-trace-frobenius-character-identification`. -/
theorem paper_pom_schur_trace_frobenius_character_identification {Lambda : Type}
    (T f s : Lambda -> Int) (h_trace : forall lam, T lam = f lam * s lam) :
    forall lam, (T lam = f lam * s lam) ∧ (Exists fun k : Int => T lam = f lam * k) := by
  intro lam
  exact ⟨h_trace lam, ⟨s lam, h_trace lam⟩⟩

end Omega.POM

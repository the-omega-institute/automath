import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-curvature-independent-divergent`. Once every bad curvature event
forces an incompatibility, infinitely many bad events force infinitely many incompatibilities. -/
theorem paper_pom_curvature_independent_divergent
    (bad incompatible : Nat → Prop)
    (hbad : ∀ m, bad m → incompatible m)
    (hio : ∀ n, ∃ m, n ≤ m ∧ bad m) :
    ∀ n, ∃ m, n ≤ m ∧ incompatible m := by
  intro n
  rcases hio n with ⟨m, hnm, hm⟩
  exact ⟨m, hnm, hbad m hm⟩

end Omega.POM

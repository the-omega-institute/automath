import Mathlib.Tactic

theorem paper_conclusion_binfold_kappa_gauge_affine_law
    (kappa g errK errG : Nat -> Real) (s c : Real)
    (hkappa : ∀ m, kappa m = (m : Real) * s - c + errK m)
    (hgauge : ∀ m, g m = (m : Real) * s - 1 - c + errG m) :
    ∀ m, g m = kappa m - 1 + (errG m - errK m) := by
  intro m
  rw [hgauge m, hkappa m]
  ring

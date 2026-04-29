import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.POM

open Polynomial

/-- The audited quartic for the `E₈` square-spectrum collapse. -/
noncomputable def pom_e8_square_spectrum_collapse_trace7_quartic : Polynomial ℝ :=
  X ^ 4 - C 7 * X ^ 3 + C 14 * X ^ 2 - C 8 * X + C 1

/-- The first quadratic trace coefficient in the audited factorization. -/
noncomputable def pom_e8_square_spectrum_collapse_trace7_aPlus : ℝ :=
  (7 + Real.sqrt 5) / 2

/-- The second quadratic trace coefficient in the audited factorization. -/
noncomputable def pom_e8_square_spectrum_collapse_trace7_aMinus : ℝ :=
  (7 - Real.sqrt 5) / 2

/-- The first quadratic constant coefficient in the audited factorization. -/
noncomputable def pom_e8_square_spectrum_collapse_trace7_bPlus : ℝ :=
  (3 + Real.sqrt 5) / 2

/-- The second quadratic constant coefficient in the audited factorization. -/
noncomputable def pom_e8_square_spectrum_collapse_trace7_bMinus : ℝ :=
  (3 - Real.sqrt 5) / 2

/-- The discriminant of the first quadratic factor. -/
noncomputable def pom_e8_square_spectrum_collapse_trace7_deltaPlus : ℝ :=
  (15 + 3 * Real.sqrt 5) / 2

/-- The discriminant of the second quadratic factor. -/
noncomputable def pom_e8_square_spectrum_collapse_trace7_deltaMinus : ℝ :=
  (15 - 3 * Real.sqrt 5) / 2

/-- One of the four real `E₈` square-spectrum values. -/
noncomputable def pom_e8_square_spectrum_collapse_trace7_root1 : ℝ :=
  (pom_e8_square_spectrum_collapse_trace7_aPlus +
      Real.sqrt pom_e8_square_spectrum_collapse_trace7_deltaPlus) / 2

/-- One of the four real `E₈` square-spectrum values. -/
noncomputable def pom_e8_square_spectrum_collapse_trace7_root2 : ℝ :=
  (pom_e8_square_spectrum_collapse_trace7_aPlus -
      Real.sqrt pom_e8_square_spectrum_collapse_trace7_deltaPlus) / 2

/-- One of the four real `E₈` square-spectrum values. -/
noncomputable def pom_e8_square_spectrum_collapse_trace7_root3 : ℝ :=
  (pom_e8_square_spectrum_collapse_trace7_aMinus +
      Real.sqrt pom_e8_square_spectrum_collapse_trace7_deltaMinus) / 2

/-- One of the four real `E₈` square-spectrum values. -/
noncomputable def pom_e8_square_spectrum_collapse_trace7_root4 : ℝ :=
  (pom_e8_square_spectrum_collapse_trace7_aMinus -
      Real.sqrt pom_e8_square_spectrum_collapse_trace7_deltaMinus) / 2

/-- The four audited `E₈` square-spectrum values factor the explicit quartic, so Vieta gives the
trace sum `7`.  Paper label: `prop:pom-e8-square-spectrum-collapse-trace7`. -/
theorem paper_pom_e8_square_spectrum_collapse_trace7 :
    pom_e8_square_spectrum_collapse_trace7_quartic =
      (X - C pom_e8_square_spectrum_collapse_trace7_root1) *
        (X - C pom_e8_square_spectrum_collapse_trace7_root2) *
        (X - C pom_e8_square_spectrum_collapse_trace7_root3) *
        (X - C pom_e8_square_spectrum_collapse_trace7_root4) ∧
      pom_e8_square_spectrum_collapse_trace7_root1 +
          pom_e8_square_spectrum_collapse_trace7_root2 +
          pom_e8_square_spectrum_collapse_trace7_root3 +
          pom_e8_square_spectrum_collapse_trace7_root4 = 7 := by
  have hsqrt5_sq : (Real.sqrt 5) ^ 2 = 5 := by
    exact Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 5)
  have hsqrt5_le5 : Real.sqrt 5 ≤ 5 := by
    nlinarith [sq_nonneg (Real.sqrt 5), hsqrt5_sq]
  have hdeltaPlus_nonneg : 0 ≤ pom_e8_square_spectrum_collapse_trace7_deltaPlus := by
    unfold pom_e8_square_spectrum_collapse_trace7_deltaPlus
    positivity
  have hdeltaMinus_nonneg : 0 ≤ pom_e8_square_spectrum_collapse_trace7_deltaMinus := by
    unfold pom_e8_square_spectrum_collapse_trace7_deltaMinus
    nlinarith
  have hpairPlus_sum :
      pom_e8_square_spectrum_collapse_trace7_root1 +
          pom_e8_square_spectrum_collapse_trace7_root2 =
        pom_e8_square_spectrum_collapse_trace7_aPlus := by
    unfold pom_e8_square_spectrum_collapse_trace7_root1
      pom_e8_square_spectrum_collapse_trace7_root2
    ring
  have hpairMinus_sum :
      pom_e8_square_spectrum_collapse_trace7_root3 +
          pom_e8_square_spectrum_collapse_trace7_root4 =
        pom_e8_square_spectrum_collapse_trace7_aMinus := by
    unfold pom_e8_square_spectrum_collapse_trace7_root3
      pom_e8_square_spectrum_collapse_trace7_root4
    ring
  have hpairPlus_prod :
      pom_e8_square_spectrum_collapse_trace7_root1 *
          pom_e8_square_spectrum_collapse_trace7_root2 =
        pom_e8_square_spectrum_collapse_trace7_bPlus := by
    have hdelta_sq :
        (Real.sqrt pom_e8_square_spectrum_collapse_trace7_deltaPlus) ^ 2 =
          pom_e8_square_spectrum_collapse_trace7_deltaPlus := by
      exact Real.sq_sqrt hdeltaPlus_nonneg
    unfold pom_e8_square_spectrum_collapse_trace7_root1
      pom_e8_square_spectrum_collapse_trace7_root2
      pom_e8_square_spectrum_collapse_trace7_aPlus
      pom_e8_square_spectrum_collapse_trace7_bPlus
      pom_e8_square_spectrum_collapse_trace7_deltaPlus at *
    nlinarith
  have hpairMinus_prod :
      pom_e8_square_spectrum_collapse_trace7_root3 *
          pom_e8_square_spectrum_collapse_trace7_root4 =
        pom_e8_square_spectrum_collapse_trace7_bMinus := by
    have hdelta_sq :
        (Real.sqrt pom_e8_square_spectrum_collapse_trace7_deltaMinus) ^ 2 =
          pom_e8_square_spectrum_collapse_trace7_deltaMinus := by
      exact Real.sq_sqrt hdeltaMinus_nonneg
    unfold pom_e8_square_spectrum_collapse_trace7_root3
      pom_e8_square_spectrum_collapse_trace7_root4
      pom_e8_square_spectrum_collapse_trace7_aMinus
      pom_e8_square_spectrum_collapse_trace7_bMinus
      pom_e8_square_spectrum_collapse_trace7_deltaMinus at *
    nlinarith
  have hquadraticPlus :
      (X - C pom_e8_square_spectrum_collapse_trace7_root1) *
          (X - C pom_e8_square_spectrum_collapse_trace7_root2) =
        X ^ 2 - C pom_e8_square_spectrum_collapse_trace7_aPlus * X +
          C pom_e8_square_spectrum_collapse_trace7_bPlus := by
    calc
      (X - C pom_e8_square_spectrum_collapse_trace7_root1) *
          (X - C pom_e8_square_spectrum_collapse_trace7_root2) =
          X ^ 2 -
            X *
              C
                (pom_e8_square_spectrum_collapse_trace7_root1 +
                  pom_e8_square_spectrum_collapse_trace7_root2) +
            C
              (pom_e8_square_spectrum_collapse_trace7_root1 *
                pom_e8_square_spectrum_collapse_trace7_root2) := by
            rw [show X * C
                (pom_e8_square_spectrum_collapse_trace7_root1 +
                  pom_e8_square_spectrum_collapse_trace7_root2) =
                  X * C pom_e8_square_spectrum_collapse_trace7_root1 +
                    X * C pom_e8_square_spectrum_collapse_trace7_root2 by
                  rw [C_add, mul_add]]
            ring_nf
            rw [C_mul]
      _ = X ^ 2 - C pom_e8_square_spectrum_collapse_trace7_aPlus * X +
            C pom_e8_square_spectrum_collapse_trace7_bPlus := by
            rw [hpairPlus_sum, hpairPlus_prod, mul_comm]
  have hquadraticMinus :
      (X - C pom_e8_square_spectrum_collapse_trace7_root3) *
          (X - C pom_e8_square_spectrum_collapse_trace7_root4) =
        X ^ 2 - C pom_e8_square_spectrum_collapse_trace7_aMinus * X +
          C pom_e8_square_spectrum_collapse_trace7_bMinus := by
    calc
      (X - C pom_e8_square_spectrum_collapse_trace7_root3) *
          (X - C pom_e8_square_spectrum_collapse_trace7_root4) =
          X ^ 2 -
            X *
              C
                (pom_e8_square_spectrum_collapse_trace7_root3 +
                  pom_e8_square_spectrum_collapse_trace7_root4) +
            C
              (pom_e8_square_spectrum_collapse_trace7_root3 *
                pom_e8_square_spectrum_collapse_trace7_root4) := by
            rw [show X * C
                (pom_e8_square_spectrum_collapse_trace7_root3 +
                  pom_e8_square_spectrum_collapse_trace7_root4) =
                  X * C pom_e8_square_spectrum_collapse_trace7_root3 +
                    X * C pom_e8_square_spectrum_collapse_trace7_root4 by
                  rw [C_add, mul_add]]
            ring_nf
            rw [C_mul]
      _ = X ^ 2 - C pom_e8_square_spectrum_collapse_trace7_aMinus * X +
            C pom_e8_square_spectrum_collapse_trace7_bMinus := by
            rw [hpairMinus_sum, hpairMinus_prod, mul_comm]
  have ha_sum :
      pom_e8_square_spectrum_collapse_trace7_aPlus +
          pom_e8_square_spectrum_collapse_trace7_aMinus = 7 := by
    unfold pom_e8_square_spectrum_collapse_trace7_aPlus
      pom_e8_square_spectrum_collapse_trace7_aMinus
    ring
  have hb_sum :
      pom_e8_square_spectrum_collapse_trace7_bPlus +
          pom_e8_square_spectrum_collapse_trace7_bMinus = 3 := by
    unfold pom_e8_square_spectrum_collapse_trace7_bPlus
      pom_e8_square_spectrum_collapse_trace7_bMinus
    ring
  have ha_prod :
      pom_e8_square_spectrum_collapse_trace7_aPlus *
          pom_e8_square_spectrum_collapse_trace7_aMinus = 11 := by
    unfold pom_e8_square_spectrum_collapse_trace7_aPlus
      pom_e8_square_spectrum_collapse_trace7_aMinus
    nlinarith
  have hb_prod :
      pom_e8_square_spectrum_collapse_trace7_bPlus *
          pom_e8_square_spectrum_collapse_trace7_bMinus = 1 := by
    unfold pom_e8_square_spectrum_collapse_trace7_bPlus
      pom_e8_square_spectrum_collapse_trace7_bMinus
    nlinarith
  have hab_mixed :
      pom_e8_square_spectrum_collapse_trace7_aPlus *
          pom_e8_square_spectrum_collapse_trace7_bMinus +
        pom_e8_square_spectrum_collapse_trace7_aMinus *
          pom_e8_square_spectrum_collapse_trace7_bPlus = 8 := by
    unfold pom_e8_square_spectrum_collapse_trace7_aPlus
      pom_e8_square_spectrum_collapse_trace7_aMinus
      pom_e8_square_spectrum_collapse_trace7_bPlus
      pom_e8_square_spectrum_collapse_trace7_bMinus
    nlinarith
  have hquartic_factor :
      pom_e8_square_spectrum_collapse_trace7_quartic =
        (X ^ 2 - C pom_e8_square_spectrum_collapse_trace7_aPlus * X +
            C pom_e8_square_spectrum_collapse_trace7_bPlus) *
          (X ^ 2 - C pom_e8_square_spectrum_collapse_trace7_aMinus * X +
            C pom_e8_square_spectrum_collapse_trace7_bMinus) := by
    symm
    calc
      (X ^ 2 - C pom_e8_square_spectrum_collapse_trace7_aPlus * X +
            C pom_e8_square_spectrum_collapse_trace7_bPlus) *
          (X ^ 2 - C pom_e8_square_spectrum_collapse_trace7_aMinus * X +
            C pom_e8_square_spectrum_collapse_trace7_bMinus) =
          X ^ 4 -
            C
                (pom_e8_square_spectrum_collapse_trace7_aPlus +
                  pom_e8_square_spectrum_collapse_trace7_aMinus) *
              X ^ 3 +
            C
                (pom_e8_square_spectrum_collapse_trace7_aPlus *
                    pom_e8_square_spectrum_collapse_trace7_aMinus +
                  (pom_e8_square_spectrum_collapse_trace7_bPlus +
                    pom_e8_square_spectrum_collapse_trace7_bMinus)) *
              X ^ 2 -
            C
                (pom_e8_square_spectrum_collapse_trace7_aPlus *
                    pom_e8_square_spectrum_collapse_trace7_bMinus +
                  pom_e8_square_spectrum_collapse_trace7_aMinus *
                    pom_e8_square_spectrum_collapse_trace7_bPlus) *
              X +
            C
              (pom_e8_square_spectrum_collapse_trace7_bPlus *
                pom_e8_square_spectrum_collapse_trace7_bMinus) := by
            ring_nf
            rw [C_add, C_add, C_add, C_mul, C_mul, C_mul]
            rw [C_add, mul_add, C_mul]
            ring_nf
      _ = pom_e8_square_spectrum_collapse_trace7_quartic := by
            rw [ha_sum, ha_prod, hb_sum, hab_mixed, hb_prod]
            unfold pom_e8_square_spectrum_collapse_trace7_quartic
            ring
  refine ⟨?_, ?_⟩
  · calc
      pom_e8_square_spectrum_collapse_trace7_quartic =
          (X ^ 2 - C pom_e8_square_spectrum_collapse_trace7_aPlus * X +
              C pom_e8_square_spectrum_collapse_trace7_bPlus) *
            (X ^ 2 - C pom_e8_square_spectrum_collapse_trace7_aMinus * X +
              C pom_e8_square_spectrum_collapse_trace7_bMinus) := hquartic_factor
      _ =
          ((X - C pom_e8_square_spectrum_collapse_trace7_root1) *
              (X - C pom_e8_square_spectrum_collapse_trace7_root2)) *
            ((X - C pom_e8_square_spectrum_collapse_trace7_root3) *
              (X - C pom_e8_square_spectrum_collapse_trace7_root4)) := by
            rw [hquadraticPlus, hquadraticMinus]
      _ =
          (X - C pom_e8_square_spectrum_collapse_trace7_root1) *
            (X - C pom_e8_square_spectrum_collapse_trace7_root2) *
            (X - C pom_e8_square_spectrum_collapse_trace7_root3) *
            (X - C pom_e8_square_spectrum_collapse_trace7_root4) := by
            ring
  · calc
      pom_e8_square_spectrum_collapse_trace7_root1 +
          pom_e8_square_spectrum_collapse_trace7_root2 +
          pom_e8_square_spectrum_collapse_trace7_root3 +
          pom_e8_square_spectrum_collapse_trace7_root4 =
          pom_e8_square_spectrum_collapse_trace7_aPlus +
            pom_e8_square_spectrum_collapse_trace7_aMinus := by
              rw [← hpairPlus_sum, ← hpairMinus_sum]
              ring
      _ = 7 := by
            unfold pom_e8_square_spectrum_collapse_trace7_aPlus
              pom_e8_square_spectrum_collapse_trace7_aMinus
            ring

end Omega.POM

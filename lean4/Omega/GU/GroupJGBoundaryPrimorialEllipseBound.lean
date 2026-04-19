import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.Folding.GodelFiniteDictionaryBitlength
import Omega.GU.GodelLorentzAlgebraization
import Omega.GU.JoukowskyAreaPreservingCayley

namespace Omega.GU

/-- The primorial lower bound on the concrete boundary register size transports through the
Joukowsky/Lorentz formulas to the normalized ellipse package: Minkowski identity, hyperbolic
semiaxis parametrization, unit area proxy, and the normalized Cayley parameter.
    prop:group-jg-boundary-primorial-ellipse-bound -/
theorem paper_group_jg_boundary_primorial_ellipse_bound
    (B T : ℕ) (hB : 1 ≤ B) (a : Fin T → ℕ) (ha : ∀ t, 1 ≤ a t ∧ a t ≤ B)
    (hL : 1 < (Omega.Folding.godelCode a : ℝ)) :
    let Lmax := (Omega.Folding.godelCode a : ℝ)
    let Δ := Real.log (Real.sqrt Lmax)
    let A := Real.sqrt Lmax + (Real.sqrt Lmax)⁻¹
    let B' := Real.sqrt Lmax - (Real.sqrt Lmax)⁻¹
    (Omega.Folding.primorial T : ℝ) ≤ Lmax ∧
      A ^ 2 - B' ^ 2 = 4 ∧
      A = 2 * Real.cosh Δ ∧
      B' = 2 * Real.sinh Δ ∧
      normalizedMajorSemiaxis Δ * normalizedMinorSemiaxis Δ = 1 ∧
      Real.pi * normalizedMajorSemiaxis Δ * normalizedMinorSemiaxis Δ = Real.pi ∧
      cayleyComposition Δ 0 ∧
      einsteinAddition Δ 0 := by
  dsimp
  have hPrimNat :
      Omega.Folding.primorial T ≤ Omega.Folding.godelCode a :=
    (Omega.Folding.paper_fold_godel_finite_dictionary_bitlength_theta_TlogT B T hB a ha).1
  have hPrim :
      (Omega.Folding.primorial T : ℝ) ≤ (Omega.Folding.godelCode a : ℝ) := by
    exact_mod_cast hPrimNat
  have hLor :=
    paper_group_jg_godel_lorentz_algebraization (Omega.Folding.godelCode a) hL
  have hCay :=
    paper_group_jg_joukowsky_area_preserving_cayley
      (Real.log (Real.sqrt (Omega.Folding.godelCode a : ℝ))) 0
  rcases hLor with ⟨hMinkowski, hCosh, hSinh⟩
  rcases hCay with ⟨hFamily, hCayley, hEinstein⟩
  rcases hFamily with ⟨hProd, _, _⟩
  refine ⟨hPrim, hMinkowski, hCosh, hSinh, hProd, ?_, hCayley, hEinstein⟩
  calc
    Real.pi * normalizedMajorSemiaxis (Real.log (Real.sqrt (Omega.Folding.godelCode a : ℝ))) *
        normalizedMinorSemiaxis (Real.log (Real.sqrt (Omega.Folding.godelCode a : ℝ)))
        =
        Real.pi *
          (normalizedMajorSemiaxis (Real.log (Real.sqrt (Omega.Folding.godelCode a : ℝ))) *
            normalizedMinorSemiaxis (Real.log (Real.sqrt (Omega.Folding.godelCode a : ℝ)))) := by
          ring
    _ = Real.pi * 1 := by rw [hProd]
    _ = Real.pi := by ring

end Omega.GU

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic

open scoped BigOperators

namespace Omega.Conclusion

/-- Finite Dirichlet window for the Ramanujan atomic coefficients `C_m`. -/
noncomputable def ramanujanAtomicDirichletSeries (atoms : Finset ℕ) (C : ℕ → ℂ) (s : ℕ) : ℂ :=
  atoms.sum fun m => C m / (m : ℂ) ^ s

/-- Finite Dirichlet window for the `q`-axis coefficients `Ψ_q`. -/
noncomputable def qAxisDirichletSeries (qs : Finset ℕ) (Ψ : ℕ → ℂ) (s : ℕ) : ℂ :=
  qs.sum fun q => Ψ q / (q : ℂ) ^ s

/-- Finite divisor-side series after the Ramanujan/Möbius stripping step. -/
def sigmaStrippingDirichletSeries (support : Finset ℕ) (u σ : ℕ → ℂ) : ℂ :=
  support.sum fun n => u n * σ n

/-- Finite-support formal core of
    `thm:conclusion-ramanujan-atomic-qaxis-zeta-stripping`: once the swapped Ramanujan sum has
    been identified with the stripped divisor series and the same divisor series is reorganized as
    the `q`-axis Dirichlet sum, the atomic series is exactly the `q`-axis series with the
    universal `1 / ζ` factor removed. -/
theorem paper_conclusion_ramanujan_atomic_qaxis_zeta_stripping
    (atoms qs support : Finset ℕ) (C Ψ u σ : ℕ → ℂ) (s : ℕ) (ζ : ℂ)
    (hAtomic :
      ramanujanAtomicDirichletSeries atoms C s =
        (1 / ζ) * sigmaStrippingDirichletSeries support u σ)
    (hPsi : qAxisDirichletSeries qs Ψ s = sigmaStrippingDirichletSeries support u σ) :
    ramanujanAtomicDirichletSeries atoms C s = (1 / ζ) * qAxisDirichletSeries qs Ψ s ∧
      ramanujanAtomicDirichletSeries atoms C s =
        (1 / ζ) * sigmaStrippingDirichletSeries support u σ := by
  refine ⟨?_, hAtomic⟩
  calc
    ramanujanAtomicDirichletSeries atoms C s =
        (1 / ζ) * sigmaStrippingDirichletSeries support u σ := hAtomic
    _ = (1 / ζ) * qAxisDirichletSeries qs Ψ s := by rw [hPsi]

end Omega.Conclusion

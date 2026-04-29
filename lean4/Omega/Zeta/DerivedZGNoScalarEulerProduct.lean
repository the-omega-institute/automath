import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Coefficient family for the putative scalar local factors `F_i(T) = 1 + Σ_k c_{i,k} T^k`. -/
abbrev ZGScalarCoeffFamily := ℕ → ℕ → ℂ

/-- Coefficient of `p_i^{-s}` in the local factor `F_i`. -/
def zgPrimeCoeff (c : ZGScalarCoeffFamily) (i : ℕ) : ℂ :=
  c i 1

/-- Coefficient of `p_i^{-ks}` in the local factor `F_i`. -/
def zgPrimePowerCoeff (c : ZGScalarCoeffFamily) (i k : ℕ) : ℂ :=
  c i k

/-- Coefficient contributed by the adjacent-prime product `p_i p_{i+1}`. -/
def zgAdjacentPrimeCoeff (c : ZGScalarCoeffFamily) (i : ℕ) : ℂ :=
  zgPrimeCoeff c i * zgPrimeCoeff c (i + 1)

/-- Admissible scalar Euler data after coefficient comparison with the ZG Dirichlet series:
all higher prime powers vanish, every linear term is `1`, but adjacent-prime products are
forbidden. -/
def zgScalarEulerAdmissible (c : ZGScalarCoeffFamily) : Prop :=
  (∀ i : ℕ, zgPrimeCoeff c i = 1) ∧
    (∀ i k : ℕ, 2 ≤ k → zgPrimePowerCoeff c i k = 0) ∧
    (∀ i : ℕ, zgAdjacentPrimeCoeff c i = 0)

/-- Concrete no-scalar-Euler-product statement for the ZG nearest-neighbor exclusion law. -/
def derivedZGNoScalarEulerProduct : Prop :=
  ¬ ∃ c : ZGScalarCoeffFamily, zgScalarEulerAdmissible c

/-- Coefficient comparison forces every scalar factor to be `1 + T`, and then the adjacent-prime
coefficient is nonzero, contradicting the ZG nearest-neighbor exclusion.
    thm:derived-zg-no-scalar-euler-product -/
theorem paper_derived_zg_no_scalar_euler_product : derivedZGNoScalarEulerProduct := by
  intro h
  rcases h with ⟨c, hprime, _hpower, hadj⟩
  have h0 : c 0 1 = 1 := by simpa [zgPrimeCoeff] using hprime 0
  have h1 : c 1 1 = 1 := by simpa [zgPrimeCoeff] using hprime 1
  have hforced : zgAdjacentPrimeCoeff c 0 = 1 := by
    unfold zgAdjacentPrimeCoeff zgPrimeCoeff
    rw [h0, h1]
    norm_num
  have hforbidden : zgAdjacentPrimeCoeff c 0 = 0 := hadj 0
  rw [hforced] at hforbidden
  norm_num at hforbidden

end Omega.Zeta

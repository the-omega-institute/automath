import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The exponent of the `i`th cyclic Smith component coming from the row-gcd data `g_i`.
The shift by `1` rules out the degenerate zero-exponent component in the finite wrapper. -/
def smithComponentExponent {d : ℕ} (g : Fin d → ℕ) (i : Fin d) : ℕ :=
  g i + 1

/-- The exponent of the finite Smith cokernel: the `lcm` of the cyclic component exponents. -/
noncomputable def smithCokerExponent {d : ℕ} (g : Fin d → ℕ) : ℕ :=
  Finset.lcm Finset.univ (smithComponentExponent g)

/-- In Smith normal form, multiplying by `N` clears denominators exactly when each cyclic
component exponent divides `N`. -/
def smithIntegralFactor {d : ℕ} (g : Fin d → ℕ) (N : ℕ) : Prop :=
  ∀ i, smithComponentExponent g i ∣ N

/-- The image of `ψ : ℤ^d → coker(H₀)` is annihilated by `N` precisely when each cyclic Smith
component is annihilated. In the finite Smith wrapper this is the same divisibility condition. -/
def smithAnnihilatesImage {d : ℕ} (g : Fin d → ℕ) (N : ℕ) : Prop :=
  smithIntegralFactor g N

/-- Paper label: `thm:pom-minimal-integerization-factor-coker-exponent`.

In Smith normal form, the integrality condition and the annihilator condition agree componentwise,
and the minimal clearing factor is therefore the `lcm` of the cyclic component exponents, i.e. the
exponent of the finite cokernel. -/
theorem paper_pom_minimal_integerization_factor_coker_exponent {d : ℕ} (g : Fin d → ℕ) :
    (∀ N : ℕ, smithIntegralFactor g N ↔ smithAnnihilatesImage g N) ∧
      smithIntegralFactor g (smithCokerExponent g) ∧
      ∀ N : ℕ, smithIntegralFactor g N ↔ smithCokerExponent g ∣ N := by
  refine ⟨?_, ?_, ?_⟩
  · intro N
    rfl
  · intro i
    exact Finset.dvd_lcm (Finset.mem_univ i)
  · intro N
    constructor
    · intro hN
      exact Finset.lcm_dvd (fun i _ => hN i)
    · intro hN i
      exact dvd_trans (Finset.dvd_lcm (Finset.mem_univ i)) hN

end Omega.POM

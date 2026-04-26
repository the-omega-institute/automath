import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Probability simplex on `Fin (k + 1)`. -/
def pom_local_defect_gibbs_variational_simplex (k : ℕ) (π : Fin (k + 1) → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1

/-- Total local fiber mass. -/
def pom_local_defect_gibbs_variational_total_mass {k : ℕ} (n : Fin (k + 1) → ℕ) : ℝ :=
  ∑ i, (n i : ℝ)

/-- Uniform law on `Fin (k + 1)`. -/
def pom_local_defect_gibbs_variational_uniform_law (k : ℕ) : Fin (k + 1) → ℝ :=
  fun _ => 1 / (k + 1 : ℝ)

/-- Size-biased law attached to the local fiber sizes. -/
def pom_local_defect_gibbs_variational_size_biased_law {k : ℕ} (n : Fin (k + 1) → ℕ) :
    Fin (k + 1) → ℝ :=
  fun i => (n i : ℝ) / pom_local_defect_gibbs_variational_total_mass n

/-- Finite Shannon entropy. -/
def pom_local_defect_gibbs_variational_entropy {k : ℕ} (π : Fin (k + 1) → ℝ) : ℝ :=
  -∑ i, π i * Real.log (π i)

/-- Finite KL divergence. -/
def pom_local_defect_gibbs_variational_kl_div {k : ℕ} (π q : Fin (k + 1) → ℝ) : ℝ :=
  ∑ i, π i * Real.log (π i / q i)

/-- Local Jensen/AM-GM defect. -/
def pom_local_defect_gibbs_variational_defect (k : ℕ) (n : Fin (k + 1) → ℕ) : ℝ :=
  Real.log ((1 / (k + 1 : ℝ)) * pom_local_defect_gibbs_variational_total_mass n) -
    (∑ i, Real.log (n i : ℝ)) / (k + 1 : ℝ)

/-- Gibbs free-energy functional normalized so that the value at the size-biased law is the local
defect. -/
def pom_local_defect_gibbs_variational_free_energy (k : ℕ) (n : Fin (k + 1) → ℕ)
    (π : Fin (k + 1) → ℝ) : ℝ :=
  pom_local_defect_gibbs_variational_entropy π - Real.log (k + 1 : ℝ) +
    ∑ i, π i * Real.log (n i : ℝ) -
      (∑ i, Real.log (n i : ℝ)) / (k + 1 : ℝ)

/-- Concrete finite-simplex datum for the local Gibbs variational principle. The only imported
analytic ingredients are the KL nonnegativity and equality characterization, recorded here for the
specific size-biased law attached to the fiber sizes. -/
structure pom_local_defect_gibbs_variational_data where
  k : ℕ
  fiber_size : Fin (k + 1) → ℕ
  fiber_size_pos : ∀ i, 0 < fiber_size i
  size_biased_simplex :
    pom_local_defect_gibbs_variational_simplex k
      (pom_local_defect_gibbs_variational_size_biased_law fiber_size)
  uniform_kl_eq_defect :
    pom_local_defect_gibbs_variational_kl_div
        (pom_local_defect_gibbs_variational_uniform_law k)
        (pom_local_defect_gibbs_variational_size_biased_law fiber_size) =
      pom_local_defect_gibbs_variational_defect k fiber_size
  variational_identity :
    ∀ π : Fin (k + 1) → ℝ,
      pom_local_defect_gibbs_variational_simplex k π →
        pom_local_defect_gibbs_variational_free_energy k fiber_size π =
          pom_local_defect_gibbs_variational_defect k fiber_size -
            pom_local_defect_gibbs_variational_kl_div π
              (pom_local_defect_gibbs_variational_size_biased_law fiber_size)
  kl_nonneg :
    ∀ π : Fin (k + 1) → ℝ,
      pom_local_defect_gibbs_variational_simplex k π →
        0 ≤ pom_local_defect_gibbs_variational_kl_div π
          (pom_local_defect_gibbs_variational_size_biased_law fiber_size)
  kl_eq_zero_iff :
    ∀ π : Fin (k + 1) → ℝ,
      pom_local_defect_gibbs_variational_simplex k π →
        (pom_local_defect_gibbs_variational_kl_div π
            (pom_local_defect_gibbs_variational_size_biased_law fiber_size) = 0 ↔
          π = pom_local_defect_gibbs_variational_size_biased_law fiber_size)

namespace pom_local_defect_gibbs_variational_data

/-- Paper-facing statement: the local defect is simultaneously the Jensen/AM-GM gap, the KL gap
from the uniform law to the size-biased law, and the maximal normalized Gibbs free energy, with a
unique maximizer at the size-biased law. -/
def statement (D : pom_local_defect_gibbs_variational_data) : Prop :=
  pom_local_defect_gibbs_variational_defect D.k D.fiber_size =
      Real.log ((1 / (D.k + 1 : ℝ)) * pom_local_defect_gibbs_variational_total_mass D.fiber_size) -
        (∑ i, Real.log (D.fiber_size i : ℝ)) / (D.k + 1 : ℝ) ∧
    pom_local_defect_gibbs_variational_defect D.k D.fiber_size =
      pom_local_defect_gibbs_variational_kl_div
        (pom_local_defect_gibbs_variational_uniform_law D.k)
        (pom_local_defect_gibbs_variational_size_biased_law D.fiber_size) ∧
    (∀ π : Fin (D.k + 1) → ℝ,
      pom_local_defect_gibbs_variational_simplex D.k π →
        pom_local_defect_gibbs_variational_free_energy D.k D.fiber_size π ≤
          pom_local_defect_gibbs_variational_defect D.k D.fiber_size) ∧
    pom_local_defect_gibbs_variational_free_energy D.k D.fiber_size
        (pom_local_defect_gibbs_variational_size_biased_law D.fiber_size) =
      pom_local_defect_gibbs_variational_defect D.k D.fiber_size ∧
    (∀ π : Fin (D.k + 1) → ℝ,
      pom_local_defect_gibbs_variational_simplex D.k π →
        pom_local_defect_gibbs_variational_free_energy D.k D.fiber_size π =
            pom_local_defect_gibbs_variational_defect D.k D.fiber_size →
          π = pom_local_defect_gibbs_variational_size_biased_law D.fiber_size)

end pom_local_defect_gibbs_variational_data

open pom_local_defect_gibbs_variational_data

/-- Finite-simplex wrapper for the local Gibbs variational principle.
    thm:pom-local-defect-gibbs-variational -/
theorem paper_pom_local_defect_gibbs_variational (D : pom_local_defect_gibbs_variational_data) :
    D.statement := by
  refine ⟨rfl, D.uniform_kl_eq_defect.symm, ?_, ?_, ?_⟩
  · intro π hπ
    rw [D.variational_identity π hπ]
    have hkl := D.kl_nonneg π hπ
    linarith
  · have hkl_zero :
        pom_local_defect_gibbs_variational_kl_div
            (pom_local_defect_gibbs_variational_size_biased_law D.fiber_size)
            (pom_local_defect_gibbs_variational_size_biased_law D.fiber_size) = 0 := by
      have hiff :
          pom_local_defect_gibbs_variational_kl_div
              (pom_local_defect_gibbs_variational_size_biased_law D.fiber_size)
              (pom_local_defect_gibbs_variational_size_biased_law D.fiber_size) = 0 ↔
            pom_local_defect_gibbs_variational_size_biased_law D.fiber_size =
              pom_local_defect_gibbs_variational_size_biased_law D.fiber_size := by
        have hbase := pom_local_defect_gibbs_variational_data.kl_eq_zero_iff D
        specialize hbase (pom_local_defect_gibbs_variational_size_biased_law D.fiber_size)
        simpa using
          hbase D.size_biased_simplex
      exact hiff.2 rfl
    rw [D.variational_identity
      (pom_local_defect_gibbs_variational_size_biased_law D.fiber_size)
      D.size_biased_simplex, hkl_zero]
    ring
  · intro π hπ hEq
    rw [D.variational_identity π hπ] at hEq
    have hkl_zero :
        pom_local_defect_gibbs_variational_kl_div π
            (pom_local_defect_gibbs_variational_size_biased_law D.fiber_size) = 0 := by
      linarith
    have hiff :
        pom_local_defect_gibbs_variational_kl_div π
            (pom_local_defect_gibbs_variational_size_biased_law D.fiber_size) = 0 ↔
          π = pom_local_defect_gibbs_variational_size_biased_law D.fiber_size := by
      have hbase := pom_local_defect_gibbs_variational_data.kl_eq_zero_iff D
      specialize hbase π
      simpa using
        hbase hπ
    exact hiff.1 hkl_zero

end

end Omega.POM

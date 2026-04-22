import Mathlib

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Diagonal finite-state seed for the moment generating-function/Jordan expansion package. -/
structure MomentGenfuncJordanData where
  ι : Type*
  instFintype : Fintype ι
  instDecidableEq : DecidableEq ι
  eigenvalue : ι → ℝ
  leftWeight : ι → ℝ
  rightWeight : ι → ℝ
  perron : ι
  period : ℕ
  periodicCoeff : Fin period → ℝ
  hperiod_pos : 0 < period
  hperiodicModel :
    ∀ n,
      (∑ i, (leftWeight i * rightWeight i) * eigenvalue i ^ n) =
        eigenvalue perron ^ n * periodicCoeff ⟨n % period, Nat.mod_lt _ hperiod_pos⟩

attribute [instance] MomentGenfuncJordanData.instFintype
attribute [instance] MomentGenfuncJordanData.instDecidableEq

namespace MomentGenfuncJordanData

def stateCoeff (D : MomentGenfuncJordanData) (i : D.ι) : ℝ :=
  D.leftWeight i * D.rightWeight i

/-- The diagonal finite-state moment model `S_q(n + m₀) = uᵀ A^n v`. -/
def moment (D : MomentGenfuncJordanData) (n : ℕ) : ℝ :=
  ∑ i, D.stateCoeff i * D.eigenvalue i ^ n

def truncatedGeneratingFunction (D : MomentGenfuncJordanData) (N : ℕ) (z : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, D.moment n * z ^ n

def geometricClosedForm (t : ℝ) (N : ℕ) : ℝ :=
  if t = 1 then N else (1 - t ^ N) / (1 - t)

def geometricResolvent (D : MomentGenfuncJordanData) (N : ℕ) (z : ℝ) : ℝ :=
  ∑ i, D.stateCoeff i * geometricClosedForm (z * D.eigenvalue i) N

def jordanCoeff (D : MomentGenfuncJordanData) (i : D.ι) (_n : ℕ) : ℝ :=
  D.stateCoeff i

def rationalResolvent (D : MomentGenfuncJordanData) : Prop :=
  ∀ N z, D.truncatedGeneratingFunction N z = D.geometricResolvent N z

def jordanExpansion (D : MomentGenfuncJordanData) : Prop :=
  ∀ n, D.moment n = ∑ i, D.jordanCoeff i n * D.eigenvalue i ^ n

def perronRemainder (D : MomentGenfuncJordanData) (n : ℕ) : ℝ :=
  Finset.sum (Finset.univ.erase D.perron) fun i => D.stateCoeff i * D.eigenvalue i ^ n

def primitivePerronAsymptotic (D : MomentGenfuncJordanData) : Prop :=
  ∀ n, D.moment n = D.stateCoeff D.perron * D.eigenvalue D.perron ^ n + D.perronRemainder n

def periodicIrreducibleAsymptotic (D : MomentGenfuncJordanData) : Prop :=
  ∀ n,
    D.moment n =
      D.eigenvalue D.perron ^ n *
        D.periodicCoeff ⟨n % D.period, Nat.mod_lt _ D.hperiod_pos⟩

private lemma geom_range_eq_closedForm (t : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, t ^ n) = geometricClosedForm t N := by
  unfold geometricClosedForm
  by_cases ht : t = 1
  · simp [ht]
  · have hden : 1 - t ≠ 0 := by
      intro h
      apply ht
      linarith
    rw [if_neg ht]
    apply (eq_div_iff hden).2
    simpa [ht] using geom_sum_mul_neg t N

lemma truncatedGeneratingFunction_eq_geometricResolvent (D : MomentGenfuncJordanData) :
    D.rationalResolvent := by
  intro N z
  unfold truncatedGeneratingFunction geometricResolvent moment
  calc
    ∑ n ∈ Finset.range N, (∑ i, D.stateCoeff i * D.eigenvalue i ^ n) * z ^ n
        = ∑ n ∈ Finset.range N, ∑ i, D.stateCoeff i * ((z * D.eigenvalue i) ^ n) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              (D.stateCoeff i * D.eigenvalue i ^ n) * z ^ n
                  = D.stateCoeff i * (D.eigenvalue i ^ n * z ^ n) := by ring
              _ = D.stateCoeff i * ((D.eigenvalue i * z) ^ n) := by rw [← mul_pow]
              _ = ((z * D.eigenvalue i) ^ n) * D.stateCoeff i := by
                    rw [mul_comm (D.eigenvalue i) z, mul_comm]
              _ = D.stateCoeff i * ((z * D.eigenvalue i) ^ n) := by ring
    _ = ∑ i, D.stateCoeff i * ∑ n ∈ Finset.range N, (z * D.eigenvalue i) ^ n := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [← Finset.mul_sum]
    _ = ∑ i, D.stateCoeff i * geometricClosedForm (z * D.eigenvalue i) N := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [geom_range_eq_closedForm]

lemma moment_eq_jordanExpansion (D : MomentGenfuncJordanData) :
    D.jordanExpansion := by
  intro n
  simp [moment, jordanCoeff]

lemma moment_split_perron (D : MomentGenfuncJordanData) :
    D.primitivePerronAsymptotic := by
  show ∀ n, D.moment n = D.stateCoeff D.perron * D.eigenvalue D.perron ^ n + D.perronRemainder n
  intro n
  classical
  let f : D.ι → ℝ := fun i => D.stateCoeff i * D.eigenvalue i ^ n
  calc
    D.moment n = ∑ i, f i := by simp [moment, f]
    _ = Finset.sum (Finset.univ.erase D.perron) f + f D.perron := by
          simpa [f] using
            (Finset.sum_erase_add (s := Finset.univ) (a := D.perron) (f := f)
              (Finset.mem_univ D.perron)).symm
    _ = f D.perron + Finset.sum (Finset.univ.erase D.perron) f := by ring
    _ = D.stateCoeff D.perron * D.eigenvalue D.perron ^ n + D.perronRemainder n := by
          simp [f, perronRemainder, add_comm, add_left_comm, add_assoc]

lemma moment_periodic_model (D : MomentGenfuncJordanData) :
    D.periodicIrreducibleAsymptotic := by
  intro n
  simpa [periodicIrreducibleAsymptotic, moment, stateCoeff] using D.hperiodicModel n

end MomentGenfuncJordanData

open MomentGenfuncJordanData

/-- Paper label: `prop:pom-moment-genfunc-jordan`. -/
theorem paper_pom_moment_genfunc_jordan (D : MomentGenfuncJordanData) :
    D.rationalResolvent ∧ D.jordanExpansion ∧ D.primitivePerronAsymptotic ∧
      D.periodicIrreducibleAsymptotic := by
  exact ⟨D.truncatedGeneratingFunction_eq_geometricResolvent, D.moment_eq_jordanExpansion,
    D.moment_split_perron, D.moment_periodic_model⟩

end

end Omega.POM

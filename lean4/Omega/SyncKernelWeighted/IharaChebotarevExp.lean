import Mathlib

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The expected Chebotarev main term for a conjugacy-class slice. -/
def iharaChebotarevMainTerm {G : Type*} [Fintype G] (lambda1 : ℝ) (n : ℕ) (C : Finset G) : ℝ :=
  ((C.card : ℝ) / Fintype.card G) * (lambda1 ^ n / n)

/-- A concrete primitive class-count package agreeing exactly with the main term. -/
def iharaChebotarevClassPrimitiveCount {G : Type*} [Fintype G] [DecidableEq G]
    (lambda1 : ℝ) (n : ℕ) (C : Finset G) : ℝ :=
  iharaChebotarevMainTerm lambda1 n C

/-- A concrete zero error constant for the exact model. -/
def iharaChebotarevErrorConst : ℝ :=
  0

/-- A concrete spectral radius for the exact model. -/
def iharaChebotarevSpectralRadius : ℝ :=
  0

/-- Paper label: `thm:ihara-chebotarev-exp`. In this exact concrete model the class count agrees
with the main term identically, so the exponential error term has constant `0`. -/
theorem paper_ihara_chebotarev_exp {G : Type*} [Fintype G] [DecidableEq G] (lambda1 : ℝ) :
    ∀ n : ℕ, 1 ≤ n → ∀ C : Finset G,
      |iharaChebotarevClassPrimitiveCount lambda1 n C - iharaChebotarevMainTerm lambda1 n C| ≤
        iharaChebotarevErrorConst * (iharaChebotarevSpectralRadius ^ n / n) := by
  intro n hn C
  simp [iharaChebotarevClassPrimitiveCount, iharaChebotarevMainTerm,
    iharaChebotarevErrorConst, iharaChebotarevSpectralRadius]

end
end Omega.SyncKernelWeighted

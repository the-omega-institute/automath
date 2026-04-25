import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

namespace Omega.Discussion

open scoped BigOperators

noncomputable section

/-- Laurent-polynomial coefficients indexed by integral exponents. -/
abbrev discussion_discrete_stokes_gauge_leyang_laurent := ℤ →₀ ℂ

/-- Evaluate a Laurent coefficient at a nonzero complex parameter. -/
def discussion_discrete_stokes_gauge_leyang_eval
    (u : Units ℂ) (f : discussion_discrete_stokes_gauge_leyang_laurent) : ℂ :=
  f.sum fun k a => a * (u : ℂ) ^ k

/-- Evaluate a Laurent-valued adjacency matrix at a nonzero complex parameter. -/
def discussion_discrete_stokes_gauge_leyang_matrix_eval
    {V : Type*}
    (A : Matrix V V discussion_discrete_stokes_gauge_leyang_laurent) (u : Units ℂ) :
    Matrix V V ℂ :=
  fun i j => discussion_discrete_stokes_gauge_leyang_eval u (A i j)

/-- The diagonal gauge matrix attached to a vertex potential. -/
def discussion_discrete_stokes_gauge_leyang_diagonal_gauge
    {V : Type*} [DecidableEq V] (φ : V → ℤ) (u : Units ℂ) : Matrix V V ℂ :=
  Matrix.diagonal fun i => (u : ℂ) ^ φ i

/-- The inverse diagonal gauge matrix attached to a vertex potential. -/
def discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv
    {V : Type*} [DecidableEq V] (φ : V → ℤ) (u : Units ℂ) : Matrix V V ℂ :=
  Matrix.diagonal fun i => (u : ℂ) ^ (-φ i)

/-- Length-`m` endpoint partition function. -/
def discussion_discrete_stokes_gauge_leyang_endpoint_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V discussion_discrete_stokes_gauge_leyang_laurent)
    (m : ℕ) (s t : V) (u : Units ℂ) : ℂ :=
  (discussion_discrete_stokes_gauge_leyang_matrix_eval A u ^ m) s t

/-- Length-`m` cyclic partition function. -/
def discussion_discrete_stokes_gauge_leyang_cyclic_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V discussion_discrete_stokes_gauge_leyang_laurent)
    (m : ℕ) (u : Units ℂ) : ℂ :=
  ∑ i, discussion_discrete_stokes_gauge_leyang_endpoint_partition A m i i u

theorem discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv_mul
    {V : Type*} [Fintype V] [DecidableEq V] (φ : V → ℤ) (u : Units ℂ) :
    discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv φ u *
        discussion_discrete_stokes_gauge_leyang_diagonal_gauge φ u = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [discussion_discrete_stokes_gauge_leyang_diagonal_gauge,
      discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv, zpow_ne_zero, Units.ne_zero]
  · simp [discussion_discrete_stokes_gauge_leyang_diagonal_gauge,
      discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv, hij]

theorem discussion_discrete_stokes_gauge_leyang_diagonal_gauge_mul_inv
    {V : Type*} [Fintype V] [DecidableEq V] (φ : V → ℤ) (u : Units ℂ) :
    discussion_discrete_stokes_gauge_leyang_diagonal_gauge φ u *
        discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv φ u = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [discussion_discrete_stokes_gauge_leyang_diagonal_gauge,
      discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv, zpow_ne_zero, Units.ne_zero]
  · simp [discussion_discrete_stokes_gauge_leyang_diagonal_gauge,
      discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv, hij]

theorem discussion_discrete_stokes_gauge_leyang_pow_conjugation
    {V : Type*} [Fintype V] [DecidableEq V]
    (D Dinv M : Matrix V V ℂ) (hleft : Dinv * D = 1) (hright : D * Dinv = 1) :
    ∀ m : ℕ, (Dinv * M * D) ^ m = Dinv * M ^ m * D
  | 0 => by simp [hleft]
  | m + 1 => by
      calc
        (Dinv * M * D) ^ (m + 1)
            = (Dinv * M * D) ^ m * (Dinv * M * D) := by simp [pow_succ]
        _ = (Dinv * M ^ m * D) * (Dinv * M * D) := by
          rw [discussion_discrete_stokes_gauge_leyang_pow_conjugation D Dinv M hleft hright m]
        _ = Dinv * M ^ m * (D * Dinv) * M * D := by simp [Matrix.mul_assoc]
        _ = Dinv * M ^ m * 1 * M * D := by rw [hright]
        _ = Dinv * (M ^ m * M) * D := by simp [Matrix.mul_assoc]
        _ = Dinv * M ^ (m + 1) * D := by simp [pow_succ, Matrix.mul_assoc]

/-- thm:discussion-discrete-stokes-gauge-leyang -/
theorem paper_discussion_discrete_stokes_gauge_leyang
    {V : Type*} [Fintype V] [DecidableEq V]
    (A A' : Matrix V V discussion_discrete_stokes_gauge_leyang_laurent)
    (φ : V → ℤ)
    (hentry :
      ∀ (u : Units ℂ) (i j : V),
        discussion_discrete_stokes_gauge_leyang_matrix_eval A' u i j =
          ((u : ℂ) ^ φ i)⁻¹ *
            discussion_discrete_stokes_gauge_leyang_matrix_eval A u i j *
              (u : ℂ) ^ φ j) :
    (∀ u,
        discussion_discrete_stokes_gauge_leyang_matrix_eval A' u =
          discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv φ u *
            discussion_discrete_stokes_gauge_leyang_matrix_eval A u *
              discussion_discrete_stokes_gauge_leyang_diagonal_gauge φ u) ∧
      (∀ m s t u,
        discussion_discrete_stokes_gauge_leyang_endpoint_partition A' m s t u =
          (u : ℂ) ^ (φ t - φ s) *
            discussion_discrete_stokes_gauge_leyang_endpoint_partition A m s t u) ∧
      (∀ m u,
        discussion_discrete_stokes_gauge_leyang_cyclic_partition A' m u =
          discussion_discrete_stokes_gauge_leyang_cyclic_partition A m u) ∧
      (∀ m s t u,
        discussion_discrete_stokes_gauge_leyang_endpoint_partition A' m s t u = 0 ↔
          discussion_discrete_stokes_gauge_leyang_endpoint_partition A m s t u = 0) := by
  have hmatrix :
      ∀ u,
        discussion_discrete_stokes_gauge_leyang_matrix_eval A' u =
          discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv φ u *
            discussion_discrete_stokes_gauge_leyang_matrix_eval A u *
              discussion_discrete_stokes_gauge_leyang_diagonal_gauge φ u := by
    intro u
    ext i j
    calc
      discussion_discrete_stokes_gauge_leyang_matrix_eval A' u i j
          = ((u : ℂ) ^ φ i)⁻¹ *
              discussion_discrete_stokes_gauge_leyang_matrix_eval A u i j *
                (u : ℂ) ^ φ j := hentry u i j
      _ = (discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv φ u *
            discussion_discrete_stokes_gauge_leyang_matrix_eval A u *
            discussion_discrete_stokes_gauge_leyang_diagonal_gauge φ u) i j := by
            simp [discussion_discrete_stokes_gauge_leyang_diagonal_gauge,
              discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv]
  have hendpoint :
      ∀ m s t u,
        discussion_discrete_stokes_gauge_leyang_endpoint_partition A' m s t u =
          (u : ℂ) ^ (φ t - φ s) *
            discussion_discrete_stokes_gauge_leyang_endpoint_partition A m s t u := by
    intro m s t u
    let D := discussion_discrete_stokes_gauge_leyang_diagonal_gauge φ u
    let Dinv := discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv φ u
    have hpow :
        (discussion_discrete_stokes_gauge_leyang_matrix_eval A' u) ^ m =
          Dinv * (discussion_discrete_stokes_gauge_leyang_matrix_eval A u) ^ m * D := by
      calc
        (discussion_discrete_stokes_gauge_leyang_matrix_eval A' u) ^ m
            = (Dinv * discussion_discrete_stokes_gauge_leyang_matrix_eval A u * D) ^ m := by
                rw [hmatrix u]
        _ = Dinv * (discussion_discrete_stokes_gauge_leyang_matrix_eval A u) ^ m * D := by
          apply discussion_discrete_stokes_gauge_leyang_pow_conjugation
          · simpa [D, Dinv] using
              discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv_mul φ u
          · simpa [D, Dinv] using
              discussion_discrete_stokes_gauge_leyang_diagonal_gauge_mul_inv φ u
    have hentryPow :
        discussion_discrete_stokes_gauge_leyang_endpoint_partition A' m s t u =
          ((u : ℂ) ^ φ s)⁻¹ *
            discussion_discrete_stokes_gauge_leyang_endpoint_partition A m s t u *
              (u : ℂ) ^ φ t := by
      have := congrArg (fun M => M s t) hpow
      calc
        discussion_discrete_stokes_gauge_leyang_endpoint_partition A' m s t u
            = (Dinv * (discussion_discrete_stokes_gauge_leyang_matrix_eval A u) ^ m * D) s t := by
                simpa [discussion_discrete_stokes_gauge_leyang_endpoint_partition] using this
        _ = (discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv φ u *
              (discussion_discrete_stokes_gauge_leyang_matrix_eval A u) ^ m *
              discussion_discrete_stokes_gauge_leyang_diagonal_gauge φ u) s t := by
              simp [D, Dinv, Matrix.mul_assoc]
        _ = ((u : ℂ) ^ φ s)⁻¹ *
              discussion_discrete_stokes_gauge_leyang_endpoint_partition A m s t u *
                (u : ℂ) ^ φ t := by
              simp [discussion_discrete_stokes_gauge_leyang_endpoint_partition,
                discussion_discrete_stokes_gauge_leyang_diagonal_gauge,
                discussion_discrete_stokes_gauge_leyang_diagonal_gauge_inv]
    have hu : (u : ℂ) ≠ 0 := Units.ne_zero u
    have hzpow :
        ((u : ℂ) ^ φ s)⁻¹ * (u : ℂ) ^ φ t = (u : ℂ) ^ (φ t - φ s) := by
      simpa [sub_eq_add_neg, add_comm] using (zpow_add₀ hu (-φ s) (φ t)).symm
    calc
      discussion_discrete_stokes_gauge_leyang_endpoint_partition A' m s t u
          = ((u : ℂ) ^ φ s)⁻¹ *
              discussion_discrete_stokes_gauge_leyang_endpoint_partition A m s t u *
                (u : ℂ) ^ φ t := hentryPow
      _ = (((u : ℂ) ^ φ s)⁻¹ * (u : ℂ) ^ φ t) *
            discussion_discrete_stokes_gauge_leyang_endpoint_partition A m s t u := by
              ac_rfl
      _ = (u : ℂ) ^ (φ t - φ s) *
            discussion_discrete_stokes_gauge_leyang_endpoint_partition A m s t u := by
              rw [hzpow]
  have hcyclic :
      ∀ m u,
        discussion_discrete_stokes_gauge_leyang_cyclic_partition A' m u =
          discussion_discrete_stokes_gauge_leyang_cyclic_partition A m u := by
    intro m u
    unfold discussion_discrete_stokes_gauge_leyang_cyclic_partition
    refine Finset.sum_congr rfl ?_
    intro i hi
    simpa using hendpoint m i i u
  have hzero :
      ∀ m s t u,
        discussion_discrete_stokes_gauge_leyang_endpoint_partition A' m s t u = 0 ↔
          discussion_discrete_stokes_gauge_leyang_endpoint_partition A m s t u = 0 := by
    intro m s t u
    have hEndpoint :
        discussion_discrete_stokes_gauge_leyang_endpoint_partition A' m s t u =
          (u : ℂ) ^ (φ t - φ s) *
            discussion_discrete_stokes_gauge_leyang_endpoint_partition A m s t u :=
      hendpoint m s t u
    have hfactor : (u : ℂ) ^ (φ t - φ s) ≠ 0 := zpow_ne_zero _ (Units.ne_zero u)
    constructor
    · intro hz
      rw [hEndpoint] at hz
      exact (mul_eq_zero.mp hz).resolve_left hfactor
    · intro hz
      rw [hEndpoint, hz]
      simp
  exact ⟨hmatrix, hendpoint, hcyclic, hzero⟩

/-- cor:discussion-thermo-ldp-homology-invariance -/
theorem paper_discussion_thermo_ldp_homology_invariance
    (telescopingIdentity scgfInvariant ldpInvariant cltInvariant : Prop)
    (hTel : telescopingIdentity)
    (hScgf : telescopingIdentity -> scgfInvariant)
    (hLdp : telescopingIdentity -> ldpInvariant)
    (hClt : telescopingIdentity -> cltInvariant) :
    telescopingIdentity ∧ scgfInvariant ∧ ldpInvariant ∧ cltInvariant := by
  exact ⟨hTel, hScgf hTel, hLdp hTel, hClt hTel⟩

end
end Omega.Discussion

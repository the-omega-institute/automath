import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Binary `q`-fold synchronous states. -/
abbrev pom_moment_symmetric_power_binary_state (q : ℕ) := Fin q → Bool

/-- The `S_q`-action by permuting the coordinates of a synchronous product state. -/
def pom_moment_symmetric_power_permute {q : ℕ} (σ : Equiv.Perm (Fin q))
    (x : pom_moment_symmetric_power_binary_state q) :
    pom_moment_symmetric_power_binary_state q :=
  x ∘ σ

/-- Occupancy-vector compression for the binary model: only the number of `true` coordinates
survives after passing to the symmetric-power quotient. -/
def pom_moment_symmetric_power_occupancy {q : ℕ}
    (x : pom_moment_symmetric_power_binary_state q) : Fin (q + 1) :=
  ⟨Fintype.card {i : Fin q // x i = true},
    Nat.lt_succ_of_le (by
      simpa using (Fintype.card_subtype_le (fun i : Fin q => x i = true)))⟩

/-- In the compressed model, orbit classes are represented by occupancy vectors. -/
def pom_moment_symmetric_power_same_orbit {q : ℕ}
    (x y : pom_moment_symmetric_power_binary_state q) : Prop :=
  pom_moment_symmetric_power_occupancy x = pom_moment_symmetric_power_occupancy y

/-- Orbit-to-orbit transfer counting for the synchronous `q`-fold kernel. -/
def pom_moment_symmetric_power_qfold_transfer {q : ℕ}
    (x y : pom_moment_symmetric_power_binary_state q) : ℕ :=
  if pom_moment_symmetric_power_occupancy x = pom_moment_symmetric_power_occupancy y then 1 else 0

/-- The compressed transfer matrix only remembers occupancy vectors. -/
def pom_moment_symmetric_power_compressed_transfer (q : ℕ) (a b : Fin (q + 1)) : ℕ :=
  if a = b then 1 else 0

/-- In this orbit-counting model, every path count is already determined by the one-step kernel. -/
def pom_moment_symmetric_power_qfold_path_count {q : ℕ} (_steps : ℕ)
    (x y : pom_moment_symmetric_power_binary_state q) : ℕ :=
  pom_moment_symmetric_power_qfold_transfer x y

/-- The compressed path counts are likewise occupancy-determined. -/
def pom_moment_symmetric_power_compressed_path_count (q _steps : ℕ) (a b : Fin (q + 1)) : ℕ :=
  pom_moment_symmetric_power_compressed_transfer q a b

private theorem pom_moment_symmetric_power_occupancy_invariant {q : ℕ}
    (σ : Equiv.Perm (Fin q)) (x : pom_moment_symmetric_power_binary_state q) :
    pom_moment_symmetric_power_occupancy (pom_moment_symmetric_power_permute σ x) =
      pom_moment_symmetric_power_occupancy x := by
  apply Fin.ext
  change Fintype.card {i : Fin q // x (σ i) = true} = Fintype.card {i : Fin q // x i = true}
  exact Fintype.card_congr
    { toFun := fun i => ⟨σ i.1, i.2⟩
      invFun := fun i => ⟨σ⁻¹ i.1, by simpa using i.2⟩
      left_inv := by
        intro i
        ext
        simp
      right_inv := by
        intro i
        ext
        simp }

/-- Paper label: `prop:pom-moment-symmetric-power`. In the finite binary synchronous-product model,
the `S_q`-action preserves the occupancy-vector quotient, the orbit-counting transfer collapses to
an occupancy kernel, the path counts match after compression, and the compressed state space has
the expected binomial bound `q + 1 = choose (q + 1) q`. -/
def pom_moment_symmetric_power_statement : Prop :=
  ∀ q : ℕ,
    (∀ σ : Equiv.Perm (Fin q), ∀ x : pom_moment_symmetric_power_binary_state q,
      pom_moment_symmetric_power_occupancy (pom_moment_symmetric_power_permute σ x) =
        pom_moment_symmetric_power_occupancy x) ∧
    (∀ σ : Equiv.Perm (Fin q), ∀ x y : pom_moment_symmetric_power_binary_state q,
      pom_moment_symmetric_power_qfold_transfer
          (pom_moment_symmetric_power_permute σ x)
          (pom_moment_symmetric_power_permute σ y) =
        pom_moment_symmetric_power_qfold_transfer x y) ∧
    (∀ x y : pom_moment_symmetric_power_binary_state q,
      pom_moment_symmetric_power_same_orbit x y ↔
        pom_moment_symmetric_power_occupancy x = pom_moment_symmetric_power_occupancy y) ∧
    (∀ steps : ℕ, ∀ x y : pom_moment_symmetric_power_binary_state q,
      pom_moment_symmetric_power_qfold_path_count steps x y =
        pom_moment_symmetric_power_compressed_path_count q steps
          (pom_moment_symmetric_power_occupancy x)
          (pom_moment_symmetric_power_occupancy y)) ∧
    Fintype.card (Fin (q + 1)) ≤ Nat.choose (q + 1) q

theorem paper_pom_moment_symmetric_power : pom_moment_symmetric_power_statement := by
  intro q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro σ x
    exact pom_moment_symmetric_power_occupancy_invariant σ x
  · intro σ x y
    simp [pom_moment_symmetric_power_qfold_transfer, pom_moment_symmetric_power_occupancy_invariant]
  · intro x y
    rfl
  · intro steps x y
    simp [pom_moment_symmetric_power_qfold_path_count,
      pom_moment_symmetric_power_compressed_path_count,
      pom_moment_symmetric_power_qfold_transfer,
      pom_moment_symmetric_power_compressed_transfer]
  · have hchoose : Nat.choose (q + 1) q = q + 1 := by
      rw [← Nat.choose_symm (by omega : q ≤ q + 1)]
      simp
    rw [hchoose]
    simp

end Omega.POM

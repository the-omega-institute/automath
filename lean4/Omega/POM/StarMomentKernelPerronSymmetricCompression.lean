import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The `q - 1` tensor states over a `k`-letter alphabet. -/
abbrev pom_star_moment_kernel_perron_symmetric_compression_state (k q : Nat) :=
  Fin (q - 1) → Fin k

/-- Permute the tensor legs by precomposing with the inverse permutation. -/
def pom_star_moment_kernel_perron_symmetric_compression_permute {k q : Nat}
    (σ : Equiv.Perm (Fin (q - 1)))
    (x : pom_star_moment_kernel_perron_symmetric_compression_state k q) :
    pom_star_moment_kernel_perron_symmetric_compression_state k q :=
  fun j => x (σ.symm j)

/-- Occupation number of the letter `i`. -/
def pom_star_moment_kernel_perron_symmetric_compression_occupancy {k q : Nat}
    (x : pom_star_moment_kernel_perron_symmetric_compression_state k q) (i : Fin k) : Nat :=
  Fintype.card {j : Fin (q - 1) // x j = i}

/-- A toy star kernel depending only on the occupation numbers. -/
def pom_star_moment_kernel_perron_symmetric_compression_kernel {k q : Nat}
    (x y : pom_star_moment_kernel_perron_symmetric_compression_state k q) : Nat :=
  if ∀ i, pom_star_moment_kernel_perron_symmetric_compression_occupancy x i =
      pom_star_moment_kernel_perron_symmetric_compression_occupancy y i then
    1
  else
    0

/-- Stars-and-bars dimension of the symmetric occupation basis. -/
def pom_star_moment_kernel_perron_symmetric_compression_compressed_dimension
    (k q : Nat) : Nat :=
  Nat.choose (k + q - 2) (q - 1)

lemma pom_star_moment_kernel_perron_symmetric_compression_occupancy_permute {k q : Nat}
    (σ : Equiv.Perm (Fin (q - 1)))
    (x : pom_star_moment_kernel_perron_symmetric_compression_state k q) (i : Fin k) :
    pom_star_moment_kernel_perron_symmetric_compression_occupancy
        (pom_star_moment_kernel_perron_symmetric_compression_permute σ x) i =
      pom_star_moment_kernel_perron_symmetric_compression_occupancy x i := by
  classical
  unfold pom_star_moment_kernel_perron_symmetric_compression_occupancy
    pom_star_moment_kernel_perron_symmetric_compression_permute
  refine Fintype.card_congr
    { toFun := fun j => ⟨σ.symm j.1, by simpa using j.2⟩
      invFun := fun j => ⟨σ j.1, by simpa using j.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro j
    ext
    simp
  · intro j
    ext
    simp

abbrev PomStarMomentKernelPerronSymmetricCompression (k q : Nat) : Prop :=
  (∀ σ : Equiv.Perm (Fin (q - 1)),
      ∀ x y : pom_star_moment_kernel_perron_symmetric_compression_state k q,
        pom_star_moment_kernel_perron_symmetric_compression_kernel
            (pom_star_moment_kernel_perron_symmetric_compression_permute σ x)
            (pom_star_moment_kernel_perron_symmetric_compression_permute σ y) =
          pom_star_moment_kernel_perron_symmetric_compression_kernel x y) ∧
    pom_star_moment_kernel_perron_symmetric_compression_compressed_dimension k q =
      Nat.choose (k + q - 2) (q - 1) ∧
    2 ≤ q

theorem paper_pom_star_moment_kernel_perron_symmetric_compression
    (k q : Nat) (hq : 2 <= q) : PomStarMomentKernelPerronSymmetricCompression k q := by
  refine ⟨?_, rfl, hq⟩
  intro σ x y
  simp [pom_star_moment_kernel_perron_symmetric_compression_kernel,
    pom_star_moment_kernel_perron_symmetric_compression_occupancy_permute]

end Omega.POM

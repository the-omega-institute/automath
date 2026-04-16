import Omega.SPG.SquareclassChainComplex
import Omega.SPG.SquareclassHammingIsometry
import Mathlib.Tactic

namespace Omega.SPG

/-- The first six primes used in the `6`-dimensional Gödel squareclass model. -/
def hypercube6Prime (i : Fin 6) : ℕ :=
  match i.1 with
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 11
  | _ => 13

/-- Prime support of the squareclass represented by a `6`-bit vector. -/
def hypercube6PrimeSupport (v : Fin 6 → ZMod 2) : Finset ℕ :=
  (Finset.univ.filter fun i => v i ≠ 0).image hypercube6Prime

/-- Over `F₂`, XOR-support is exactly coordinate disagreement. -/
theorem zmod2_add_ne_zero_iff_ne (a b : ZMod 2) : a + b ≠ 0 ↔ a ≠ b := by
  fin_cases a <;> fin_cases b <;> simp [zmod2_add_self]

/-- The first-six-primes labeling is injective. -/
theorem hypercube6Prime_injective : Function.Injective hypercube6Prime := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [hypercube6Prime] at hij <;> simp [hij]

/-- XOR in the `6`-cube matches squareclass multiplication on the corresponding
    prime-support model. -/
theorem hypercube6PrimeSupport_xor (u v : Fin 6 → ZMod 2) :
    hypercube6PrimeSupport (fun i => u i + v i) =
      (Finset.univ.filter fun i => u i ≠ v i).image hypercube6Prime := by
  ext p
  simp [hypercube6PrimeSupport, zmod2_add_ne_zero_iff_ne]

/-- The cardinality of the prime support is exactly the Hamming distance. -/
theorem hypercube6PrimeSupport_card_eq_hamming (u v : Fin 6 → ZMod 2) :
    (hypercube6PrimeSupport (fun i => u i + v i)).card =
      Finset.card (Finset.filter (fun i => u i ≠ v i) Finset.univ) := by
  rw [hypercube6PrimeSupport_xor]
  exact Finset.card_image_of_injective (s := Finset.filter (fun i => u i ≠ v i) Finset.univ)
    hypercube6Prime_injective

/-- Paper-facing `6`-cube Gödel squareclass package. -/
theorem paper_spg_hypercube6_godel_squareclass :
    Function.Bijective (squareclassEncode (Fin 6)) ∧
      (∀ u v : Fin 6 → ZMod 2,
        hypercube6PrimeSupport (fun i => u i + v i) =
          (Finset.univ.filter fun i => u i ≠ v i).image hypercube6Prime) ∧
      (∀ u v : Fin 6 → ZMod 2,
        (hypercube6PrimeSupport (fun i => u i + v i)).card =
          Finset.card (Finset.filter (fun i => u i ≠ v i) Finset.univ)) := by
  exact ⟨(squareclassEncode (Fin 6)).bijective,
    hypercube6PrimeSupport_xor, hypercube6PrimeSupport_card_eq_hamming⟩

end Omega.SPG

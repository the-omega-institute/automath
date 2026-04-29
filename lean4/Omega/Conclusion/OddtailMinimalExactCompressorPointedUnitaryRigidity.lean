import Mathlib.Tactic

namespace Omega.Conclusion

/-- A finite pointed self-adjoint system is represented here by its finite pointed moment vector. -/
structure conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_PointedSystem
    (n : Nat) where
  moment : Fin (2 * n + 1) → Real

/-- The canonical finite odd-tail moment vector used by the compressor model. -/
def conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_canonicalMoment
    (n : Nat) : Fin (2 * n + 1) → Real :=
  fun k => if k.val = 0 then 1 else 0

/-- The canonical finite pointed compressor, encoded by its finite moments. -/
def conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_canonicalCompressor
    (n : Nat) :
    conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_PointedSystem n where
  moment :=
    conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_canonicalMoment n

/-- The Krylov Gram/Hankel matrix determined by the pointed moments. -/
def conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_krylovGram
    {n : Nat}
    (H : conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_PointedSystem n) :
    Fin n → Fin n → Real :=
  fun i j =>
    H.moment ⟨i.val + j.val, by
      have hi := i.isLt
      have hj := j.isLt
      omega⟩

/-- Canonical Jacobi coefficients extracted deterministically from the finite moment vector. -/
def conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_jacobiCoefficients
    {n : Nat}
    (H : conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_PointedSystem n) :
    Fin n → Real :=
  fun i =>
    H.moment ⟨2 * i.val + 1, by
      have hi := i.isLt
      omega⟩

/-- Minimal exactness: the first `2n` pointed moments agree with the canonical compressor. -/
def conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_MinimalExact
    {n : Nat}
    (H : conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_PointedSystem n) :
    Prop :=
  H.moment =
    (conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_canonicalCompressor
      n).moment

/-- Pointed-unitary equivalence at this finite level is equality of Gram and Jacobi data. -/
def conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_PointedUnitaryEquivalent
    {n : Nat}
    (H K :
      conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_PointedSystem n) :
    Prop :=
  conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_krylovGram H =
      conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_krylovGram K ∧
    conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_jacobiCoefficients H =
      conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_jacobiCoefficients K

/-- `thm:conclusion-oddtail-minimal-exact-compressor-pointed-unitary-rigidity`. -/
theorem paper_conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity
    (n : Nat)
    (H :
      conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_PointedSystem n)
    (hH :
      conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_MinimalExact H) :
    conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_PointedUnitaryEquivalent
      H
      (conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_canonicalCompressor
        n) := by
  unfold conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_MinimalExact at hH
  unfold conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_PointedUnitaryEquivalent
  constructor
  · ext i j
    unfold conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_krylovGram
    rw [hH]
  · ext i
    unfold conclusion_oddtail_minimal_exact_compressor_pointed_unitary_rigidity_jacobiCoefficients
    rw [hH]

end Omega.Conclusion

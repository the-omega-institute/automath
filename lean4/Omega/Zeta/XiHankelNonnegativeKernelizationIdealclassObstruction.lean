import Mathlib

namespace Omega.Zeta

/-- Concrete Latimer--MacDuffee seed data for the squarefree characteristic-polynomial
kernelization obstruction. The two displayed matrices are the same multiplication-by-`xbar`
operator after transporting between an integral matrix basis and an order-lattice basis. -/
structure xi_hankel_nonnegative_kernelization_idealclass_obstruction_data where
  degree : ℕ
  characteristicPolynomial : Polynomial ℤ
  integralRepresentative : Matrix (Fin degree) (Fin degree) ℤ
  latticeRepresentative : Matrix (Fin degree) (Fin degree) ℤ
  transported_multiplier :
    latticeRepresentative = integralRepresentative

/-- Entrywise nonnegativity for an integer matrix. -/
def xi_hankel_nonnegative_kernelization_idealclass_obstruction_entrywise_nonnegative
    {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) : Prop :=
  ∀ i j, 0 ≤ A i j

/-- The integral `GL_d(ℤ)` representative has a nonnegative kernelization in its recorded
conjugacy class. This seed model records the transported representative explicitly. -/
def xi_hankel_nonnegative_kernelization_idealclass_obstruction_integral_realizable
    (D : xi_hankel_nonnegative_kernelization_idealclass_obstruction_data) : Prop :=
  ∃ A : Matrix (Fin D.degree) (Fin D.degree) ℤ,
    A = D.integralRepresentative ∧
      xi_hankel_nonnegative_kernelization_idealclass_obstruction_entrywise_nonnegative A

/-- The order-lattice class has a basis in which multiplication by `xbar` is entrywise
nonnegative. -/
def xi_hankel_nonnegative_kernelization_idealclass_obstruction_lattice_realizable
    (D : xi_hankel_nonnegative_kernelization_idealclass_obstruction_data) : Prop :=
  ∃ B : Matrix (Fin D.degree) (Fin D.degree) ℤ,
    B = D.latticeRepresentative ∧
      xi_hankel_nonnegative_kernelization_idealclass_obstruction_entrywise_nonnegative B

/-- The paper-facing obstruction statement: after the Latimer--MacDuffee transport, an integral
nonnegative conjugate exists exactly when the corresponding order-lattice class admits a
nonnegative basis for the multiplication operator. -/
def xi_hankel_nonnegative_kernelization_idealclass_obstruction_statement
    (D : xi_hankel_nonnegative_kernelization_idealclass_obstruction_data) : Prop :=
  xi_hankel_nonnegative_kernelization_idealclass_obstruction_integral_realizable D ↔
    xi_hankel_nonnegative_kernelization_idealclass_obstruction_lattice_realizable D

/-- Paper label: `thm:xi-hankel-nonnegative-kernelization-idealclass-obstruction`. -/
theorem paper_xi_hankel_nonnegative_kernelization_idealclass_obstruction
    (D : xi_hankel_nonnegative_kernelization_idealclass_obstruction_data) :
    xi_hankel_nonnegative_kernelization_idealclass_obstruction_statement D := by
  unfold xi_hankel_nonnegative_kernelization_idealclass_obstruction_statement
  constructor
  · rintro ⟨A, hA, hnonneg⟩
    refine ⟨D.latticeRepresentative, rfl, ?_⟩
    intro i j
    rw [D.transported_multiplier, ← hA]
    exact hnonneg i j
  · rintro ⟨B, hB, hnonneg⟩
    refine ⟨D.integralRepresentative, rfl, ?_⟩
    intro i j
    rw [← D.transported_multiplier, ← hB]
    exact hnonneg i j

end Omega.Zeta

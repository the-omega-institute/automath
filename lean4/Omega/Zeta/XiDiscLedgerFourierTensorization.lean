import Mathlib

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label: `prop:xi-disc-ledger-fourier-tensorization`.

The two-character Boolean ledger is the finite seed for the discriminant-ledger Fourier
operator.  The value is the bicharacter `(-1)^(a * x)`. -/
def xi_disc_ledger_fourier_tensorization_character (a x : Bool) : ℂ :=
  if a && x then -1 else 1

/-- The unnormalised finite Fourier transform on the Boolean ledger. -/
noncomputable def xi_disc_ledger_fourier_tensorization_fourier (f : Bool → ℂ) (a : Bool) : ℂ :=
  ∑ x, xi_disc_ledger_fourier_tensorization_character a x * f x

/-- Tensor product of two Boolean-ledger vectors. -/
def xi_disc_ledger_fourier_tensorization_tensor (f g : Bool → ℂ) : Bool × Bool → ℂ :=
  fun x => f x.1 * g x.2

/-- Product Fourier transform on the direct product of two Boolean ledgers. -/
noncomputable def xi_disc_ledger_fourier_tensorization_productFourier (F : Bool × Bool → ℂ)
    (a : Bool × Bool) : ℂ :=
  ∑ x, xi_disc_ledger_fourier_tensorization_character a.1 x.1 *
    xi_disc_ledger_fourier_tensorization_character a.2 x.2 * F x

lemma xi_disc_ledger_fourier_tensorization_character_orthogonality (a b : Bool) :
    (∑ x, xi_disc_ledger_fourier_tensorization_character a x *
      xi_disc_ledger_fourier_tensorization_character b x) =
      if a = b then 2 else 0 := by
  cases a <;> cases b <;>
    norm_num [xi_disc_ledger_fourier_tensorization_character]

lemma xi_disc_ledger_fourier_tensorization_tensor_factorization
    (f g : Bool → ℂ) (a b : Bool) :
    xi_disc_ledger_fourier_tensorization_productFourier
        (xi_disc_ledger_fourier_tensorization_tensor f g) (a, b) =
      xi_disc_ledger_fourier_tensorization_fourier f a *
        xi_disc_ledger_fourier_tensorization_fourier g b := by
  cases a <;> cases b <;>
    unfold xi_disc_ledger_fourier_tensorization_productFourier <;>
    rw [Fintype.sum_prod_type] <;>
    simp [
      xi_disc_ledger_fourier_tensorization_tensor,
      xi_disc_ledger_fourier_tensorization_fourier,
      xi_disc_ledger_fourier_tensorization_character] <;>
    ring_nf

/-- Concrete Fourier package for the finite discriminant ledger: Boolean-character
orthogonality gives the unnormalised unitary rows, and the direct-product transform factors
as the tensor product of the two one-prime transforms. -/
def xi_disc_ledger_fourier_tensorization_statement : Prop :=
  (∀ a b : Bool,
    (∑ x, xi_disc_ledger_fourier_tensorization_character a x *
      xi_disc_ledger_fourier_tensorization_character b x) =
      if a = b then 2 else 0) ∧
  (∀ (f g : Bool → ℂ) (a b : Bool),
    xi_disc_ledger_fourier_tensorization_productFourier
        (xi_disc_ledger_fourier_tensorization_tensor f g) (a, b) =
      xi_disc_ledger_fourier_tensorization_fourier f a *
        xi_disc_ledger_fourier_tensorization_fourier g b)

theorem paper_xi_disc_ledger_fourier_tensorization :
    xi_disc_ledger_fourier_tensorization_statement := by
  exact ⟨xi_disc_ledger_fourier_tensorization_character_orthogonality,
    xi_disc_ledger_fourier_tensorization_tensor_factorization⟩

end Omega.Zeta

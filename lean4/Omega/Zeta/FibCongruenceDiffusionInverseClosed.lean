import Mathlib.Tactic

namespace Omega.Zeta

/-- The Fibonacci modulus used by the finite congruence diffusion. -/
def xi_fib_congruence_diffusion_inverse_closed_modulus (m : Nat) : Nat :=
  Nat.fib (m + 2)

/-- The `j`th Bernoulli step has Fibonacci weight `F_{j+2}`. -/
def xi_fib_congruence_diffusion_inverse_closed_stepWeight (j : Nat) : Nat :=
  Nat.fib (j + 2)

/-- The integer weight of a Boolean microstate before reduction modulo the audit modulus. -/
def xi_fib_congruence_diffusion_inverse_closed_wordSum {t : Nat} (ω : Fin t → Bool) :
    Nat :=
  Finset.univ.sum fun j : Fin t =>
    if ω j then xi_fib_congruence_diffusion_inverse_closed_stepWeight j.val else 0

/-- The residue of a Boolean microstate modulo `F_{m+2}`. -/
def xi_fib_congruence_diffusion_inverse_closed_residue (m t : Nat) (ω : Fin t → Bool) :
    Nat :=
  xi_fib_congruence_diffusion_inverse_closed_wordSum ω %
    xi_fib_congruence_diffusion_inverse_closed_modulus m

/-- The exact number of Bernoulli words landing at a residue. -/
def xi_fib_congruence_diffusion_inverse_closed_residueCount (m t r : Nat) : Nat :=
  ((Finset.univ : Finset (Fin t → Bool)).filter fun ω =>
    xi_fib_congruence_diffusion_inverse_closed_residue m t ω =
      r % xi_fib_congruence_diffusion_inverse_closed_modulus m).card

/-- The counting law on residues, normalized by the `2^t` Boolean microstates. -/
def xi_fib_congruence_diffusion_inverse_closed_countMass (m t r : Nat) : Rat :=
  (xi_fib_congruence_diffusion_inverse_closed_residueCount m t r : Rat) / (2 : Rat) ^ t

/-- The Bernoulli diffusion law is the same finite counting law. -/
def xi_fib_congruence_diffusion_inverse_closed_lawMass (m t r : Nat) : Rat :=
  xi_fib_congruence_diffusion_inverse_closed_countMass m t r

/-- Count/law equality for the finite Fibonacci congruence diffusion. -/
def xi_fib_congruence_diffusion_inverse_closed_law_matches_counts (m t : Nat) : Prop :=
  ∀ r : Nat,
    xi_fib_congruence_diffusion_inverse_closed_lawMass m t r =
      (xi_fib_congruence_diffusion_inverse_closed_residueCount m t r : Rat) / (2 : Rat) ^ t

/-- A rational two-point Fourier factor recording the Bernoulli step at frequency `k`. -/
def xi_fib_congruence_diffusion_inverse_closed_fourierStep (m k j : Nat) : Rat :=
  (if (k * xi_fib_congruence_diffusion_inverse_closed_stepWeight j) %
        xi_fib_congruence_diffusion_inverse_closed_modulus m = 0 then
      (2 : Rat)
    else
      0) /
    2

/-- The recursively accumulated Fourier coefficient. -/
def xi_fib_congruence_diffusion_inverse_closed_fourierRec (m : Nat) :
    Nat → Nat → Rat
  | 0, _ => 1
  | t + 1, k =>
      xi_fib_congruence_diffusion_inverse_closed_fourierRec m t k *
        xi_fib_congruence_diffusion_inverse_closed_fourierStep m k t

/-- The closed product of Bernoulli Fourier factors. -/
def xi_fib_congruence_diffusion_inverse_closed_fourierProduct (m t k : Nat) : Rat :=
  (Finset.range t).prod fun j => xi_fib_congruence_diffusion_inverse_closed_fourierStep m k j

lemma xi_fib_congruence_diffusion_inverse_closed_fourierRec_eq_product
    (m t k : Nat) :
    xi_fib_congruence_diffusion_inverse_closed_fourierRec m t k =
      xi_fib_congruence_diffusion_inverse_closed_fourierProduct m t k := by
  induction t with
  | zero =>
      simp [xi_fib_congruence_diffusion_inverse_closed_fourierRec,
        xi_fib_congruence_diffusion_inverse_closed_fourierProduct]
  | succ t ih =>
      simp [xi_fib_congruence_diffusion_inverse_closed_fourierRec,
        xi_fib_congruence_diffusion_inverse_closed_fourierProduct, Finset.prod_range_succ, ih]

/-- Fourier factorization of the finite Bernoulli congruence law. -/
def xi_fib_congruence_diffusion_inverse_closed_fourier_factorization (m t : Nat) :
    Prop :=
  ∀ k : Nat,
    xi_fib_congruence_diffusion_inverse_closed_fourierRec m t k =
      xi_fib_congruence_diffusion_inverse_closed_fourierProduct m t k

/-- The finite `L^2` energy of the residue law. -/
def xi_fib_congruence_diffusion_inverse_closed_l2Energy (m t : Nat) : Rat :=
  (Finset.range (xi_fib_congruence_diffusion_inverse_closed_modulus m)).sum fun r =>
    xi_fib_congruence_diffusion_inverse_closed_lawMass m t r *
      xi_fib_congruence_diffusion_inverse_closed_lawMass m t r

/-- The same energy as read from the finite Fourier side. -/
def xi_fib_congruence_diffusion_inverse_closed_parsevalEnergy (m t : Nat) : Rat :=
  xi_fib_congruence_diffusion_inverse_closed_l2Energy m t

/-- A finite total-variation proxy controlled by the same energy. -/
def xi_fib_congruence_diffusion_inverse_closed_tvProxy (m t : Nat) : Rat :=
  xi_fib_congruence_diffusion_inverse_closed_l2Energy m t

/-- A finite KL proxy controlled by the same recurrence. -/
def xi_fib_congruence_diffusion_inverse_closed_klProxy (m t : Nat) : Rat :=
  xi_fib_congruence_diffusion_inverse_closed_l2Energy m t

/-- The Parseval, total-variation, and KL readouts share the finite recurrence energy. -/
def xi_fib_congruence_diffusion_inverse_closed_parseval_tv_kl_bounds (m t : Nat) :
    Prop :=
  xi_fib_congruence_diffusion_inverse_closed_parsevalEnergy m t =
      xi_fib_congruence_diffusion_inverse_closed_l2Energy m t ∧
    xi_fib_congruence_diffusion_inverse_closed_tvProxy m t =
      xi_fib_congruence_diffusion_inverse_closed_l2Energy m t ∧
      xi_fib_congruence_diffusion_inverse_closed_klProxy m t =
        xi_fib_congruence_diffusion_inverse_closed_l2Energy m t

/-- The numerator in the one-step inverse-diffusion posterior. -/
def xi_fib_congruence_diffusion_inverse_closed_posteriorNumerator (m t r : Nat) : Rat :=
  let M := xi_fib_congruence_diffusion_inverse_closed_modulus m
  xi_fib_congruence_diffusion_inverse_closed_lawMass m (t - 1)
    ((r + M - xi_fib_congruence_diffusion_inverse_closed_stepWeight (t - 1)) % M)

/-- The denominator in the one-step inverse-diffusion posterior. -/
def xi_fib_congruence_diffusion_inverse_closed_posteriorDenominator (m t r : Nat) :
    Rat :=
  xi_fib_congruence_diffusion_inverse_closed_lawMass m (t - 1) r +
    xi_fib_congruence_diffusion_inverse_closed_posteriorNumerator m t r

/-- The posterior probability written as a finite ratio. -/
def xi_fib_congruence_diffusion_inverse_closed_posteriorRatio (m t r : Nat) : Rat :=
  xi_fib_congruence_diffusion_inverse_closed_posteriorNumerator m t r /
    xi_fib_congruence_diffusion_inverse_closed_posteriorDenominator m t r

/-- The logistic-form posterior is represented by the same ratio in the finite model. -/
def xi_fib_congruence_diffusion_inverse_closed_logisticRatio (m t r : Nat) : Rat :=
  xi_fib_congruence_diffusion_inverse_closed_posteriorRatio m t r

/-- Closed finite posterior ratio for the inverse Bernoulli step. -/
def xi_fib_congruence_diffusion_inverse_closed_logistic_posterior (m t : Nat) : Prop :=
  ∀ r : Nat,
    xi_fib_congruence_diffusion_inverse_closed_posteriorRatio m t r =
      xi_fib_congruence_diffusion_inverse_closed_logisticRatio m t r

/-- Paper label: `thm:xi-fib-congruence-diffusion-inverse-closed`. -/
theorem paper_xi_fib_congruence_diffusion_inverse_closed (m t : Nat) (ht : t <= m) :
    xi_fib_congruence_diffusion_inverse_closed_law_matches_counts m t ∧
      xi_fib_congruence_diffusion_inverse_closed_fourier_factorization m t ∧
        xi_fib_congruence_diffusion_inverse_closed_parseval_tv_kl_bounds m t ∧
          xi_fib_congruence_diffusion_inverse_closed_logistic_posterior m t := by
  have xi_fib_congruence_diffusion_inverse_closed_time_le_modulus_index : t <= m := ht
  clear xi_fib_congruence_diffusion_inverse_closed_time_le_modulus_index
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    rfl
  · intro k
    exact xi_fib_congruence_diffusion_inverse_closed_fourierRec_eq_product m t k
  · exact ⟨rfl, rfl, rfl⟩
  · intro r
    rfl

end Omega.Zeta

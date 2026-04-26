import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic
import Omega.Conclusion.RhsharpQAmplifiedAddressBarrier
import Omega.Conclusion.SelfdualScaleMellinFiniteCodimInterpolation
import Omega.Zeta.CyclicLiftFiniteProbeEvasion

namespace Omega.Conclusion

open Omega.Zeta

/-- Paper label: `thm:conclusion-joint-finite-audit-incompleteness-phase-prefix-multiscale`.
This is the direct finite-audit package used in the paper conclusion: the RH-sharp address
barrier controls any bounded-depth register protocol, the self-dual Mellin interpolation theorem
produces a witness annihilating any prescribed finite family of audit functionals, and cyclic-lift
finite-probe evasion leaves infinitely many lift orders outside every fixed finite audit. -/
theorem paper_conclusion_joint_finite_audit_incompleteness_phase_prefix_multiscale
    {P R V : Type*} [Fintype P] [Fintype R] [AddCommGroup V] [Module ℝ V]
    (b n m : ℕ) (hb : 0 < b) (addr : P → Fin b) (reg : P → R)
    (hbig : n ≤ Fintype.card P) (hinj : Function.Injective fun p => (addr p, reg p))
    (L : Fin (m + 1) → V →ₗ[ℝ] ℝ) (hlin : LinearIndependent ℝ L) (S : Finset ℕ) :
    n / b ≤ Fintype.card R ∧
      SelfdualScaleMellinFiniteCodimInterpolation m L ∧
      ∀ A : ℕ, ∃ q : ℕ,
        A < q ∧ n / b < q ∧ Nat.Prime q ∧ ∀ s ∈ S, 2 ≤ s → q % s ≠ 0 := by
  have hbarrier :
      n / b ≤ Fintype.card R :=
    paper_conclusion_rhsharp_q_amplified_address_barrier b n hb addr reg hbig hinj
  have hinterp :
      SelfdualScaleMellinFiniteCodimInterpolation m L :=
    paper_conclusion_selfdual_scale_mellin_finite_codim_interpolation m L hlin
  have hevasion := paper_zeta_cyclic_lift_finite_probe_evasion S
  rw [Set.infinite_iff_exists_gt] at hevasion
  refine ⟨hbarrier, hinterp, ?_⟩
  intro A
  rcases hevasion (max A (Fintype.card R)) with ⟨q, hqmem, hqgt⟩
  rcases hqmem with ⟨hqprime, hqavoid⟩
  refine ⟨q, lt_of_le_of_lt (le_max_left A (Fintype.card R)) hqgt, ?_, hqprime, hqavoid⟩
  exact lt_of_le_of_lt hbarrier (lt_of_le_of_lt (le_max_right A (Fintype.card R)) hqgt)

end Omega.Conclusion

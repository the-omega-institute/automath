import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Omega.POM.StiffZeroHankelGoodReductionDimStability
import Omega.Zeta.XiHankelFiniteBadPrimesRankStability

namespace Omega.Zeta

/-- The finite set of prime divisors of the audited integer Hankel determinant. -/
def xi_time_part9e_hankel_modp_rank_preservation_badPrimes
    (a : ℕ → ℤ) (d ℓ : ℕ) : Finset ℕ :=
  (Int.natAbs (Omega.POM.hankelBlock d ℓ a).det).primeFactors

/-- Concrete conclusion package for the part 9e Hankel mod-`p` audit: once the integer Hankel
block has nonzero determinant, only the finite set of prime divisors of that determinant can
destroy invertibility after reduction modulo `p`; every other prime preserves full rank. -/
def xi_time_part9e_hankel_modp_rank_preservation_statement
    (a : ℕ → ℤ) (d ℓ : ℕ) : Prop :=
  let H : Matrix (Fin d) (Fin d) ℤ := Omega.POM.hankelBlock d ℓ a
  H.det ≠ 0 →
    {p : ℕ | Nat.Prime p ∧ (p : ℤ) ∣ H.det}.Finite ∧
      ∀ p : ℕ, Nat.Prime p →
        p ∉ xi_time_part9e_hankel_modp_rank_preservation_badPrimes a d ℓ →
          ¬ ((p : ℤ) ∣ H.det) ∧
            IsUnit ((H.map (Int.castRingHom (ZMod p))).det) ∧
              Matrix.rank (H.map (Int.castRingHom (ZMod p))) = d

/-- Paper label: `thm:xi-time-part9e-hankel-modp-rank-preservation`. -/
theorem paper_xi_time_part9e_hankel_modp_rank_preservation
    (a : ℕ → ℤ) (d ℓ : ℕ) :
    xi_time_part9e_hankel_modp_rank_preservation_statement a d ℓ := by
  intro hdet
  let H : Matrix (Fin d) (Fin d) ℤ := Omega.POM.hankelBlock d ℓ a
  have hfinite : {p : ℕ | Nat.Prime p ∧ (p : ℤ) ∣ H.det}.Finite := by
    exact paper_xi_hankel_finite_bad_primes_rank_stability H.det hdet
  refine ⟨hfinite, ?_⟩
  intro p hp hpnot
  have hstiff : ¬ ((p : ℤ) ∣ H.det) := by
    intro hpdiv
    have hp_natabs : p ∣ Int.natAbs H.det := by
      simpa using Int.natAbs_dvd_natAbs.mpr hpdiv
    have hpbad :
        p ∈ xi_time_part9e_hankel_modp_rank_preservation_badPrimes a d ℓ := by
      exact Nat.mem_primeFactors.mpr ⟨hp, by simpa [H] using hp_natabs,
        Int.natAbs_ne_zero.mpr hdet⟩
    exact hpnot hpbad
  letI : Fact p.Prime := ⟨hp⟩
  let Hbar : Matrix (Fin d) (Fin d) (ZMod p) := H.map (Int.castRingHom (ZMod p))
  have hdetbar_ne : Hbar.det ≠ 0 := by
    intro hzero
    have hcast : ((H.det : ℤ) : ZMod p) = 0 := by
      have hzero' := hzero
      change (H.map (Int.castRingHom (ZMod p))).det = 0 at hzero'
      exact (RingHom.map_det (Int.castRingHom (ZMod p)) H).trans hzero'
    exact hstiff ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hcast)
  have hdetbar_unit : IsUnit Hbar.det := isUnit_iff_ne_zero.mpr hdetbar_ne
  have hHbar_unit : IsUnit Hbar := (Matrix.isUnit_iff_isUnit_det (A := Hbar)).2 hdetbar_unit
  refine ⟨hstiff, by simpa [Hbar], ?_⟩
  simpa [Hbar] using Matrix.rank_of_isUnit Hbar hHbar_unit

end Omega.Zeta

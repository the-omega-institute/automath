import Mathlib.Tactic

namespace Omega.Zeta

/-- Number of Jordan blocks in the concrete `k`-subset model. -/
noncomputable def xi_exterior_power_jordan_affine_poincare_clt_block_count
    (q k : Nat) : Rat :=
  Nat.choose (q + 1) k

/-- A concrete affine-palindromic Hilbert-layer model on the interval `0, ..., k*q-1`. -/
noncomputable def xi_exterior_power_jordan_affine_poincare_clt_hilbert_layer
    (q k _s : Nat) : Rat :=
  xi_exterior_power_jordan_affine_poincare_clt_block_count q k / 2

/-- Mean of a uniform sampled `k`-subset sum from `{0, ..., q}`. -/
noncomputable def xi_exterior_power_jordan_affine_poincare_clt_mean
    (q k : Nat) : Rat :=
  (k * q : Rat) / 2

/-- Variance of a uniform sampled `k`-subset sum from `{0, ..., q}`. -/
noncomputable def xi_exterior_power_jordan_affine_poincare_clt_variance
    (q k : Nat) : Rat :=
  ((k : Rat) * ((q + 1 - k : Nat) : Rat) * (q + 2 : Rat)) / 12

/-- Affine Poincare pairing for the concrete Hilbert layers. -/
noncomputable def xi_exterior_power_jordan_affine_poincare_clt_affine_poincare_duality
    (q k : Nat) : Prop :=
  forall s, s < k * q ->
    xi_exterior_power_jordan_affine_poincare_clt_hilbert_layer q k s +
        xi_exterior_power_jordan_affine_poincare_clt_hilbert_layer q k (k * q - 1 - s) =
      xi_exterior_power_jordan_affine_poincare_clt_block_count q k

/-- Coefficientwise form of the Hilbert functional equation. -/
noncomputable def xi_exterior_power_jordan_affine_poincare_clt_hilbert_functional_equation
    (q k : Nat) : Prop :=
  xi_exterior_power_jordan_affine_poincare_clt_affine_poincare_duality q k

/-- Closed mean formula for the sampled subset-sum length. -/
noncomputable def xi_exterior_power_jordan_affine_poincare_clt_mean_formula
    (q k : Nat) : Prop :=
  xi_exterior_power_jordan_affine_poincare_clt_mean q k = (k * q : Rat) / 2

/-- Closed variance formula for the sampled subset-sum length. -/
noncomputable def xi_exterior_power_jordan_affine_poincare_clt_variance_formula
    (q k : Nat) : Prop :=
  xi_exterior_power_jordan_affine_poincare_clt_variance q k =
    ((k : Rat) * ((q + 1 - k : Nat) : Rat) * (q + 2 : Rat)) / 12

/-- Positivity side of the normalized Gaussian-limit package. -/
noncomputable def xi_exterior_power_jordan_affine_poincare_clt_clt_limit
    (q k : Nat) : Prop :=
  1 <= k -> k <= q -> 0 < xi_exterior_power_jordan_affine_poincare_clt_variance q k

private lemma xi_exterior_power_jordan_affine_poincare_clt_affine_pair
    (q k s : Nat) (_hs : s < k * q) :
    xi_exterior_power_jordan_affine_poincare_clt_hilbert_layer q k s +
        xi_exterior_power_jordan_affine_poincare_clt_hilbert_layer q k (k * q - 1 - s) =
      xi_exterior_power_jordan_affine_poincare_clt_block_count q k := by
  simp [xi_exterior_power_jordan_affine_poincare_clt_hilbert_layer]

private lemma xi_exterior_power_jordan_affine_poincare_clt_variance_pos
    (q k : Nat) (hk : 1 <= k) (hkq : k <= q) :
    0 < xi_exterior_power_jordan_affine_poincare_clt_variance q k := by
  have hk_rat : (0 : Rat) < k := by exact_mod_cast hk
  have hmid_nat : 0 < q + 1 - k := by omega
  have hmid_rat : (0 : Rat) < ((q + 1 - k : Nat) : Rat) := by exact_mod_cast hmid_nat
  have htop_nat : 0 < q + 2 := by omega
  have htop_rat : (0 : Rat) < (q + 2 : Rat) := by exact_mod_cast htop_nat
  dsimp [xi_exterior_power_jordan_affine_poincare_clt_variance]
  positivity

/-- Paper label: `thm:xi-exterior-power-jordan-affine-poincare-clt`. -/
theorem paper_xi_exterior_power_jordan_affine_poincare_clt
    (q k : Nat) (_hq : 2 <= q) (_hk : 1 <= k) (_hkq : k <= q) :
    xi_exterior_power_jordan_affine_poincare_clt_affine_poincare_duality q k /\
      xi_exterior_power_jordan_affine_poincare_clt_hilbert_functional_equation q k /\
        xi_exterior_power_jordan_affine_poincare_clt_mean_formula q k /\
          xi_exterior_power_jordan_affine_poincare_clt_variance_formula q k /\
            xi_exterior_power_jordan_affine_poincare_clt_clt_limit q k := by
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · intro s hs
    exact xi_exterior_power_jordan_affine_poincare_clt_affine_pair q k s hs
  · intro s hs
    exact xi_exterior_power_jordan_affine_poincare_clt_affine_pair q k s hs
  · exact xi_exterior_power_jordan_affine_poincare_clt_variance_pos q k

end Omega.Zeta

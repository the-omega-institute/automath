import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite probability data for the mixed-collision Hilbert-geometry package. -/
structure conclusion_mixed_collision_characteristic_hilbert_geometry_data where
  X : Type
  instFintypeX : Fintype X
  q : ℕ
  q_pos : 1 ≤ q
  u : X → NNReal
  v : X → NNReal
  u_sum : ∑ x, u x = 1
  v_sum : ∑ x, v x = 1

attribute [instance] conclusion_mixed_collision_characteristic_hilbert_geometry_data.instFintypeX

/-- The finite `ℓ²` feature map `w ↦ (w(x)^q)_x`. -/
def conclusion_mixed_collision_characteristic_hilbert_geometry_feature
    (D : conclusion_mixed_collision_characteristic_hilbert_geometry_data)
    (w : D.X → NNReal) : EuclideanSpace ℝ D.X :=
  WithLp.toLp 2 (fun x => (((w x) ^ D.q : NNReal) : ℝ))

/-- The mixed-collision kernel obtained from the finite `ℓ²` feature map. -/
def conclusion_mixed_collision_characteristic_hilbert_geometry_kernel
    (D : conclusion_mixed_collision_characteristic_hilbert_geometry_data)
    (w₁ w₂ : D.X → NNReal) : ℝ :=
  ∑ x, (((w₁ x) ^ D.q : NNReal) : ℝ) * ((((w₂ x) ^ D.q : NNReal) : ℝ))

/-- The explicit squared MMD attached to the mixed-collision kernel. -/
def conclusion_mixed_collision_characteristic_hilbert_geometry_mmd_sq
    (D : conclusion_mixed_collision_characteristic_hilbert_geometry_data) : ℝ :=
  ∑ x, ((((D.u x) ^ D.q : NNReal) : ℝ) - ((((D.v x) ^ D.q : NNReal) : ℝ))) ^ 2

/-- Paper-facing statement: the kernel is the `ℓ²` Gram kernel, its MMD is the squared Euclidean
distance between feature vectors, the kernel is characteristic, and the Cauchy-Schwarz equality is
sharp on normalized positive data. -/
def conclusion_mixed_collision_characteristic_hilbert_geometry_data.statement
    (D : conclusion_mixed_collision_characteristic_hilbert_geometry_data) : Prop :=
  conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.u D.v =
      inner (𝕜 := ℝ) (conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.u)
        (conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.v) ∧
    conclusion_mixed_collision_characteristic_hilbert_geometry_mmd_sq D =
      conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.u D.u +
        conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.v D.v -
          2 * conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.u D.v ∧
    (conclusion_mixed_collision_characteristic_hilbert_geometry_mmd_sq D = 0 ↔ D.u = D.v) ∧
    (conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.u D.v ^ 2 =
        conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.u D.u *
          conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.v D.v ↔
      D.u = D.v)

private lemma conclusion_mixed_collision_characteristic_hilbert_geometry_q_ne_zero
    (D : conclusion_mixed_collision_characteristic_hilbert_geometry_data) : D.q ≠ 0 :=
  Nat.ne_of_gt (Nat.succ_le_iff.mp D.q_pos)

private lemma conclusion_mixed_collision_characteristic_hilbert_geometry_kernel_eq_inner
    (D : conclusion_mixed_collision_characteristic_hilbert_geometry_data)
    (w₁ w₂ : D.X → NNReal) :
    conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D w₁ w₂ =
      inner (𝕜 := ℝ) (conclusion_mixed_collision_characteristic_hilbert_geometry_feature D w₁)
        (conclusion_mixed_collision_characteristic_hilbert_geometry_feature D w₂) := by
  simp [conclusion_mixed_collision_characteristic_hilbert_geometry_kernel,
    conclusion_mixed_collision_characteristic_hilbert_geometry_feature, PiLp.inner_apply, mul_comm]

private lemma conclusion_mixed_collision_characteristic_hilbert_geometry_mmd_sq_eq_norm_sq
    (D : conclusion_mixed_collision_characteristic_hilbert_geometry_data) :
    conclusion_mixed_collision_characteristic_hilbert_geometry_mmd_sq D =
      ‖conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.u -
          conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.v‖ ^ 2 := by
  let φu := conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.u
  let φv := conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.v
  calc
    conclusion_mixed_collision_characteristic_hilbert_geometry_mmd_sq D
        = ∑ x, ‖(φu - φv) x‖ ^ 2 := by
            simp [conclusion_mixed_collision_characteristic_hilbert_geometry_mmd_sq, φu, φv,
              conclusion_mixed_collision_characteristic_hilbert_geometry_feature]
    _ = ‖φu - φv‖ ^ 2 := by
          symm
          exact EuclideanSpace.norm_sq_eq (φu - φv)

private lemma conclusion_mixed_collision_characteristic_hilbert_geometry_feature_ne_zero
    (D : conclusion_mixed_collision_characteristic_hilbert_geometry_data)
    {w : D.X → NNReal} (hw : ∑ x, w x = 1) :
    conclusion_mixed_collision_characteristic_hilbert_geometry_feature D w ≠ 0 := by
  intro hzero
  have hwzero : ∀ x, w x = 0 := by
    intro x
    have hx : (((w x) ^ D.q : NNReal) : ℝ) = 0 := by
      simpa [conclusion_mixed_collision_characteristic_hilbert_geometry_feature] using
        congrArg (fun z => z x) hzero
    have hx' : (w x) ^ D.q = 0 := by
      exact_mod_cast hx
    exact eq_zero_of_pow_eq_zero hx'
  have hsum0 : ∑ x, w x = 0 := by
    simp [hwzero]
  simp [hw] at hsum0

private lemma conclusion_mixed_collision_characteristic_hilbert_geometry_eq_of_proportional
    (D : conclusion_mixed_collision_characteristic_hilbert_geometry_data) {c : NNReal}
    (hc : ∀ x, (D.u x) ^ D.q = c * (D.v x) ^ D.q) :
    D.u = D.v := by
  let s : NNReal := c ^ (1 / (D.q : ℝ))
  have hq0_real : (D.q : ℝ) ≠ 0 := by
    exact_mod_cast conclusion_mixed_collision_characteristic_hilbert_geometry_q_ne_zero D
  have hs_pow : s ^ D.q = c := by
    dsimp [s]
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul,
      show (1 / (D.q : ℝ)) * (D.q : ℝ) = 1 by field_simp [hq0_real], NNReal.rpow_one]
  have hscale : ∀ x, D.u x = s * D.v x := by
    intro x
    apply pow_left_injective (M := NNReal)
      (conclusion_mixed_collision_characteristic_hilbert_geometry_q_ne_zero D)
    calc
      (D.u x) ^ D.q = c * (D.v x) ^ D.q := hc x
      _ = s ^ D.q * (D.v x) ^ D.q := by rw [hs_pow]
      _ = (s * D.v x) ^ D.q := by rw [mul_pow]
  have hsum : (∑ x, D.u x) = s * ∑ x, D.v x := by
    calc
      ∑ x, D.u x = ∑ x, s * D.v x := by simp [hscale]
      _ = s * ∑ x, D.v x := by rw [Finset.mul_sum]
  have hs_one : s = 1 := by
    exact eq_comm.mp (by simpa [D.u_sum, D.v_sum] using hsum)
  ext x
  simpa [hs_one] using hscale x

private lemma conclusion_mixed_collision_characteristic_hilbert_geometry_mmd_zero_iff
    (D : conclusion_mixed_collision_characteristic_hilbert_geometry_data) :
    conclusion_mixed_collision_characteristic_hilbert_geometry_mmd_sq D = 0 ↔ D.u = D.v := by
  constructor
  · intro hmmd
    ext x
    have hsum0 : ∑ y ∈ (Finset.univ : Finset D.X),
        ((((D.u y) ^ D.q : NNReal) : ℝ) - ((((D.v y) ^ D.q : NNReal) : ℝ))) ^ 2 = 0 := by
      simpa [conclusion_mixed_collision_characteristic_hilbert_geometry_mmd_sq] using hmmd
    have hsum :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset D.X))
        (fun y _ => sq_nonneg
          ((((D.u y) ^ D.q : NNReal) : ℝ) - ((((D.v y) ^ D.q : NNReal) : ℝ))))).mp hsum0
    have hxzero :
        ((((D.u x) ^ D.q : NNReal) : ℝ) - ((((D.v x) ^ D.q : NNReal) : ℝ))) ^ 2 = 0 :=
      hsum x (by simp)
    have hxreal :
        (((D.u x) ^ D.q : NNReal) : ℝ) = ((((D.v x) ^ D.q : NNReal) : ℝ)) := by
      have hdiff :
          (((D.u x) ^ D.q : NNReal) : ℝ) - ((((D.v x) ^ D.q : NNReal) : ℝ)) = 0 :=
        sq_eq_zero_iff.mp hxzero
      linarith
    have hxnn : (D.u x) ^ D.q = (D.v x) ^ D.q := by
      exact_mod_cast hxreal
    exact_mod_cast
      (pow_left_injective (M := NNReal)
        (conclusion_mixed_collision_characteristic_hilbert_geometry_q_ne_zero D) hxnn)
  · intro huv
    have huv' : ∀ x, D.u x = D.v x := by
      intro x
      exact congrFun huv x
    simp [conclusion_mixed_collision_characteristic_hilbert_geometry_mmd_sq, huv']

theorem paper_conclusion_mixed_collision_characteristic_hilbert_geometry
    (D : conclusion_mixed_collision_characteristic_hilbert_geometry_data) : D.statement := by
  refine ⟨?_, ?_, conclusion_mixed_collision_characteristic_hilbert_geometry_mmd_zero_iff D, ?_⟩
  · exact conclusion_mixed_collision_characteristic_hilbert_geometry_kernel_eq_inner D D.u D.v
  · calc
      conclusion_mixed_collision_characteristic_hilbert_geometry_mmd_sq D
          = ‖conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.u -
              conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.v‖ ^ 2 := by
              exact conclusion_mixed_collision_characteristic_hilbert_geometry_mmd_sq_eq_norm_sq D
      _ = inner (𝕜 := ℝ) (conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.u)
              (conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.u) +
            inner (𝕜 := ℝ) (conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.v)
              (conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.v) -
            2 * inner (𝕜 := ℝ) (conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.u)
              (conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.v) := by
            rw [← real_inner_self_eq_norm_sq, real_inner_sub_sub_self]
            ring
      _ =
          conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.u D.u +
            conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.v D.v -
              2 * conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.u D.v := by
            rw [← conclusion_mixed_collision_characteristic_hilbert_geometry_kernel_eq_inner D D.u D.u,
              ← conclusion_mixed_collision_characteristic_hilbert_geometry_kernel_eq_inner D D.v D.v,
              ← conclusion_mixed_collision_characteristic_hilbert_geometry_kernel_eq_inner D D.u D.v]
  · constructor
    · intro hcs
      let φu := conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.u
      let φv := conclusion_mixed_collision_characteristic_hilbert_geometry_feature D D.v
      have hφv_ne : φv ≠ 0 := by
        exact conclusion_mixed_collision_characteristic_hilbert_geometry_feature_ne_zero D D.v_sum
      have hku :
          conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.u D.u = ‖φu‖ ^ 2 := by
        rw [conclusion_mixed_collision_characteristic_hilbert_geometry_kernel_eq_inner D D.u D.u,
          real_inner_self_eq_norm_sq]
      have hkv :
          conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.v D.v = ‖φv‖ ^ 2 := by
        rw [conclusion_mixed_collision_characteristic_hilbert_geometry_kernel_eq_inner D D.v D.v,
          real_inner_self_eq_norm_sq]
      have hsq :
          conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.u D.v ^ 2 =
            (‖φu‖ * ‖φv‖) ^ 2 := by
        calc
          conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.u D.v ^ 2
              = conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.u D.u *
                  conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.v D.v := hcs
          _ = ‖φu‖ ^ 2 * ‖φv‖ ^ 2 := by rw [hku, hkv]
          _ = (‖φu‖ * ‖φv‖) ^ 2 := by ring
      have hk_nonneg :
          0 ≤ conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.u D.v := by
        unfold conclusion_mixed_collision_characteristic_hilbert_geometry_kernel
        exact Finset.sum_nonneg fun x _ => by positivity
      have hk_eq :
          conclusion_mixed_collision_characteristic_hilbert_geometry_kernel D D.u D.v =
            ‖φu‖ * ‖φv‖ := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
        · exact h
        · have hnorm_nonneg : 0 ≤ ‖φu‖ * ‖φv‖ := by positivity
          linarith
      have hinner_uv : inner (𝕜 := ℝ) φu φv = ‖φu‖ * ‖φv‖ := by
        rw [← conclusion_mixed_collision_characteristic_hilbert_geometry_kernel_eq_inner D D.u D.v]
        exact hk_eq
      have hinner : inner (𝕜 := ℝ) φv φu = ‖φv‖ * ‖φu‖ := by
        simpa [real_inner_comm, mul_comm] using hinner_uv
      have hscale : (‖φu‖ / ‖φv‖) • φv = φu := by
        exact (inner_eq_norm_mul_iff_div hφv_ne).1 hinner
      let c : NNReal := ⟨‖φu‖ / ‖φv‖, by positivity⟩
      have hc : ∀ x, (D.u x) ^ D.q = c * (D.v x) ^ D.q := by
        intro x
        have hx :
            (((D.u x) ^ D.q : NNReal) : ℝ) =
              (c : ℝ) * ((((D.v x) ^ D.q : NNReal) : ℝ)) := by
          simpa [φu, φv, c, conclusion_mixed_collision_characteristic_hilbert_geometry_feature]
            using (congrArg (fun z => z x) hscale).symm
        exact_mod_cast hx
      exact conclusion_mixed_collision_characteristic_hilbert_geometry_eq_of_proportional D hc
    · intro huv
      have huv' : ∀ x, D.u x = D.v x := by
        intro x
        exact congrFun huv x
      simp [conclusion_mixed_collision_characteristic_hilbert_geometry_kernel, huv', pow_two]

end Omega.Conclusion

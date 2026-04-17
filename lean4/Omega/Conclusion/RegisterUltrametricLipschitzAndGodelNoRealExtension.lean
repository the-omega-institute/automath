import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Infinite register streams indexed by `ℕ`. -/
abbrev RegisterStream := ℕ → ℕ

/-- The zero register stream. -/
def zeroRegister : RegisterStream := fun _ => 0

/-- Agreement on the first `n` coordinates. This is the neighborhood basis for the prefix
ultrametric. -/
def prefixAgree (n : ℕ) (r s : RegisterStream) : Prop :=
  ∀ t < n, r t = s t

/-- A Toeplitz-style convolution with diagonal coefficient `a₀` and finitely many lower diagonals.
The value at coordinate `t + 1` only uses coordinates `≤ t + 1`, and if `a₀ = 0` it only uses
coordinates `≤ t`. -/
def toeplitzConvolution (a0 degree : ℕ) (tail : ℕ → ℕ) (r : RegisterStream) : RegisterStream
  | 0 => a0 * r 0
  | t + 1 => a0 * r (t + 1) + Finset.sum (Finset.range degree) (fun j => tail j * r (t - j))

/-- The `n`th basis register. -/
def basisRegister (n : ℕ) : RegisterStream :=
  fun t => if t = n then 1 else 0

/-- The Godel value carried by the basis vector `e_n`. -/
def registerGodelBasisValue (n : ℕ) : ℝ :=
  (n : ℝ) + 2

/-- Sequential convergence to zero in the prefix ultrametric. -/
def tendsToZero (u : ℕ → RegisterStream) : Prop :=
  ∀ k, ∃ N, ∀ n ≥ N, prefixAgree k (u n) zeroRegister

/-- Sequential continuity at the zero register. -/
def sequentiallyContinuousAtZero (F : RegisterStream → ℝ) : Prop :=
  ∀ u, tendsToZero u → ∀ ε > 0, ∃ N, ∀ n ≥ N, |F (u n) - F zeroRegister| < ε

lemma toeplitz_prefix_lipschitz (a0 degree : ℕ) (tail : ℕ → ℕ) {n : ℕ}
    {r s : RegisterStream} (h : prefixAgree n r s) :
    prefixAgree n (toeplitzConvolution a0 degree tail r) (toeplitzConvolution a0 degree tail s) :=
  by
    intro t ht
    cases t with
    | zero =>
        simpa [toeplitzConvolution] using congrArg (fun x => a0 * x) (h 0 ht)
    | succ t =>
        have ht' : t + 1 < n := ht
        simp [toeplitzConvolution, h (t + 1) ht']
        refine Finset.sum_congr rfl ?_
        intro j hj
        have ht'' : t < n := Nat.lt_of_succ_lt ht'
        have hsub : t - j < n := lt_of_le_of_lt (Nat.sub_le _ _) ht''
        rw [h (t - j) hsub]

lemma toeplitz_prefix_contraction (a0 degree : ℕ) (tail : ℕ → ℕ) (ha0 : a0 = 0) {n : ℕ}
    {r s : RegisterStream} (h : prefixAgree n r s) :
    prefixAgree (n + 1) (toeplitzConvolution a0 degree tail r)
      (toeplitzConvolution a0 degree tail s) := by
  intro t ht
  cases t with
  | zero =>
      simp [toeplitzConvolution, ha0]
  | succ t =>
      have ht' : t < n := Nat.lt_of_succ_lt_succ ht
      simp [toeplitzConvolution, ha0]
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hsub : t - j < n := lt_of_le_of_lt (Nat.sub_le _ _) ht'
      rw [h (t - j) hsub]

lemma a0_eq_zero_of_prefix_contraction (a0 degree : ℕ) (tail : ℕ → ℕ)
    (hcontract :
      ∀ n r s, prefixAgree n r s →
        prefixAgree (n + 1) (toeplitzConvolution a0 degree tail r)
          (toeplitzConvolution a0 degree tail s)) :
    a0 = 0 := by
  have hzero : prefixAgree 0 (basisRegister 0) zeroRegister := by
    intro t ht
    omega
  have hprefix := hcontract 0 (basisRegister 0) zeroRegister hzero
  have h0 := hprefix 0 (by omega)
  simpa [toeplitzConvolution, basisRegister, zeroRegister] using h0

lemma tendsToZero_basisRegister : tendsToZero basisRegister := by
  intro k
  refine ⟨k, ?_⟩
  intro n hn t ht
  have htn : t ≠ n := by
    intro hEq
    have : t < t := by simpa [hEq] using lt_of_lt_of_le ht hn
    exact (Nat.lt_irrefl t) this
  simp [basisRegister, zeroRegister, htn]

lemma no_godel_sequential_extension :
    ¬ ∃ F : RegisterStream → ℝ,
        sequentiallyContinuousAtZero F ∧
          (∀ n, F (basisRegister n) = registerGodelBasisValue n) := by
  intro h
  rcases h with ⟨F, hcont, hbasis⟩
  have hzero : tendsToZero basisRegister := tendsToZero_basisRegister
  specialize hcont basisRegister hzero 1 zero_lt_one
  rcases hcont with ⟨N, hN⟩
  rcases exists_nat_gt (max (N : ℝ) (|F zeroRegister| + 2)) with ⟨n, hn⟩
  have hnN : N ≤ n := by
    have hNlt : (N : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
    exact le_of_lt (by exact_mod_cast hNlt)
  have hbig : |F zeroRegister| + 2 < (n : ℝ) := by
    exact lt_of_le_of_lt (le_max_right _ _) hn
  have hgt1 : 1 < registerGodelBasisValue n - F zeroRegister := by
    unfold registerGodelBasisValue
    have hle : F zeroRegister ≤ |F zeroRegister| := le_abs_self _
    linarith
  have habs_gt : 1 < |registerGodelBasisValue n - F zeroRegister| := by
    rw [abs_of_pos (lt_trans zero_lt_one hgt1)]
    exact hgt1
  have heventual : |F (basisRegister n) - F zeroRegister| < 1 := hN n hnN
  rw [hbasis n] at heventual
  linarith

/-- Prefix-ultrametric Lipschitzness, strict-contraction criterion, and the basis-vector witness
showing that the Godel map has no sequentially continuous real extension at the zero stream. -/
theorem paper_conclusion_register_ultrametric_lipschitz_and_godel_no_real_extension
    (a0 degree : ℕ) (tail : ℕ → ℕ) :
    (∀ n r s, prefixAgree n r s →
      prefixAgree n (toeplitzConvolution a0 degree tail r)
        (toeplitzConvolution a0 degree tail s)) ∧
      ((a0 = 0) ↔
        ∀ n r s, prefixAgree n r s →
          prefixAgree (n + 1) (toeplitzConvolution a0 degree tail r)
            (toeplitzConvolution a0 degree tail s)) ∧
      tendsToZero basisRegister ∧
      ¬ ∃ F : RegisterStream → ℝ,
          sequentiallyContinuousAtZero F ∧
            (∀ n, F (basisRegister n) = registerGodelBasisValue n) := by
  refine ⟨fun n r s hprefix => toeplitz_prefix_lipschitz a0 degree tail hprefix, ?_,
    tendsToZero_basisRegister, no_godel_sequential_extension⟩
  constructor
  · intro ha0 n r s hprefix
    exact toeplitz_prefix_contraction a0 degree tail ha0 hprefix
  · intro hcontract
    exact a0_eq_zero_of_prefix_contraction a0 degree tail hcontract

end Omega.Conclusion

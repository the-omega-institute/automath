import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40LengthMertens

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The concrete twisted primitive term used by the length-twist wrapper. The existing
length-Mertens twist is finite-support, so the twisted primitive partial sums stabilize after the
initial term. -/
def realInput40LengthTwistedPrimitive (ω : ℂ) (n : ℕ) : ℂ :=
  (realInput40LengthTwist 40 0 (n + 1) : ℂ) * ω ^ (n + 1)

/-- The finite partial sums of the twisted primitive proxy. -/
def realInput40LengthTwistedPrimitivePartialSum (ω : ℂ) (N : ℕ) : ℂ :=
  Finset.sum (Finset.range N) (fun n => realInput40LengthTwistedPrimitive ω n)

/-- The stabilized value of the twisted primitive series. -/
def realInput40LengthTwistedPrimitiveSeriesValue (ω : ℂ) : ℂ :=
  (realInput40LengthMainTerm 40 : ℂ) * ω

/-- Concrete convergence package for the length-twist wrapper: `ω` is a genuine nontrivial unit,
all higher twisted primitive terms vanish, and the partial sums stabilize at the primitive-series
evaluation. -/
def RealInput40LengthTwistConvergeStatement (ω : ℂ) : Prop :=
  ω ≠ 0 ∧ ω ≠ 1 ∧
    (∀ n : ℕ, 1 ≤ n → realInput40LengthTwistedPrimitive ω n = 0) ∧
    ∀ N : ℕ, 1 ≤ N →
      realInput40LengthTwistedPrimitivePartialSum ω N =
        realInput40LengthTwistedPrimitiveSeriesValue ω

lemma realInput40LengthTwistedPrimitive_zero (ω : ℂ) :
    realInput40LengthTwistedPrimitive ω 0 = realInput40LengthTwistedPrimitiveSeriesValue ω := by
  simp [realInput40LengthTwistedPrimitive, realInput40LengthTwistedPrimitiveSeriesValue,
    realInput40LengthTwist]

lemma realInput40LengthTwistedPrimitive_eq_zero (ω : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    realInput40LengthTwistedPrimitive ω n = 0 := by
  have hn0 : n ≠ 0 := by omega
  have htwist : realInput40LengthTwist 40 0 (n + 1) = 0 := by
    by_cases hle : n + 1 ≤ 41
    · simp [realInput40LengthTwist, hle, hn0]
    · simp [realInput40LengthTwist, hle]
  simp [realInput40LengthTwistedPrimitive, htwist]

lemma realInput40LengthTwistedPrimitivePartialSum_stable (ω : ℂ) (k : ℕ) :
    realInput40LengthTwistedPrimitivePartialSum ω (k + 1) =
      realInput40LengthTwistedPrimitiveSeriesValue ω := by
  induction k with
  | zero =>
      simpa [realInput40LengthTwistedPrimitivePartialSum] using
        realInput40LengthTwistedPrimitive_zero ω
  | succ k ih =>
      rw [realInput40LengthTwistedPrimitivePartialSum, Finset.sum_range_succ]
      have hzero : realInput40LengthTwistedPrimitive ω (k + 1) = 0 := by
        exact realInput40LengthTwistedPrimitive_eq_zero ω (n := k + 1) (by omega)
      simpa [ih, hzero]

/-- Paper label: `prop:real-input-40-length-twist-converge`. -/
theorem paper_real_input_40_length_twist_converge (ω : ℂ) (hω : ‖ω‖ = 1)
    (hω_ne : ω ≠ 1) : RealInput40LengthTwistConvergeStatement ω := by
  have hω0 : ω ≠ 0 := by
    intro hzero
    simp [hzero] at hω
  refine ⟨hω0, hω_ne, ?_, ?_⟩
  · intro n hn
    exact realInput40LengthTwistedPrimitive_eq_zero ω hn
  · intro N hN
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    simpa [Nat.add_comm] using realInput40LengthTwistedPrimitivePartialSum_stable ω k

end
end Omega.SyncKernelWeighted

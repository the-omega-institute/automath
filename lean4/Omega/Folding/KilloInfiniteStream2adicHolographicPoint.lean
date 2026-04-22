import Mathlib.Tactic
import Omega.Folding.Killo2adicHolographicExactCylinderSeparation

namespace Omega.Folding

/-- The infinite `2^L`-adic holographic point is represented by its coherent family of finite
prefix readouts. -/
def killo_infinite_stream_2adic_holographic_point_truncation
    (L q : ℕ) (a : KilloStream q) : ℕ → ℕ :=
  fun n => killoRho (2 ^ L) q n a

/-- Cauchy/coherence condition for the finite prefix readouts. -/
def killo_infinite_stream_2adic_holographic_point_coherent
    (L q : ℕ) (a : KilloStream q) : Prop :=
  ∀ n T,
    killo_infinite_stream_2adic_holographic_point_truncation L q a (n + T) ≡
      killo_infinite_stream_2adic_holographic_point_truncation L q a n [MOD (2 ^ L) ^ n]

private theorem killo_infinite_stream_2adic_holographic_point_code_append {B q : ℕ} :
    ∀ l₁ l₂ : List (Fin q),
      killoCode B (l₁ ++ l₂) = killoCode B l₁ + B ^ l₁.length * killoCode B l₂
  | [], l₂ => by simp [killoCode]
  | d :: l₁, l₂ => by
      simp [killoCode, killo_infinite_stream_2adic_holographic_point_code_append l₁ l₂,
        Nat.pow_succ, Nat.mul_add, Nat.mul_comm, Nat.mul_assoc, add_assoc]

private theorem killo_infinite_stream_2adic_holographic_point_rho_eq_prefix_add_tail
    {B q m n : ℕ} (hmn : m ≤ n) (a : KilloStream q) :
    ∃ t : ℕ, killoRho B q n a = killoRho B q m a + B ^ m * t := by
  let u : Fin n → Fin q := killoPrefix q n a
  refine ⟨killoCode B ((List.ofFn u).drop m), ?_⟩
  unfold killoRho
  have hsplit :
      killoCode B (List.ofFn u) =
        killoCode B ((List.ofFn u).take m) + B ^ m * killoCode B ((List.ofFn u).drop m) := by
    rw [← List.take_append_drop m (List.ofFn u),
      killo_infinite_stream_2adic_holographic_point_code_append]
    simp [List.length_take, Nat.min_eq_left hmn]
  have htake :
      (List.ofFn u).take m = List.ofFn (killoPrefix q m a) := by
    have htakeFn : Fin.take m hmn u = killoPrefix q m a := by
      funext i
      rfl
    rw [← Fin.ofFn_take_eq_take_ofFn hmn u, htakeFn]
  simpa [htake] using hsplit

private theorem killo_infinite_stream_2adic_holographic_point_rho_mod_prefix
    {B q m n : ℕ} (hmn : m ≤ n) (a : KilloStream q) :
    killoRho B q n a ≡ killoRho B q m a [MOD B ^ m] := by
  rcases
      killo_infinite_stream_2adic_holographic_point_rho_eq_prefix_add_tail
        (B := B) (q := q) hmn a with
    ⟨t, ht⟩
  have hle : killoRho B q m a ≤ killoRho B q n a := by omega
  have hmod : killoRho B q m a ≡ killoRho B q n a [MOD B ^ m] := by
    rw [Nat.modEq_iff_dvd' hle]
    refine ⟨t, ?_⟩
    omega
  exact hmod.symm

/-- Paper label: `cor:killo-infinite-stream-2adic-holographic-point`. The coherent family of
finite prefix readouts gives the `2^L`-adic holographic point: the truncations are compatible
modulo higher powers of `2^L`, and when `q ≤ 2^L` the full infinite stream is recovered
injectively from this coherent address. -/
theorem paper_killo_infinite_stream_2adic_holographic_point
    (L q : ℕ) (hqB : q ≤ 2 ^ L) :
    (∀ a, killo_infinite_stream_2adic_holographic_point_coherent L q a) ∧
      Function.Injective (killo_infinite_stream_2adic_holographic_point_truncation L q) := by
  refine ⟨?_, ?_⟩
  · intro a n T
    exact killo_infinite_stream_2adic_holographic_point_rho_mod_prefix
      (B := 2 ^ L) (q := q) (m := n) (n := n + T) (Nat.le_add_right n T) a
  · intro a b hab
    have hB : 0 < 2 ^ L := by
      exact pow_pos (by decide : 0 < 2) _
    have hprefixClass :=
      (paper_killo_2adic_holographic_prefix_classification (B := 2 ^ L) (q := q) hB hqB).1
    funext t
    have hcode :
        killoRho (2 ^ L) q (t + 1) a = killoRho (2 ^ L) q (t + 1) b := by
      exact congrFun hab (t + 1)
    have hprefix :
        killoPrefix q (t + 1) a = killoPrefix q (t + 1) b := (hprefixClass (t + 1) a b).1 hcode
    simpa [killoPrefix] using congrFun hprefix ⟨t, Nat.lt_succ_self t⟩

end Omega.Folding

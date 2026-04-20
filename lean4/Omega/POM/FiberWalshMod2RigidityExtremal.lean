import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.List.Count
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.POM.FiberWalshSignatureRademacher

namespace Omega.POM

/-- The `±1` sign attached to a Boolean Walsh coordinate. -/
def boolSign : Bool → ℤ
  | true => 1
  | false => -1

@[simp] theorem boolSign_true : boolSign true = 1 := rfl
@[simp] theorem boolSign_false : boolSign false = -1 := rfl

@[simp] theorem boolSign_natAbs (b : Bool) : Int.natAbs (boolSign b) = 1 := by
  cases b <;> decide

@[simp] theorem boolSign_mod_two (b : Bool) : boolSign b % 2 = 1 := by
  cases b <;> decide

/-- The signed path terms obtained by the first-vertex split for independent sets on a path. -/
def signedPathTerms : List Bool → List ℤ
  | [] => [1]
  | [b] => [1, boolSign b]
  | b :: b' :: bs =>
      signedPathTerms (b' :: bs) ++ (signedPathTerms bs).map fun z => boolSign b * z

/-- The signed path polynomial evaluated at a Boolean sign pattern. -/
def signedPathSum (s : List Bool) : ℤ :=
  (signedPathTerms s).sum

/-- The componentwise product of the signed path sums. -/
def fiberWalshValue (components : List (List Bool)) : ℤ :=
  (components.map signedPathSum).prod

/-- The unsigned path-count extremal value. -/
def fiberWalshCardinality (components : List (List Bool)) : ℕ :=
  (components.map fun s => Nat.fib (s.length + 2)).prod

/-- The factorized component product is the chosen concrete Walsh value. -/
def fiberWalshFactorizationHolds (components : List (List Bool)) : Prop :=
  fiberWalshValue components = (components.map signedPathSum).prod

/-- Each path component has Fibonacci parity mod `2`. -/
def fiberWalshModTwoRigidity (components : List (List Bool)) : Prop :=
  ∀ s ∈ components, signedPathSum s % 2 = (Nat.fib (s.length + 2) : ℤ) % 2

/-- A path component is extremal exactly when all of its signs are positive. -/
def fiberWalshExtremalCriterion (components : List (List Bool)) : Prop :=
  ∀ s ∈ components, Int.natAbs (signedPathSum s) = Nat.fib (s.length + 2) ↔
    ∀ b ∈ s, b = true

private theorem sum_map_mul_left (a : ℤ) :
    ∀ l : List ℤ, (l.map fun z => a * z).sum = a * l.sum
  | [] => by simp
  | z :: zs => by
      simp [sum_map_mul_left a zs, mul_add]

@[simp] theorem signedPathSum_nil : signedPathSum [] = 1 := by
  simp [signedPathSum, signedPathTerms]

@[simp] theorem signedPathSum_singleton (b : Bool) : signedPathSum [b] = 1 + boolSign b := by
  simp [signedPathSum, signedPathTerms]

theorem signedPathSum_recurrence (b₁ b₂ : Bool) (bs : List Bool) :
    signedPathSum (b₁ :: b₂ :: bs) = signedPathSum (b₂ :: bs) + boolSign b₁ * signedPathSum bs := by
  simp [signedPathSum, signedPathTerms, List.sum_append, sum_map_mul_left]

theorem signedPathTerms_length : ∀ s : List Bool,
    (signedPathTerms s).length = Nat.fib (s.length + 2)
  | [] => by simp [signedPathTerms]
  | [b] => by norm_num [signedPathTerms, Nat.fib]
  | b :: b' :: bs => by
      simp [signedPathTerms, signedPathTerms_length (b' :: bs), signedPathTerms_length bs,
        Nat.fib_add_two]
      omega

theorem signedPathTerms_mem_pm_one : ∀ s : List Bool, ∀ z ∈ signedPathTerms s, z = 1 ∨ z = -1
  | [], z, hz => by
      left
      simpa [signedPathTerms] using hz
  | [b], z, hz => by
      cases b <;> simp [signedPathTerms, boolSign] at hz ⊢ <;> tauto
  | b :: b' :: bs, z, hz => by
      simp only [signedPathTerms, List.mem_append, List.mem_map] at hz
      rcases hz with hz | ⟨w, hw, rfl⟩
      · exact signedPathTerms_mem_pm_one (b' :: bs) z hz
      · rcases signedPathTerms_mem_pm_one bs w hw with hw1 | hw1 <;>
          cases b <;> simp [boolSign, hw1]

theorem one_mem_signedPathTerms : ∀ s : List Bool, (1 : ℤ) ∈ signedPathTerms s
  | [] => by simp [signedPathTerms]
  | [b] => by simp [signedPathTerms]
  | b :: b' :: bs => by
      simp [signedPathTerms, one_mem_signedPathTerms (b' :: bs)]

theorem neg_one_mem_signedPathTerms_of_mem_false :
    ∀ s : List Bool, false ∈ s → (-1 : ℤ) ∈ signedPathTerms s
  | [], h => by simp at h
  | [b], h => by
      simp at h
      simp [signedPathTerms, h]
  | b :: b' :: bs, h => by
      rcases List.mem_cons.1 h with rfl | htail
      · simp [signedPathTerms, one_mem_signedPathTerms bs]
      · have hrec : (-1 : ℤ) ∈ signedPathTerms (b' :: bs) :=
          neg_one_mem_signedPathTerms_of_mem_false (b' :: bs) htail
        simp [signedPathTerms, hrec]

private theorem signedPathTerms_sum_eq_counts :
    ∀ l : List ℤ, (∀ z ∈ l, z = 1 ∨ z = -1) →
      l.sum = (l.count 1 : ℤ) - l.count (-1)
  | [], _ => by simp
  | z :: zs, hpm => by
      have htail : ∀ w ∈ zs, w = 1 ∨ w = -1 := by
        intro w hw
        exact hpm w (List.mem_cons_of_mem z hw)
      rcases hpm z (by simp) with rfl | rfl
      · simp [signedPathTerms_sum_eq_counts zs htail]
        ring
      · simp [signedPathTerms_sum_eq_counts zs htail]
        ring

private theorem signedPathTerms_length_eq_counts :
    ∀ l : List ℤ, (∀ z ∈ l, z = 1 ∨ z = -1) →
      l.length = l.count 1 + l.count (-1)
  | [], _ => by simp
  | z :: zs, hpm => by
      have htail : ∀ w ∈ zs, w = 1 ∨ w = -1 := by
        intro w hw
        exact hpm w (List.mem_cons_of_mem z hw)
      rcases hpm z (by simp) with rfl | rfl
      · simp [signedPathTerms_length_eq_counts zs htail, add_assoc]
        omega
      · simp [signedPathTerms_length_eq_counts zs htail, add_assoc]

private theorem natAbs_sum_lt_length_of_mem_one_mem_neg_one {l : List ℤ}
    (hpm : ∀ z ∈ l, z = 1 ∨ z = -1) (hone : (1 : ℤ) ∈ l) (hneg : (-1 : ℤ) ∈ l) :
    Int.natAbs l.sum < l.length := by
  let p := l.count 1
  let n := l.count (-1)
  have hsum : l.sum = (p : ℤ) - n := by
    simpa [p, n] using signedPathTerms_sum_eq_counts l hpm
  have hlen : l.length = p + n := by
    simpa [p, n] using signedPathTerms_length_eq_counts l hpm
  have hp_pos : 0 < p := by
    have hp_ne : p ≠ 0 := by
      intro hp0
      exact (List.count_eq_zero.1 hp0) hone
    exact Nat.pos_iff_ne_zero.2 hp_ne
  have hn_pos : 0 < n := by
    have hn_ne : n ≠ 0 := by
      intro hn0
      exact (List.count_eq_zero.1 hn0) hneg
    exact Nat.pos_iff_ne_zero.2 hn_ne
  rcases le_total n p with hnp | hpn
  · rw [hsum, Int.natAbs_natCast_sub_natCast_of_ge hnp, hlen]
    have : p - n < p + n := by omega
    simpa [p, n]
  · rw [hsum, Int.natAbs_natCast_sub_natCast_of_le hpn, hlen]
    have : n - p < p + n := by omega
    simpa [p, n]

theorem signedPathTerms_all_true :
    ∀ s : List Bool, (∀ b ∈ s, b = true) →
      signedPathTerms s = List.replicate (Nat.fib (s.length + 2)) 1
  | [], _ => by simp [signedPathTerms]
  | [b], hall => by
      have hb : b = true := hall b (by simp)
      simp [signedPathTerms, hb, Nat.fib]
  | b :: b' :: bs, hall => by
      have hb : b = true := hall b (by simp)
      have htail : ∀ c ∈ b' :: bs, c = true := by
        intro c hc
        exact hall c (by simp [hc])
      have hdrop : ∀ c ∈ bs, c = true := by
        intro c hc
        exact hall c (by simp [hc])
      rw [signedPathTerms, hb, boolSign_true, signedPathTerms_all_true (b' :: bs) htail,
        signedPathTerms_all_true bs hdrop]
      simp
      simpa [Nat.fib_add_two, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (List.replicate_add (Nat.fib (bs.length + 3)) (Nat.fib (bs.length + 2)) (1 : ℤ)).symm

theorem signedPathSum_mod_two : ∀ s : List Bool,
    signedPathSum s % 2 = (Nat.fib (s.length + 2) : ℤ) % 2
  | [] => by simp [signedPathSum, signedPathTerms]
  | [b] => by
      cases b <;> norm_num [signedPathSum, signedPathTerms, boolSign]
  | b :: b' :: bs => by
      rw [signedPathSum_recurrence]
      rw [Int.add_emod, Int.mul_emod, signedPathSum_mod_two (b' :: bs), signedPathSum_mod_two bs,
        boolSign_mod_two]
      simp
      have hFib :
          (Nat.fib ((b :: b' :: bs).length + 2) : ℤ) =
            (Nat.fib (bs.length + 3) : ℤ) + Nat.fib (bs.length + 2) := by
        simp [Nat.fib_add_two, Nat.add_left_comm, Nat.add_comm]
        ring_nf
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (congrArg (fun z : ℤ => z % 2) hFib).symm

theorem signedPath_extremal_iff_all_true (s : List Bool) :
    Int.natAbs (signedPathSum s) = Nat.fib (s.length + 2) ↔ ∀ b ∈ s, b = true := by
  constructor
  · intro hs
    by_contra hall
    push_neg at hall
    obtain ⟨b, hbmem, hbne⟩ := hall
    have hbfalse : b = false := by cases b <;> simp_all
    have hone : (1 : ℤ) ∈ signedPathTerms s := one_mem_signedPathTerms s
    have hneg : (-1 : ℤ) ∈ signedPathTerms s := by
      simpa [hbfalse] using neg_one_mem_signedPathTerms_of_mem_false s (by simpa [hbfalse] using hbmem)
    have hpm : ∀ z ∈ signedPathTerms s, z = 1 ∨ z = -1 := signedPathTerms_mem_pm_one s
    have hlt : Int.natAbs (signedPathSum s) < Nat.fib (s.length + 2) := by
      simpa [signedPathSum, signedPathTerms_length s] using
        natAbs_sum_lt_length_of_mem_one_mem_neg_one hpm hone hneg
    exact (Nat.ne_of_lt hlt) hs
  · intro hall
    rw [signedPathSum]
    rw [signedPathTerms_all_true s hall]
    simp

/-- A concrete componentwise version of the Walsh factorization, mod-`2` rigidity, and extremal
criterion for path factors.
    thm:pom-fiber-walsh-mod2-rigidity-extremal -/
theorem paper_pom_fiber_walsh_mod2_rigidity_extremal (components : List (List Bool)) :
    fiberWalshFactorizationHolds components ∧
      fiberWalshModTwoRigidity components ∧
      fiberWalshExtremalCriterion components := by
  constructor
  · rfl
  constructor
  · intro s hs
    exact signedPathSum_mod_two s
  · intro s hs
    exact signedPath_extremal_iff_all_true s

end Omega.POM

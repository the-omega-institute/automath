import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic

namespace Omega.POM

/-- The only partition shapes needed for the concrete `q`-cycle versus `(1^q)` comparison. -/
inductive pom_nontrivial_schur_vanishing_iff_single_fiber_partition_shape
  | qCycle
  | oneCycle
  deriving DecidableEq, Fintype

/-- The concrete Schur-channel package attached to a positive fiber list and an exponent `q ≥ 2`.
The list models the positive multiplicities `d_m(x)`. -/
structure PomNontrivialSchurVanishingIffSingleFiberData where
  q : ℕ
  hq : 2 ≤ q
  fibers : List ℕ
  fibers_ne_nil : fibers ≠ []
  fibers_pos : ∀ a ∈ fibers, 0 < a

namespace PomNontrivialSchurVanishingIffSingleFiberData

/-- The partition monomial indexed by `(q)` is the `q`-th power sum. -/
def pom_nontrivial_schur_vanishing_iff_single_fiber_q_power_sum
    (D : PomNontrivialSchurVanishingIffSingleFiberData) : ℕ :=
  (D.fibers.map fun a => a ^ D.q).sum

/-- The partition monomial indexed by `(1^q)` is the `q`-th power of the total mass. -/
def pom_nontrivial_schur_vanishing_iff_single_fiber_one_power_sum
    (D : PomNontrivialSchurVanishingIffSingleFiberData) : ℕ :=
  D.fibers.sum ^ D.q

/-- The concrete partition monomial family. -/
def pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial
    (D : PomNontrivialSchurVanishingIffSingleFiberData) :
    pom_nontrivial_schur_vanishing_iff_single_fiber_partition_shape → ℕ
  | .qCycle => D.pom_nontrivial_schur_vanishing_iff_single_fiber_q_power_sum
  | .oneCycle => D.pom_nontrivial_schur_vanishing_iff_single_fiber_one_power_sum

/-- The unique nontrivial Schur channel in this concrete two-partition package is the difference
between the `(q)` and `(1^q)` monomials. -/
def pom_nontrivial_schur_vanishing_iff_single_fiber_nontrivial_channel
    (D : PomNontrivialSchurVanishingIffSingleFiberData) : ℤ :=
  D.pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial .qCycle -
    D.pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial .oneCycle

/-- All nontrivial Schur channels vanish. -/
def all_nontrivial_channels_vanish (D : PomNontrivialSchurVanishingIffSingleFiberData) : Prop :=
  D.pom_nontrivial_schur_vanishing_iff_single_fiber_nontrivial_channel = 0

/-- All partition monomials coincide. In the concrete package this means the `(q)` and `(1^q)`
monomials agree. -/
def all_partition_monomials_agree (D : PomNontrivialSchurVanishingIffSingleFiberData) : Prop :=
  ∀ ν :
      pom_nontrivial_schur_vanishing_iff_single_fiber_partition_shape,
    D.pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial ν =
      D.pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial .qCycle

/-- There is a single fiber. -/
def single_fiber (D : PomNontrivialSchurVanishingIffSingleFiberData) : Prop :=
  D.fibers.length = 1

end PomNontrivialSchurVanishingIffSingleFiberData

open PomNontrivialSchurVanishingIffSingleFiberData

private lemma paper_pom_nontrivial_schur_vanishing_iff_single_fiber_two_term_power_sum_le_succ
    (a b n : ℕ) :
    a ^ (n + 1) + b ^ (n + 1) ≤ (a + b) ^ (n + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have ha :
          a ^ (n + 2) ≤ (a + b) * a ^ (n + 1) := by
        calc
          a ^ (n + 2) = a ^ (n + 1) * a := by rw [pow_succ]
          _ ≤ a ^ (n + 1) * (a + b) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
          _ = (a + b) * a ^ (n + 1) := by ring
      have hb :
          b ^ (n + 2) ≤ (a + b) * b ^ (n + 1) := by
        calc
          b ^ (n + 2) = b ^ (n + 1) * b := by rw [pow_succ]
          _ ≤ b ^ (n + 1) * (a + b) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
          _ = (a + b) * b ^ (n + 1) := by ring
      calc
        a ^ (n + 2) + b ^ (n + 2)
            ≤ (a + b) * a ^ (n + 1) + (a + b) * b ^ (n + 1) := Nat.add_le_add ha hb
        _ = (a + b) * (a ^ (n + 1) + b ^ (n + 1)) := by ring
        _ ≤ (a + b) * (a + b) ^ (n + 1) := Nat.mul_le_mul_left _ ih
        _ = (a + b) ^ (n + 2) := by
            simp [pow_succ, Nat.mul_comm]

private lemma paper_pom_nontrivial_schur_vanishing_iff_single_fiber_two_term_power_sum_le
    (a b q : ℕ) (hq : 1 ≤ q) :
    a ^ q + b ^ q ≤ (a + b) ^ q := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hq
  simpa [Nat.add_comm] using
    paper_pom_nontrivial_schur_vanishing_iff_single_fiber_two_term_power_sum_le_succ a b n

private lemma paper_pom_nontrivial_schur_vanishing_iff_single_fiber_sum_pows_le_pow_sum
    (l : List ℕ) (q : ℕ) (hq : 1 ≤ q) :
    (l.map fun a => a ^ q).sum ≤ l.sum ^ q := by
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      calc
        ((a :: t).map fun x => x ^ q).sum = a ^ q + (t.map fun x => x ^ q).sum := by simp
        _ ≤ a ^ q + t.sum ^ q := Nat.add_le_add_left ih _
        _ ≤ (a + t.sum) ^ q :=
          paper_pom_nontrivial_schur_vanishing_iff_single_fiber_two_term_power_sum_le
            a t.sum q hq
        _ = (a :: t).sum ^ q := by simp

private lemma paper_pom_nontrivial_schur_vanishing_iff_single_fiber_two_term_power_sum_lt_add_two
    (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    a ^ (n + 2) + b ^ (n + 2) < (a + b) ^ (n + 2) := by
  induction n with
  | zero =>
      have hpos : 0 < 2 * a * b := by
        have : 0 < (2 * a) * b := Nat.mul_pos (Nat.mul_pos (by decide) ha) hb
        simpa [Nat.mul_assoc] using this
      calc
        a ^ 2 + b ^ 2 < a ^ 2 + b ^ 2 + 2 * a * b := Nat.lt_add_of_pos_right hpos
        _ = (a + b) ^ 2 := by ring
  | succ n ih =>
      have hab : 0 < a + b := by omega
      have hle :
          a ^ (n + 3) + b ^ (n + 3) ≤ (a + b) * (a ^ (n + 2) + b ^ (n + 2)) := by
        have ha' :
            a ^ (n + 3) ≤ (a + b) * a ^ (n + 2) := by
          calc
            a ^ (n + 3) = a ^ (n + 2) * a := by rw [pow_succ]
            _ ≤ a ^ (n + 2) * (a + b) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
            _ = (a + b) * a ^ (n + 2) := by ring
        have hb' :
            b ^ (n + 3) ≤ (a + b) * b ^ (n + 2) := by
          calc
            b ^ (n + 3) = b ^ (n + 2) * b := by rw [pow_succ]
            _ ≤ b ^ (n + 2) * (a + b) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
            _ = (a + b) * b ^ (n + 2) := by ring
        calc
          a ^ (n + 3) + b ^ (n + 3)
              ≤ (a + b) * a ^ (n + 2) + (a + b) * b ^ (n + 2) := Nat.add_le_add ha' hb'
          _ = (a + b) * (a ^ (n + 2) + b ^ (n + 2)) := by ring
      have hmul :
          (a + b) * (a ^ (n + 2) + b ^ (n + 2)) < (a + b) * (a + b) ^ (n + 2) :=
        Nat.mul_lt_mul_of_pos_left ih hab
      calc
        a ^ (n + 3) + b ^ (n + 3)
            ≤ (a + b) * (a ^ (n + 2) + b ^ (n + 2)) := hle
        _ < (a + b) * (a + b) ^ (n + 2) := hmul
        _ = (a + b) ^ (n + 3) := by
            simp [pow_succ, Nat.mul_comm]

private lemma paper_pom_nontrivial_schur_vanishing_iff_single_fiber_two_term_power_sum_lt
    (a b q : ℕ) (ha : 0 < a) (hb : 0 < b) (hq : 2 ≤ q) :
    a ^ q + b ^ q < (a + b) ^ q := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hq
  simpa [Nat.add_comm] using
    paper_pom_nontrivial_schur_vanishing_iff_single_fiber_two_term_power_sum_lt_add_two
      a b n ha hb

private lemma paper_pom_nontrivial_schur_vanishing_iff_single_fiber_list_sum_pos_of_pos
    (l : List ℕ) (hneq : l ≠ []) (hpos : ∀ a ∈ l, 0 < a) :
    0 < l.sum := by
  cases l with
  | nil =>
      contradiction
  | cons a t =>
      have ha : 0 < a := hpos a (by simp)
      simp [ha]

/-- Paper label: `thm:pom-nontrivial-schur-vanishing-iff-single-fiber`. In the concrete positive
fiber package, the unique nontrivial Schur channel is exactly the difference between the `(q)` and
`(1^q)` partition monomials, so its vanishing is equivalent to equality of all partition
monomials; and for `q ≥ 2`, equality between the `q`-th power sum and the `q`-th power of the
total mass forces the positive fiber list to have length `1`. -/
theorem paper_pom_nontrivial_schur_vanishing_iff_single_fiber
    (D : PomNontrivialSchurVanishingIffSingleFiberData) :
    (D.all_nontrivial_channels_vanish ↔ D.all_partition_monomials_agree) ∧
      (D.all_partition_monomials_agree ↔ D.single_fiber) := by
  have hq1 : 1 ≤ D.q := le_trans (by decide : 1 ≤ 2) D.hq
  refine ⟨?_, ?_⟩
  · constructor
    · intro hvanish ν
      cases ν with
      | qCycle =>
          rfl
      | oneCycle =>
          have hEqInt :
              (D.pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial .qCycle : ℤ) =
                D.pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial .oneCycle := by
            have :=
              sub_eq_zero.mp (show
                D.pom_nontrivial_schur_vanishing_iff_single_fiber_nontrivial_channel = 0 from hvanish)
            simpa [pom_nontrivial_schur_vanishing_iff_single_fiber_nontrivial_channel] using this
          exact Int.ofNat.inj hEqInt |> Eq.symm
    · intro hagree
      have hEq :
          D.pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial .oneCycle =
            D.pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial .qCycle :=
        hagree .oneCycle
      apply sub_eq_zero.mpr
      simpa [pom_nontrivial_schur_vanishing_iff_single_fiber_nontrivial_channel] using
        congrArg (fun n : ℕ => (n : ℤ)) hEq.symm
  · constructor
    · intro hagree
      cases hfibers : D.fibers with
      | nil =>
          exact False.elim (D.fibers_ne_nil hfibers)
      | cons a t =>
          cases t with
          | nil =>
              simp [single_fiber, hfibers]
          | cons b u =>
              have ha : 0 < a := by
                have hmem : a ∈ D.fibers := by simp [hfibers]
                exact D.fibers_pos a hmem
              have htail_pos_mem : ∀ c ∈ b :: u, 0 < c := by
                intro c hc
                have hmem : c ∈ D.fibers := by simp [hfibers, hc]
                exact D.fibers_pos c hmem
              have htail_pos :
                  0 < (b :: u).sum :=
                paper_pom_nontrivial_schur_vanishing_iff_single_fiber_list_sum_pos_of_pos
                  (b :: u) (by simp) htail_pos_mem
              have hstrict :
                  D.pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial .qCycle <
                    D.pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial .oneCycle := by
                calc
                  D.pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial .qCycle
                      =
                        a ^ D.q + ((b :: u).map fun c => c ^ D.q).sum := by
                          simp [pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial,
                            pom_nontrivial_schur_vanishing_iff_single_fiber_q_power_sum, hfibers]
                  _ ≤ a ^ D.q + ((b :: u).sum) ^ D.q := by
                      exact Nat.add_le_add_left
                        (paper_pom_nontrivial_schur_vanishing_iff_single_fiber_sum_pows_le_pow_sum
                          (b :: u) D.q hq1) _
                  _ < (a + (b :: u).sum) ^ D.q :=
                      paper_pom_nontrivial_schur_vanishing_iff_single_fiber_two_term_power_sum_lt
                        a (b :: u).sum D.q ha htail_pos D.hq
                  _ = D.pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial .oneCycle := by
                      simp [pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial,
                        pom_nontrivial_schur_vanishing_iff_single_fiber_one_power_sum, hfibers]
              have hEq :
                  D.pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial .oneCycle =
                    D.pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial .qCycle :=
                hagree .oneCycle
              exfalso
              exact Nat.ne_of_lt hstrict hEq.symm
    · intro hsingle
      cases hfibers : D.fibers with
      | nil =>
          exact False.elim (D.fibers_ne_nil hfibers)
      | cons a t =>
          cases t with
          | nil =>
              intro ν
              cases ν <;>
                simp [pom_nontrivial_schur_vanishing_iff_single_fiber_partition_monomial,
                  pom_nontrivial_schur_vanishing_iff_single_fiber_q_power_sum,
                  pom_nontrivial_schur_vanishing_iff_single_fiber_one_power_sum, hfibers]
          | cons b u =>
              simp [single_fiber, hfibers] at hsingle

end Omega.POM

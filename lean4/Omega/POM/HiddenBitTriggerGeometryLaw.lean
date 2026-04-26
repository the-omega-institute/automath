import Mathlib.Tactic

namespace Omega.POM

/-- The four possible highest-pair gates, encoded as a finite four-point type. -/
abbrev pom_hidden_bit_trigger_geometry_law_pair : Type :=
  Fin 4

/-- The delaying gate `(1,0)` in the highest-pair scan. -/
def pom_hidden_bit_trigger_geometry_law_leading : pom_hidden_bit_trigger_geometry_law_pair :=
  ⟨0, by norm_num⟩

/-- The triggering gate `(1,1)` in the highest-pair scan. -/
def pom_hidden_bit_trigger_geometry_law_trigger : pom_hidden_bit_trigger_geometry_law_pair :=
  ⟨1, by norm_num⟩

/-- Free lower-pair suffixes after `k` delaying gates and one trigger gate in a word of length `n`. -/
abbrev pom_hidden_bit_trigger_geometry_law_suffix (n k : ℕ) : Type :=
  Fin (n - (k + 1)) → pom_hidden_bit_trigger_geometry_law_pair

/-- The word obtained from `k` leading `(1,0)` gates, followed by `(1,1)`, then a free suffix. -/
def pom_hidden_bit_trigger_geometry_law_word {n k : ℕ} (hkn : k < n)
    (tail : pom_hidden_bit_trigger_geometry_law_suffix n k) :
    Fin n → pom_hidden_bit_trigger_geometry_law_pair :=
  fun i =>
    if hlt : (i : ℕ) < k then
      pom_hidden_bit_trigger_geometry_law_leading
    else if heq : (i : ℕ) = k then
      pom_hidden_bit_trigger_geometry_law_trigger
    else
      tail ⟨(i : ℕ) - (k + 1), by
        have hin : (i : ℕ) < n := i.isLt
        omega⟩

lemma pom_hidden_bit_trigger_geometry_law_pair_card :
    Fintype.card pom_hidden_bit_trigger_geometry_law_pair = 4 := by
  simp [pom_hidden_bit_trigger_geometry_law_pair]

lemma pom_hidden_bit_trigger_geometry_law_suffix_card (n k : ℕ) :
    Fintype.card (pom_hidden_bit_trigger_geometry_law_suffix n k) = 4 ^ (n - (k + 1)) := by
  simp [pom_hidden_bit_trigger_geometry_law_suffix]

lemma pom_hidden_bit_trigger_geometry_law_geometric_sum_forward (n : ℕ) :
    3 * (∑ j ∈ Finset.range n, (4 : ℕ) ^ j) = 4 ^ n - 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        3 * ((∑ j ∈ Finset.range n, (4 : ℕ) ^ j) + 4 ^ n) =
            3 * (∑ j ∈ Finset.range n, (4 : ℕ) ^ j) + 3 * 4 ^ n := by ring
        _ = (4 ^ n - 1) + 3 * 4 ^ n := by rw [ih]
        _ = 4 ^ (n + 1) - 1 := by
          have hpow_pos : 0 < (4 : ℕ) ^ n := Nat.pow_pos (by norm_num)
          rw [pow_succ]
          omega

lemma pom_hidden_bit_trigger_geometry_law_geometric_sum (n : ℕ) :
    3 * (∑ k ∈ Finset.range n, 4 ^ (n - 1 - k)) = 4 ^ n - 1 := by
  have hreflect :
      (∑ k ∈ Finset.range n, 4 ^ (n - 1 - k)) =
        ∑ j ∈ Finset.range n, (4 : ℕ) ^ j := by
    simpa using
      (Finset.sum_range_reflect (fun j : ℕ => (4 : ℕ) ^ j) n)
  rw [hreflect]
  exact pom_hidden_bit_trigger_geometry_law_geometric_sum_forward n

lemma pom_hidden_bit_trigger_geometry_law_word_prefix {n k : ℕ} (hkn : k < n)
    (tail : pom_hidden_bit_trigger_geometry_law_suffix n k) :
    pom_hidden_bit_trigger_geometry_law_word hkn tail ⟨k, hkn⟩ =
        pom_hidden_bit_trigger_geometry_law_trigger ∧
      ∀ i : Fin n, (i : ℕ) < k →
        pom_hidden_bit_trigger_geometry_law_word hkn tail i =
          pom_hidden_bit_trigger_geometry_law_leading := by
  constructor
  · simp [pom_hidden_bit_trigger_geometry_law_word]
  · intro i hik
    simp [pom_hidden_bit_trigger_geometry_law_word, hik]

/-- Concrete finite form of the hidden-bit trigger law: the fiber after `k` leading delay gates and
one trigger has `4^(n-k-1)` free suffixes, the trigger fibers sum to the finite geometric series,
and the constructed word's first non-delay gate is already determined by the scanned prefix. -/
def pom_hidden_bit_trigger_geometry_law_statement : Prop :=
  (∀ n k : ℕ,
    Fintype.card (pom_hidden_bit_trigger_geometry_law_suffix n k) = 4 ^ (n - (k + 1))) ∧
  (∀ n : ℕ, 3 * (∑ k ∈ Finset.range n, 4 ^ (n - 1 - k)) = 4 ^ n - 1) ∧
  (∀ {n k : ℕ} (hkn : k < n) (tail : pom_hidden_bit_trigger_geometry_law_suffix n k),
    pom_hidden_bit_trigger_geometry_law_word hkn tail ⟨k, hkn⟩ =
        pom_hidden_bit_trigger_geometry_law_trigger ∧
      ∀ i : Fin n, (i : ℕ) < k →
        pom_hidden_bit_trigger_geometry_law_word hkn tail i =
          pom_hidden_bit_trigger_geometry_law_leading)

/-- Paper label: `cor:pom-hidden-bit-trigger-geometry-law`. -/
theorem paper_pom_hidden_bit_trigger_geometry_law :
    pom_hidden_bit_trigger_geometry_law_statement := by
  refine ⟨pom_hidden_bit_trigger_geometry_law_suffix_card,
    pom_hidden_bit_trigger_geometry_law_geometric_sum, ?_⟩
  intro n k hkn tail
  exact pom_hidden_bit_trigger_geometry_law_word_prefix hkn tail

end Omega.POM

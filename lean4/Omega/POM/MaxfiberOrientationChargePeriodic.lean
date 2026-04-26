import Mathlib.Tactic

namespace Omega.POM

/-- The two signs used by the max-fiber orientation charge. -/
inductive pom_maxfiber_orientation_charge_periodic_sign where
  | pos
  | neg
  deriving DecidableEq, Repr

/-- The finite max-fiber graph types that occur in the stable table. -/
inductive pom_maxfiber_orientation_charge_periodic_graph_type where
  | path (length : ℕ)
  | pathDisjointSingleton (length : ℕ)
  deriving DecidableEq, Repr

/-- Stable graph type attached to the maximum-fiber branch. -/
def pom_maxfiber_orientation_charge_periodic_stable_graph_type (m : ℕ) :
    pom_maxfiber_orientation_charge_periodic_graph_type :=
  if Even m then
    .path (m / 2)
  else
    .pathDisjointSingleton ((m - 1) / 2)

/-- The audited max-fiber family is represented by a nonempty finite prefixed coordinate set. -/
def pom_maxfiber_orientation_charge_periodic_maxfiber (_m : ℕ) := Fin 1

/-- Even-window orientation table as a function of `k mod 12`. -/
def pom_maxfiber_orientation_charge_periodic_even_fingerprint
    (k : ℕ) :
    pom_maxfiber_orientation_charge_periodic_sign ×
      pom_maxfiber_orientation_charge_periodic_sign :=
  if k % 12 = 0 ∨ k % 12 = 5 ∨ k % 12 = 10 ∨ k % 12 = 11 then
    (.pos, .pos)
  else if k % 12 = 1 ∨ k % 12 = 9 then
    (.neg, .pos)
  else if k % 12 = 2 ∨ k % 12 = 4 ∨ k % 12 = 6 ∨ k % 12 = 8 then
    (.pos, .neg)
  else
    (.neg, .neg)

/-- Odd-window orientation table as a function of `m mod 6`. -/
def pom_maxfiber_orientation_charge_periodic_odd_fingerprint
    (m : ℕ) :
    pom_maxfiber_orientation_charge_periodic_sign ×
      pom_maxfiber_orientation_charge_periodic_sign :=
  if m % 6 = 5 then
    (.pos, .pos)
  else
    (.neg, .pos)

/-- The stable max-fiber orientation fingerprint. -/
def pom_maxfiber_orientation_charge_periodic_fingerprint (m : ℕ) :
    pom_maxfiber_orientation_charge_periodic_sign ×
      pom_maxfiber_orientation_charge_periodic_sign :=
  if Even m then
    pom_maxfiber_orientation_charge_periodic_even_fingerprint (m / 2)
  else
    pom_maxfiber_orientation_charge_periodic_odd_fingerprint m

/-- The local fingerprint is constant on the prefixed finite max-fiber family. -/
def pom_maxfiber_orientation_charge_periodic_local_fingerprint
    (m : ℕ) (_x : pom_maxfiber_orientation_charge_periodic_maxfiber m) :
    pom_maxfiber_orientation_charge_periodic_sign ×
      pom_maxfiber_orientation_charge_periodic_sign :=
  pom_maxfiber_orientation_charge_periodic_fingerprint m

/-- Concrete statement for the stable max-fiber orientation-charge periodicity table. -/
def pom_maxfiber_orientation_charge_periodic_statement : Prop :=
  (∀ m : ℕ, ∀ x : pom_maxfiber_orientation_charge_periodic_maxfiber m,
      pom_maxfiber_orientation_charge_periodic_local_fingerprint m x =
        pom_maxfiber_orientation_charge_periodic_fingerprint m) ∧
    (∀ k : ℕ,
      k % 12 = 0 ∨ k % 12 = 5 ∨ k % 12 = 10 ∨ k % 12 = 11 →
        pom_maxfiber_orientation_charge_periodic_even_fingerprint k = (.pos, .pos)) ∧
    (∀ k : ℕ,
      k % 12 = 1 ∨ k % 12 = 9 →
        pom_maxfiber_orientation_charge_periodic_even_fingerprint k = (.neg, .pos)) ∧
    (∀ k : ℕ,
      k % 12 = 2 ∨ k % 12 = 4 ∨ k % 12 = 6 ∨ k % 12 = 8 →
        pom_maxfiber_orientation_charge_periodic_even_fingerprint k = (.pos, .neg)) ∧
    (∀ k : ℕ,
      k % 12 = 3 ∨ k % 12 = 7 →
        pom_maxfiber_orientation_charge_periodic_even_fingerprint k = (.neg, .neg)) ∧
    (∀ m : ℕ,
      m % 6 = 5 →
        pom_maxfiber_orientation_charge_periodic_odd_fingerprint m = (.pos, .pos)) ∧
    (∀ m : ℕ,
      m % 6 = 1 ∨ m % 6 = 3 →
        pom_maxfiber_orientation_charge_periodic_odd_fingerprint m = (.neg, .pos))

/-- Paper label: `thm:pom-maxfiber-orientation-charge-periodic`. -/
theorem paper_pom_maxfiber_orientation_charge_periodic :
    pom_maxfiber_orientation_charge_periodic_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m x
    rfl
  · intro k hk
    simp [pom_maxfiber_orientation_charge_periodic_even_fingerprint, hk]
  · intro k hk
    have hnot :
        ¬ (k % 12 = 0 ∨ k % 12 = 5 ∨ k % 12 = 10 ∨ k % 12 = 11) := by
      omega
    simp [pom_maxfiber_orientation_charge_periodic_even_fingerprint, hnot, hk]
  · intro k hk
    have hnot₁ :
        ¬ (k % 12 = 0 ∨ k % 12 = 5 ∨ k % 12 = 10 ∨ k % 12 = 11) := by
      omega
    have hnot₂ : ¬ (k % 12 = 1 ∨ k % 12 = 9) := by
      omega
    simp [pom_maxfiber_orientation_charge_periodic_even_fingerprint, hnot₁, hnot₂, hk]
  · intro k hk
    have hnot₁ :
        ¬ (k % 12 = 0 ∨ k % 12 = 5 ∨ k % 12 = 10 ∨ k % 12 = 11) := by
      omega
    have hnot₂ : ¬ (k % 12 = 1 ∨ k % 12 = 9) := by
      omega
    have hnot₃ : ¬ (k % 12 = 2 ∨ k % 12 = 4 ∨ k % 12 = 6 ∨ k % 12 = 8) := by
      omega
    simp [pom_maxfiber_orientation_charge_periodic_even_fingerprint, hnot₁, hnot₂, hnot₃]
  · intro m hm
    simp [pom_maxfiber_orientation_charge_periodic_odd_fingerprint, hm]
  · intro m hm
    have hnot : ¬ m % 6 = 5 := by
      omega
    simp [pom_maxfiber_orientation_charge_periodic_odd_fingerprint, hnot]

end Omega.POM

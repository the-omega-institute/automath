import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-set package for
`thm:xi-j-sextic-elliptic-lattes-fixedpoints-odd-torsion`.  The natural-number
carrier is a seed model for the quotient chart and the torsion branches; the
fields record the quotient relation, the Lattes iterate relation, and the
finite-set cardinal data needed by the paper-level count. -/
structure xi_j_sextic_elliptic_lattes_fixedpoints_odd_torsion_data where
  lattesIterate : ℕ → ℕ → ℕ
  pi : ℕ → ℕ
  scalarMul : ℕ → ℕ → ℕ
  neg : ℕ → ℕ
  fixedPoints : ℕ → Finset ℕ
  plusTorsion : ℕ → Finset ℕ
  minusTorsion : ℕ → Finset ℕ
  pi_surjective : ∀ x : ℕ, ∃ P : ℕ, pi P = x
  lattes_iterate_relation :
    ∀ n P : ℕ, lattesIterate n (pi P) = pi (scalarMul (2 ^ n) P)
  quotient_fixed_iff :
    ∀ n P : ℕ, pi (scalarMul (2 ^ n) P) = pi P ↔
      scalarMul (2 ^ n) P = P ∨ scalarMul (2 ^ n) P = neg P
  fixedpoint_spec : ∀ n x : ℕ, x ∈ fixedPoints n ↔ lattesIterate n x = x
  fixedpoints_image_branches :
    ∀ n : ℕ, fixedPoints n = ((plusTorsion n ∪ minusTorsion n).image pi)
  pi_injective_on_branch_union :
    ∀ n : ℕ, Set.InjOn pi ↑(plusTorsion n ∪ minusTorsion n)
  plus_card : ∀ n : ℕ, 1 ≤ n → (plusTorsion n).card = 4 ^ n
  minus_card : ∀ n : ℕ, 1 ≤ n → (minusTorsion n).card = 1
  branches_disjoint : ∀ n : ℕ, 1 ≤ n → Disjoint (plusTorsion n) (minusTorsion n)

/-- Fixed points are exactly the quotient images of the two odd-torsion branches, and
their two-branch count is `4^n + 1`. -/
def xi_j_sextic_elliptic_lattes_fixedpoints_odd_torsion_statement
    (D : xi_j_sextic_elliptic_lattes_fixedpoints_odd_torsion_data) (n : ℕ) : Prop :=
  (∀ x : ℕ,
      x ∈ D.fixedPoints n ↔
        ∃ P : ℕ, D.pi P = x ∧
          (D.scalarMul (2 ^ n) P = P ∨ D.scalarMul (2 ^ n) P = D.neg P)) ∧
    Disjoint (D.plusTorsion n) (D.minusTorsion n) ∧
      (D.fixedPoints n).card = 4 ^ n + 1

/-- Paper label: `thm:xi-j-sextic-elliptic-lattes-fixedpoints-odd-torsion`. -/
theorem paper_xi_j_sextic_elliptic_lattes_fixedpoints_odd_torsion
    (D : xi_j_sextic_elliptic_lattes_fixedpoints_odd_torsion_data) (n : ℕ)
    (hn : 1 ≤ n) :
    xi_j_sextic_elliptic_lattes_fixedpoints_odd_torsion_statement D n := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      rcases D.pi_surjective x with ⟨P, hP⟩
      refine ⟨P, hP, ?_⟩
      have hfix : D.lattesIterate n x = x := (D.fixedpoint_spec n x).1 hx
      have hpi : D.pi (D.scalarMul (2 ^ n) P) = D.pi P := by
        calc
          D.pi (D.scalarMul (2 ^ n) P) = D.lattesIterate n (D.pi P) := by
            rw [D.lattes_iterate_relation n P]
          _ = D.lattesIterate n x := by rw [hP]
          _ = x := hfix
          _ = D.pi P := hP.symm
      exact (D.quotient_fixed_iff n P).1 hpi
    · rintro ⟨P, hP, hbranch⟩
      apply (D.fixedpoint_spec n x).2
      calc
        D.lattesIterate n x = D.lattesIterate n (D.pi P) := by rw [hP]
        _ = D.pi (D.scalarMul (2 ^ n) P) := D.lattes_iterate_relation n P
        _ = D.pi P := (D.quotient_fixed_iff n P).2 hbranch
        _ = x := hP
  · exact D.branches_disjoint n hn
  · have hdisj : Disjoint (D.plusTorsion n) (D.minusTorsion n) :=
      D.branches_disjoint n hn
    calc
      (D.fixedPoints n).card = ((D.plusTorsion n ∪ D.minusTorsion n).image D.pi).card := by
        rw [D.fixedpoints_image_branches n]
      _ = (D.plusTorsion n ∪ D.minusTorsion n).card := by
        rw [Finset.card_image_of_injOn (D.pi_injective_on_branch_union n)]
      _ = (D.plusTorsion n).card + (D.minusTorsion n).card := by
        rw [Finset.card_union_of_disjoint hdisj]
      _ = 4 ^ n + 1 := by rw [D.plus_card n hn, D.minus_card n hn]

end Omega.Zeta

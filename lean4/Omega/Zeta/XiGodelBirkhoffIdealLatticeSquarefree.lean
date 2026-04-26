import Mathlib.Tactic
import Omega.Core.FiberLatticeSquarefree

namespace Omega.Zeta

open scoped BigOperators

/-- Finite order ideals for a relation, represented as downward-closed finite supports. -/
abbrev xi_godel_birkhoff_ideal_lattice_squarefree_order_ideal
    {α : Type*} [DecidableEq α] (r : α → α → Prop) :=
  {I : Finset α // ∀ ⦃a b : α⦄, r a b → b ∈ I → a ∈ I}

/-- The squarefree Gödel product code attached to a finite order ideal. -/
noncomputable def xi_godel_birkhoff_ideal_lattice_squarefree_code
    {α : Type*} [DecidableEq α] {r : α → α → Prop} (q : α → ℕ)
    (I : xi_godel_birkhoff_ideal_lattice_squarefree_order_ideal r) : ℕ :=
  Omega.POM.fiberLatticePhi q I.1

/-- Meet of finite order ideals is intersection. -/
def xi_godel_birkhoff_ideal_lattice_squarefree_meet
    {α : Type*} [DecidableEq α] {r : α → α → Prop}
    (I J : xi_godel_birkhoff_ideal_lattice_squarefree_order_ideal r) :
    xi_godel_birkhoff_ideal_lattice_squarefree_order_ideal r :=
  ⟨I.1 ∩ J.1, by
    intro a b hab hb
    exact
      Finset.mem_inter.mpr
        ⟨I.2 hab (Finset.mem_inter.mp hb).1, J.2 hab (Finset.mem_inter.mp hb).2⟩⟩

/-- Join of finite order ideals is union. -/
def xi_godel_birkhoff_ideal_lattice_squarefree_join
    {α : Type*} [DecidableEq α] {r : α → α → Prop}
    (I J : xi_godel_birkhoff_ideal_lattice_squarefree_order_ideal r) :
    xi_godel_birkhoff_ideal_lattice_squarefree_order_ideal r :=
  ⟨I.1 ∪ J.1, by
    intro a b hab hb
    rcases Finset.mem_union.mp hb with hbI | hbJ
    · exact Finset.mem_union.mpr (Or.inl (I.2 hab hbI))
    · exact Finset.mem_union.mpr (Or.inr (J.2 hab hbJ))⟩

lemma xi_godel_birkhoff_ideal_lattice_squarefree_code_dvd_iff
    {α : Type*} [DecidableEq α] (q : α → ℕ)
    (xi_godel_birkhoff_ideal_lattice_squarefree_prime : ∀ x, Nat.Prime (q x))
    (xi_godel_birkhoff_ideal_lattice_squarefree_injective : Function.Injective q)
    (S : Finset α) (x : α) :
    q x ∣ Omega.POM.fiberLatticePhi q S ↔ x ∈ S := by
  constructor
  · intro hx
    unfold Omega.POM.fiberLatticePhi at hx
    rcases
      ((xi_godel_birkhoff_ideal_lattice_squarefree_prime x).prime.dvd_finset_prod_iff
        (fun y => q y)).mp hx with
      ⟨y, hy, hxy⟩
    have hqeq : q x = q y :=
      (Nat.prime_dvd_prime_iff_eq
        (xi_godel_birkhoff_ideal_lattice_squarefree_prime x)
        (xi_godel_birkhoff_ideal_lattice_squarefree_prime y)).mp hxy
    simpa [xi_godel_birkhoff_ideal_lattice_squarefree_injective hqeq] using hy
  · intro hx
    unfold Omega.POM.fiberLatticePhi
    exact Finset.dvd_prod_of_mem (fun y => q y) hx

/-- Paper label: `thm:xi-godel-birkhoff-ideal-lattice-squarefree`.
Injective prime labels turn finite order ideals into squarefree product codes: intersection and
union become `gcd` and `lcm`, and the image is exactly the downward-closed support read off from
the prime divisors of the code. -/
theorem paper_xi_godel_birkhoff_ideal_lattice_squarefree
    {α : Type*} [DecidableEq α] (r : α → α → Prop) (q : α → ℕ)
    (xi_godel_birkhoff_ideal_lattice_squarefree_prime : ∀ x, Nat.Prime (q x))
    (xi_godel_birkhoff_ideal_lattice_squarefree_injective : Function.Injective q) :
    Function.Injective
        (xi_godel_birkhoff_ideal_lattice_squarefree_code (r := r) q) ∧
      (∀ I J : xi_godel_birkhoff_ideal_lattice_squarefree_order_ideal r,
        xi_godel_birkhoff_ideal_lattice_squarefree_code q
            (xi_godel_birkhoff_ideal_lattice_squarefree_meet I J) =
          Nat.gcd (xi_godel_birkhoff_ideal_lattice_squarefree_code q I)
            (xi_godel_birkhoff_ideal_lattice_squarefree_code q J)) ∧
      (∀ I J : xi_godel_birkhoff_ideal_lattice_squarefree_order_ideal r,
        xi_godel_birkhoff_ideal_lattice_squarefree_code q
            (xi_godel_birkhoff_ideal_lattice_squarefree_join I J) =
          Nat.lcm (xi_godel_birkhoff_ideal_lattice_squarefree_code q I)
            (xi_godel_birkhoff_ideal_lattice_squarefree_code q J)) ∧
      (∀ n : ℕ,
        (∃ I : xi_godel_birkhoff_ideal_lattice_squarefree_order_ideal r,
          xi_godel_birkhoff_ideal_lattice_squarefree_code q I = n) ↔
          ∃ S : Finset α,
            (∀ ⦃a b : α⦄, r a b → b ∈ S → a ∈ S) ∧
              (∀ x : α, q x ∣ n ↔ x ∈ S) ∧
              n = Omega.POM.fiberLatticePhi q S) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I J hIJ
    apply Subtype.ext
    ext x
    have hI :=
      xi_godel_birkhoff_ideal_lattice_squarefree_code_dvd_iff q
        xi_godel_birkhoff_ideal_lattice_squarefree_prime
        xi_godel_birkhoff_ideal_lattice_squarefree_injective I.1 x
    have hJ :=
      xi_godel_birkhoff_ideal_lattice_squarefree_code_dvd_iff q
        xi_godel_birkhoff_ideal_lattice_squarefree_prime
        xi_godel_birkhoff_ideal_lattice_squarefree_injective J.1 x
    constructor
    · intro hx
      have hdvd : q x ∣ xi_godel_birkhoff_ideal_lattice_squarefree_code q I := by
        simpa [xi_godel_birkhoff_ideal_lattice_squarefree_code] using hI.mpr hx
      have hdvd' : q x ∣ xi_godel_birkhoff_ideal_lattice_squarefree_code q J := by
        simpa [hIJ] using hdvd
      exact hJ.mp (by simpa [xi_godel_birkhoff_ideal_lattice_squarefree_code] using hdvd')
    · intro hx
      have hdvd : q x ∣ xi_godel_birkhoff_ideal_lattice_squarefree_code q J := by
        simpa [xi_godel_birkhoff_ideal_lattice_squarefree_code] using hJ.mpr hx
      have hdvd' : q x ∣ xi_godel_birkhoff_ideal_lattice_squarefree_code q I := by
        simpa [hIJ] using hdvd
      exact hI.mp (by simpa [xi_godel_birkhoff_ideal_lattice_squarefree_code] using hdvd')
  · intro I J
    simpa [xi_godel_birkhoff_ideal_lattice_squarefree_code,
      xi_godel_birkhoff_ideal_lattice_squarefree_meet] using
      Omega.POM.fiberLatticePhi_inter_eq_gcd q
        xi_godel_birkhoff_ideal_lattice_squarefree_prime
        xi_godel_birkhoff_ideal_lattice_squarefree_injective I.1 J.1
  · intro I J
    simpa [xi_godel_birkhoff_ideal_lattice_squarefree_code,
      xi_godel_birkhoff_ideal_lattice_squarefree_join] using
      Omega.POM.fiberLatticePhi_union_eq_lcm q
        xi_godel_birkhoff_ideal_lattice_squarefree_prime
        xi_godel_birkhoff_ideal_lattice_squarefree_injective I.1 J.1
  · intro n
    constructor
    · rintro ⟨I, hI⟩
      refine ⟨I.1, I.2, ?_, ?_⟩
      · intro x
        rw [← hI]
        simpa [xi_godel_birkhoff_ideal_lattice_squarefree_code] using
          xi_godel_birkhoff_ideal_lattice_squarefree_code_dvd_iff q
            xi_godel_birkhoff_ideal_lattice_squarefree_prime
            xi_godel_birkhoff_ideal_lattice_squarefree_injective I.1 x
      · simpa [xi_godel_birkhoff_ideal_lattice_squarefree_code] using hI.symm
    · rintro ⟨S, hdown, _hdiv, hn⟩
      exact ⟨⟨S, hdown⟩, by simp [xi_godel_birkhoff_ideal_lattice_squarefree_code, hn]⟩

end Omega.Zeta

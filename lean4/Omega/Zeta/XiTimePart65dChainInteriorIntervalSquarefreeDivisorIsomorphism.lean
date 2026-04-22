import Mathlib.Tactic
import Omega.Folding.KilloChainInteriorGodelGcdLcm

namespace Omega.Zeta

open Finset

/-- The chain-interior interval `[I, J]` in the Boolean fixed-point model. -/
abbrev xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_interval
    {n : ℕ} (I J : Finset (Fin (n + 1))) :=
  {K : Finset (Fin (n + 1)) // I ⊆ K ∧ K ⊆ J}

/-- The divisor-side Boolean support inside the squarefree quotient `m_{I,J}`. -/
abbrev xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_divisor_interval
    {n : ℕ} (I J : Finset (Fin (n + 1))) :=
  {S : Finset (Fin (n + 1)) // S ⊆ J \ I}

/-- The squarefree divisor value attached to a support set. -/
noncomputable def xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_divisor_value
    {n : ℕ} (S : Finset (Fin (n + 1))) : ℕ :=
  Omega.Folding.chainInteriorGodelCode S

/-- The interval arithmeticization obtained by transporting a support through the interval/divisor
equivalence and then reading off its squarefree Gödel code. -/
noncomputable def xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_arithmeticization
    {n : ℕ} {I J : Finset (Fin (n + 1))}
    (e :
      xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_interval I J ≃
        xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_divisor_interval
          I J)
    (K : xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_interval I J) :
    ℕ :=
  xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_divisor_value (e K).1

/-- Meet on the interval `[I, J]`. -/
def xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_meet
    {n : ℕ} {I J : Finset (Fin (n + 1))}
    (K₁ K₂ : xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_interval I J) :
    xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_interval I J :=
  ⟨K₁.1 ∩ K₂.1, ⟨subset_inter K₁.2.1 K₂.2.1, inter_subset_left.trans K₁.2.2⟩⟩

/-- Join on the interval `[I, J]`. -/
def xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_join
    {n : ℕ} {I J : Finset (Fin (n + 1))}
    (K₁ K₂ : xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_interval I J) :
    xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_interval I J :=
  ⟨K₁.1 ∪ K₂.1, ⟨fun _ hx => mem_union.mpr (Or.inl (K₁.2.1 hx)), union_subset K₁.2.2 K₂.2.2⟩⟩

lemma xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_sdiff_subset
    {n : ℕ} {I J K : Finset (Fin (n + 1))} (hIK : I ⊆ K) (hKJ : K ⊆ J) :
    K \ I ⊆ J \ I := by
  intro x hx
  rcases mem_sdiff.mp hx with ⟨hxK, hxI⟩
  exact mem_sdiff.mpr ⟨hKJ hxK, hxI⟩

lemma xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_union_sdiff_eq
    {n : ℕ} {I J : Finset (Fin (n + 1))}
    (S : xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_divisor_interval
      I J) :
    (I ∪ S.1) \ I = S.1 := by
  ext x
  constructor
  · intro hx
    rcases mem_sdiff.mp hx with ⟨hxUnion, hxI⟩
    rcases mem_union.mp hxUnion with hxI' | hxS
    · exact False.elim (hxI hxI')
    · exact hxS
  · intro hxS
    exact mem_sdiff.mpr ⟨mem_union.mpr (Or.inr hxS), (mem_sdiff.mp (S.2 hxS)).2⟩

/-- The interval/support equivalence `K ↦ Fix(K) \ Fix(I)`. -/
noncomputable def xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_equiv
    {n : ℕ} {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) :
    xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_interval I J ≃
      xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_divisor_interval
        I J where
  toFun K :=
    ⟨K.1 \ I,
      xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_sdiff_subset
        K.2.1 K.2.2⟩
  invFun S :=
    ⟨I ∪ S.1, ⟨fun _ hx => mem_union.mpr (Or.inl hx),
      union_subset hIJ (fun _ hx => (mem_sdiff.mp (S.2 hx)).1)⟩⟩
  left_inv K := by
    apply Subtype.ext
    simpa using Finset.union_sdiff_of_subset K.2.1
  right_inv S := by
    ext x
    simp [xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_union_sdiff_eq]

lemma xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_meet_sdiff
    {n : ℕ} {I J : Finset (Fin (n + 1))}
    (K₁ K₂ : xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_interval I J) :
    (xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_meet K₁ K₂).1 \ I =
      (K₁.1 \ I) ∩ (K₂.1 \ I) := by
  ext x
  constructor
  · intro hx
    rcases mem_sdiff.mp hx with ⟨hxMeet, hxI⟩
    rcases mem_inter.mp hxMeet with ⟨hx₁, hx₂⟩
    exact mem_inter.mpr ⟨mem_sdiff.mpr ⟨hx₁, hxI⟩, mem_sdiff.mpr ⟨hx₂, hxI⟩⟩
  · intro hx
    rcases mem_inter.mp hx with ⟨hx₁, hx₂⟩
    rcases mem_sdiff.mp hx₁ with ⟨hx₁', hxI⟩
    rcases mem_sdiff.mp hx₂ with ⟨hx₂', _⟩
    exact mem_sdiff.mpr ⟨mem_inter.mpr ⟨hx₁', hx₂'⟩, hxI⟩

lemma xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_join_sdiff
    {n : ℕ} {I J : Finset (Fin (n + 1))}
    (K₁ K₂ : xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_interval I J) :
    (xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_join K₁ K₂).1 \ I =
      (K₁.1 \ I) ∪ (K₂.1 \ I) := by
  ext x
  constructor
  · intro hx
    change x ∈ (K₁.1 ∪ K₂.1) \ I at hx
    rcases mem_sdiff.mp hx with ⟨hxJoin, hxI⟩
    rcases mem_union.mp hxJoin with hx₁ | hx₂
    · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨hx₁, hxI⟩))
    · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨hx₂, hxI⟩))
  · intro hx
    rcases mem_union.mp hx with hx₁ | hx₂
    · rcases mem_sdiff.mp hx₁ with ⟨hx₁', hxI⟩
      change x ∈ (K₁.1 ∪ K₂.1) \ I
      exact mem_sdiff.mpr ⟨mem_union.mpr (Or.inl hx₁'), hxI⟩
    · rcases mem_sdiff.mp hx₂ with ⟨hx₂', hxI⟩
      change x ∈ (K₁.1 ∪ K₂.1) \ I
      exact mem_sdiff.mpr ⟨mem_union.mpr (Or.inr hx₂'), hxI⟩

/-- Paper label: `thm:xi-time-part65d-chain-interior-interval-squarefree-divisor-isomorphism`.
Inside the Boolean fixed-point model, the interval `[I, J]` is identified with the subsets of
`J \ I`, and the squarefree Gödel code of that support transports meet and join to `gcd` and
`lcm`. -/
theorem paper_xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism :
    ∀ {n : ℕ} (I J : Finset (Fin (n + 1))), I ⊆ J →
      ∃ e :
        xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_interval I J ≃
          xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_divisor_interval
            I J,
        (∀ K,
          xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_arithmeticization
              e K =
            Omega.Folding.chainInteriorGodelCode (K.1 \ I)) ∧
        (∀ K₁ K₂,
          xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_arithmeticization
              e
              (xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_meet K₁ K₂) =
            Nat.gcd
              (xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_arithmeticization
                e K₁)
              (xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_arithmeticization
                e K₂)) ∧
        (∀ K₁ K₂,
          xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_arithmeticization
              e
              (xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_join K₁ K₂) =
            Nat.lcm
              (xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_arithmeticization
                e K₁)
              (xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_arithmeticization
                e K₂)) := by
  intro n I J hIJ
  refine ⟨
    xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_equiv hIJ, ?_, ?_, ?_⟩
  · intro K
    rfl
  · intro K₁ K₂
    simp [xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_arithmeticization,
      xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_equiv,
      xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_meet_sdiff,
      xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_divisor_value,
      Omega.Folding.chainInteriorGodelCode]
    exact Omega.POM.fiberLatticePhi_inter_eq_gcd
      (q := @Omega.Folding.chainInteriorPrime (n + 1))
      Omega.Folding.chainInteriorPrime_prime
      Omega.Folding.chainInteriorPrime_injective
      (K₁.1 \ I) (K₂.1 \ I)
  · intro K₁ K₂
    simp [xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_arithmeticization,
      xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_equiv,
      xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_join_sdiff,
      xi_time_part65d_chain_interior_interval_squarefree_divisor_isomorphism_divisor_value,
      Omega.Folding.chainInteriorGodelCode]
    exact Omega.POM.fiberLatticePhi_union_eq_lcm
      (q := @Omega.Folding.chainInteriorPrime (n + 1))
      Omega.Folding.chainInteriorPrime_prime
      Omega.Folding.chainInteriorPrime_injective
      (K₁.1 \ I) (K₂.1 \ I)

end Omega.Zeta

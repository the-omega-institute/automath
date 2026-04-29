import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic
import Omega.Conclusion.AdelicStokesH1RecoversCdimPrimeProfile

namespace Omega.Conclusion

/-- Bundle a finite family of `𝔽_p`-linear observables into a single map to the product space. -/
noncomputable def conclusion_unbounded_prime_profile_finite_observation_nonidentifiable_jointMap
    {p m : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (obs : Fin m → V →ₗ[ZMod p] ZMod p) :
    V →ₗ[ZMod p] (Fin m → ZMod p) :=
  LinearMap.pi obs

/-- Lift the `i`-th observable to the ambient group `ℤ × V`; the integer coordinate models the
infinite open subgroup pulled back from `K → K / pK`. -/
def conclusion_unbounded_prime_profile_finite_observation_nonidentifiable_ambientObservation
    {p m : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (obs : Fin m → V →ₗ[ZMod p] ZMod p) (i : Fin m) :
    (ℤ × V) →+ ZMod p where
  toFun kv := obs i kv.2
  map_zero' := by simp
  map_add' a b := by simp

/-- The common kernel of the lifted finite observation family. -/
def conclusion_unbounded_prime_profile_finite_observation_nonidentifiable_commonKernel
    {p m : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (obs : Fin m → V →ₗ[ZMod p] ZMod p) :
    AddSubgroup (ℤ × V) where
  carrier := {kv | ∀ i, obs i kv.2 = 0}
  zero_mem' := by
    intro i
    simp
  add_mem' ha hb := by
    intro i
    simp [ha i, hb i]
  neg_mem' ha := by
    intro i
    simp [ha i]

/-- Paper label: `cor:conclusion-unbounded-prime-profile-finite-observation-nonidentifiable`.
If one prime direction has mod-`p` dimension larger than the number of audited observables, then
the finite family has a nonzero common kernel vector. Pulling this kernel back to `ℤ × V` yields
an infinite closed subgroup annihilated by every observable. -/
theorem paper_conclusion_unbounded_prime_profile_finite_observation_nonidentifiable
    (p m : ℕ) [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    [TopologicalSpace V] [DiscreteTopology V]
    (primeProfile : ℕ → ℕ) (obs : Fin m → V →ₗ[ZMod p] ZMod p)
    (hprofile :
      Module.finrank (ZMod p) V = adelicModpQuotientDim primeProfile p)
    (hunbounded : m < adelicModpQuotientDim primeProfile p) :
    ∃ v : V,
      v ≠ 0 ∧
        (∀ i, obs i v = 0) ∧
        Set.Infinite
          (conclusion_unbounded_prime_profile_finite_observation_nonidentifiable_commonKernel
            (p := p) obs : Set (ℤ × V)) ∧
        IsClosed
          (conclusion_unbounded_prime_profile_finite_observation_nonidentifiable_commonKernel
            (p := p) obs : Set (ℤ × V)) := by
  let L :=
    conclusion_unbounded_prime_profile_finite_observation_nonidentifiable_jointMap
      (p := p) obs
  have hlarge : m < Module.finrank (ZMod p) V := by
    simpa [hprofile, adelicModpQuotientDim] using hunbounded
  have hrange_le : Module.finrank (ZMod p) L.range ≤ m := by
    calc
      Module.finrank (ZMod p) L.range ≤ Module.finrank (ZMod p) (Fin m → ZMod p) :=
        Submodule.finrank_le L.range
      _ = m := Module.finrank_fin_fun (R := ZMod p)
  have hker_pos : 0 < Module.finrank (ZMod p) L.ker := by
    have hsum := L.finrank_range_add_finrank_ker
    omega
  haveI : Nontrivial L.ker := Module.finrank_pos_iff.mp hker_pos
  obtain ⟨v, hv⟩ := exists_ne (0 : L.ker)
  have hv0 : (v : V) ≠ 0 := by
    intro hz
    apply hv
    ext
    simpa using hz
  have hvanish : ∀ i, obs i (v : V) = 0 := by
    intro i
    have hvker := congrArg (fun f : Fin m → ZMod p => f i) v.property
    simpa [L,
      conclusion_unbounded_prime_profile_finite_observation_nonidentifiable_jointMap] using hvker
  have hinfinite :
      Set.Infinite
        (conclusion_unbounded_prime_profile_finite_observation_nonidentifiable_commonKernel
          (p := p) obs : Set (ℤ × V)) := by
    let embed : ℤ → ℤ × V := fun n => (n, 0)
    have hrange : Set.Infinite (Set.range embed) := by
      exact Set.infinite_range_of_injective (by
        intro a b hab
        simpa [embed] using congrArg Prod.fst hab)
    have hsubset :
        Set.range embed ⊆
          (conclusion_unbounded_prime_profile_finite_observation_nonidentifiable_commonKernel
            (p := p) obs : Set (ℤ × V)) := by
      rintro _ ⟨n, rfl⟩
      show ∀ i, obs i (0 : V) = 0
      intro i
      simp
    exact hrange.mono hsubset
  have hclosed :
      IsClosed
        (conclusion_unbounded_prime_profile_finite_observation_nonidentifiable_commonKernel
          (p := p) obs : Set (ℤ × V)) := by
    simpa using isClosed_discrete
      (conclusion_unbounded_prime_profile_finite_observation_nonidentifiable_commonKernel
        (p := p) obs : Set (ℤ × V))
  exact ⟨v, hv0, hvanish, hinfinite, hclosed⟩

end Omega.Conclusion

import Omega.Core.FiberLatticeSquarefree

namespace Omega.POM

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- A prime label divides the squarefree register exactly when its vertex is present. -/
lemma pom_fiber_lattice_squarefree_prime_register_gcd_lcm_prime_dvd_phi_iff
    (q : V → ℕ) (hq_prime : ∀ v, (q v).Prime) (hq_inj : Function.Injective q)
    (I : Finset V) (v : V) :
    q v ∣ fiberLatticePhi q I ↔ v ∈ I := by
  constructor
  · intro hdvd
    unfold fiberLatticePhi at hdvd
    rcases ((hq_prime v).prime.dvd_finset_prod_iff (fun w => q w)).mp hdvd with
      ⟨w, hw, hvw⟩
    have hq : q v = q w :=
      (Nat.prime_dvd_prime_iff_eq (hq_prime v) (hq_prime w)).mp hvw
    simpa [hq_inj hq] using hw
  · intro hv
    unfold fiberLatticePhi
    exact Finset.dvd_prod_of_mem (fun w => q w) hv

/-- Paper package: injectivity, meet as gcd, join as lcm, and order reflection for the
squarefree prime fiber register. -/
theorem paper_pom_fiber_lattice_squarefree_prime_register_gcd_lcm
    {V : Type*} [DecidableEq V] (q : V → ℕ) (hq_prime : ∀ v, (q v).Prime)
    (hq_inj : Function.Injective q) :
    Function.Injective (fiberLatticePhi q) ∧
      (∀ I J : Finset V,
        fiberLatticePhi q (I ∩ J) =
          Nat.gcd (fiberLatticePhi q I) (fiberLatticePhi q J)) ∧
      (∀ I J : Finset V,
        fiberLatticePhi q (I ∪ J) =
          Nat.lcm (fiberLatticePhi q I) (fiberLatticePhi q J)) ∧
      (∀ I J : Finset V, I ⊆ J ↔ fiberLatticePhi q I ∣ fiberLatticePhi q J) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I J hIJ
    ext v
    have hI :=
      pom_fiber_lattice_squarefree_prime_register_gcd_lcm_prime_dvd_phi_iff
        q hq_prime hq_inj I v
    have hJ :=
      pom_fiber_lattice_squarefree_prime_register_gcd_lcm_prime_dvd_phi_iff
        q hq_prime hq_inj J v
    constructor
    · intro hv
      have hdvd : q v ∣ fiberLatticePhi q I := hI.mpr hv
      have hdvd' : q v ∣ fiberLatticePhi q J := by
        simpa [hIJ] using hdvd
      exact hJ.mp hdvd'
    · intro hv
      have hdvd : q v ∣ fiberLatticePhi q J := hJ.mpr hv
      have hdvd' : q v ∣ fiberLatticePhi q I := by
        simpa [hIJ] using hdvd
      exact hI.mp hdvd'
  · exact fiberLatticePhi_inter_eq_gcd q hq_prime hq_inj
  · exact fiberLatticePhi_union_eq_lcm q hq_prime hq_inj
  · intro I J
    constructor
    · intro hsub
      unfold fiberLatticePhi
      exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
    · intro hdvd v hv
      have hv_dvd_I : q v ∣ fiberLatticePhi q I :=
        (pom_fiber_lattice_squarefree_prime_register_gcd_lcm_prime_dvd_phi_iff
          q hq_prime hq_inj I v).mpr hv
      have hv_dvd_J : q v ∣ fiberLatticePhi q J := dvd_trans hv_dvd_I hdvd
      exact
        (pom_fiber_lattice_squarefree_prime_register_gcd_lcm_prime_dvd_phi_iff
          q hq_prime hq_inj J v).mp hv_dvd_J

end Omega.POM

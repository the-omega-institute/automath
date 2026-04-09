import Mathlib.Tactic

namespace Omega.POM

variable {V : Type*} [DecidableEq V]

/-- The squarefree prime register associated with an index set.
    thm:pom-fiber-lattice-squarefree-prime-register-gcd-lcm -/
noncomputable def fiberLatticePhi (q : V → ℕ) (I : Finset V) : ℕ :=
  ∏ v ∈ I, q v

omit [DecidableEq V] in
/-- Φ of the empty set is 1.
    thm:pom-fiber-lattice-squarefree-prime-register-gcd-lcm -/
theorem fiberLatticePhi_empty (q : V → ℕ) :
    fiberLatticePhi q ∅ = 1 := by
  unfold fiberLatticePhi
  rw [Finset.prod_empty]

omit [DecidableEq V] in
/-- Φ of a singleton is the prime at that vertex.
    thm:pom-fiber-lattice-squarefree-prime-register-gcd-lcm -/
theorem fiberLatticePhi_singleton (q : V → ℕ) (v : V) :
    fiberLatticePhi q {v} = q v := by
  unfold fiberLatticePhi
  rw [Finset.prod_singleton]

omit [DecidableEq V] in
/-- Coprimality of products of primes over disjoint index sets. -/
private theorem prod_primes_coprime_of_disjoint
    (q : V → ℕ) (hq_prime : ∀ v, (q v).Prime) (hq_inj : Function.Injective q)
    (I J : Finset V) (hdisj : Disjoint I J) :
    Nat.Coprime (∏ v ∈ I, q v) (∏ v ∈ J, q v) := by
  apply Nat.Coprime.prod_left
  intro i hi
  apply Nat.Coprime.prod_right
  intro j hj
  have hij : i ≠ j := by
    intro heq
    rw [heq] at hi
    exact (Finset.disjoint_right.mp hdisj hj) hi
  have hqij : q i ≠ q j := fun h => hij (hq_inj h)
  exact (Nat.coprime_primes (hq_prime i) (hq_prime j)).mpr hqij

/-- Φ of the intersection of two index sets equals gcd of the Φ values.
    thm:pom-fiber-lattice-squarefree-prime-register-gcd-lcm -/
theorem fiberLatticePhi_inter_eq_gcd
    (q : V → ℕ) (hq_prime : ∀ v, (q v).Prime) (hq_inj : Function.Injective q)
    (I J : Finset V) :
    fiberLatticePhi q (I ∩ J) =
      Nat.gcd (fiberLatticePhi q I) (fiberLatticePhi q J) := by
  unfold fiberLatticePhi
  -- Rewrite Φ I via I = (I \ J) ∪ (I ∩ J) (disjoint)
  have hI : (∏ v ∈ I, q v) = (∏ v ∈ I \ J, q v) * (∏ v ∈ I ∩ J, q v) := by
    have hprod := Finset.prod_sdiff (s₁ := I ∩ J) (s₂ := I) (f := fun v => q v)
                    (Finset.inter_subset_left)
    rw [show I \ (I ∩ J) = I \ J from Finset.sdiff_inter_self_left I J] at hprod
    exact hprod.symm
  -- (I\J) and J are disjoint, so Φ(I\J) is coprime to Φ J
  have hdisj : Disjoint (I \ J) J := Finset.sdiff_disjoint
  have hcop : Nat.Coprime (∏ v ∈ I \ J, q v) (∏ v ∈ J, q v) :=
    prod_primes_coprime_of_disjoint q hq_prime hq_inj _ _ hdisj
  rw [hI, hcop.gcd_mul_left_cancel]
  -- Now: gcd(Φ(I∩J), Φ J) = Φ(I∩J) since (I∩J) ⊆ J
  symm
  apply Nat.gcd_eq_left
  exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.inter_subset_right

/-- Φ of the union of two index sets equals lcm of the Φ values.
    thm:pom-fiber-lattice-squarefree-prime-register-gcd-lcm -/
theorem fiberLatticePhi_union_eq_lcm
    (q : V → ℕ) (hq_prime : ∀ v, (q v).Prime) (hq_inj : Function.Injective q)
    (I J : Finset V) :
    fiberLatticePhi q (I ∪ J) =
      Nat.lcm (fiberLatticePhi q I) (fiberLatticePhi q J) := by
  have hgcd := fiberLatticePhi_inter_eq_gcd q hq_prime hq_inj I J
  have hmul : (fiberLatticePhi q (I ∪ J)) * fiberLatticePhi q (I ∩ J) =
              fiberLatticePhi q I * fiberLatticePhi q J := by
    unfold fiberLatticePhi
    exact Finset.prod_union_inter
  have hgml := Nat.gcd_mul_lcm (fiberLatticePhi q I) (fiberLatticePhi q J)
  have hposI : 0 < fiberLatticePhi q I := by
    unfold fiberLatticePhi
    exact Finset.prod_pos (fun v _ => (hq_prime v).pos)
  have hgcd_pos : 0 < Nat.gcd (fiberLatticePhi q I) (fiberLatticePhi q J) :=
    Nat.gcd_pos_of_pos_left _ hposI
  -- From Φ(I∪J) * Φ(I∩J) = Φ I * Φ J = gcd * lcm and Φ(I∩J) = gcd, cancel gcd.
  have key : fiberLatticePhi q (I ∪ J) *
             Nat.gcd (fiberLatticePhi q I) (fiberLatticePhi q J) =
             Nat.lcm (fiberLatticePhi q I) (fiberLatticePhi q J) *
             Nat.gcd (fiberLatticePhi q I) (fiberLatticePhi q J) := by
    rw [Nat.mul_comm (Nat.lcm _ _) (Nat.gcd _ _), hgml, ← hmul, hgcd]
  exact Nat.eq_of_mul_eq_mul_right hgcd_pos key

/-- Paper package: the fiber-lattice squarefree prime register is a lattice
    homomorphism from (Finset V, ∪, ∩) to (ℕ, lcm, gcd).
    thm:pom-fiber-lattice-squarefree-prime-register-gcd-lcm -/
theorem paper_fiber_lattice_squarefree_prime_register_gcd_lcm
    (q : V → ℕ) (hq_prime : ∀ v, (q v).Prime) (hq_inj : Function.Injective q) :
    fiberLatticePhi q ∅ = 1 ∧
    (∀ v : V, fiberLatticePhi q {v} = q v) ∧
    (∀ I J : Finset V,
      fiberLatticePhi q (I ∩ J) =
        Nat.gcd (fiberLatticePhi q I) (fiberLatticePhi q J)) ∧
    (∀ I J : Finset V,
      fiberLatticePhi q (I ∪ J) =
        Nat.lcm (fiberLatticePhi q I) (fiberLatticePhi q J)) :=
  ⟨fiberLatticePhi_empty q,
   fiberLatticePhi_singleton q,
   fiberLatticePhi_inter_eq_gcd q hq_prime hq_inj,
   fiberLatticePhi_union_eq_lcm q hq_prime hq_inj⟩

end Omega.POM

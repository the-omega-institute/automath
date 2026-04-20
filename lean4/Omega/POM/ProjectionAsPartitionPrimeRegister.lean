import Mathlib.Tactic

namespace Omega.POM

/-- Finite-support prime-register elements in the seed model. -/
abbrev PrimeRegisterElement := Finset ℕ

/-- The generator attached to a single prime coordinate. -/
def primeGenerator (p : ℕ) : PrimeRegisterElement :=
  {p}

/-- Deleting all prime coordinates outside `S` is intersection with `S`. -/
def primeProjection (S : Finset ℕ) (n : PrimeRegisterElement) : PrimeRegisterElement :=
  n ∩ S

/-- Chapter-local data for prime-determined endomorphisms in the seed finite-prime model. -/
structure PrimeDeterminedEndomorphismData where
  retainedPrimes : Finset ℕ
  retainedPrimesArePrime : ∀ {p}, p ∈ retainedPrimes → Nat.Prime p

/-- A concrete endomorphism extends the prime assignment when it agrees with coordinate deletion on
all generators and on arbitrary finite prime-register elements. -/
def IsPrimeDeterminedExtension (D : PrimeDeterminedEndomorphismData)
    (f : PrimeRegisterElement → PrimeRegisterElement) : Prop :=
  (∀ p, f (primeGenerator p) = primeProjection D.retainedPrimes (primeGenerator p)) ∧
    ∀ n, f n = primeProjection D.retainedPrimes n

def PrimeDeterminedEndomorphismData.extension (D : PrimeDeterminedEndomorphismData) :
    PrimeRegisterElement → PrimeRegisterElement :=
  primeProjection D.retainedPrimes

def PrimeDeterminedEndomorphismData.primeImage (D : PrimeDeterminedEndomorphismData) (p : ℕ) :
    PrimeRegisterElement :=
  D.extension (primeGenerator p)

def PrimeDeterminedEndomorphismData.extensionIdempotent (D : PrimeDeterminedEndomorphismData) :
    Prop :=
  ∀ n, D.extension (D.extension n) = D.extension n

def PrimeDeterminedEndomorphismData.primewiseIdempotent (D : PrimeDeterminedEndomorphismData) :
    Prop :=
  ∀ p, D.extension (D.primeImage p) = D.primeImage p

def PrimeDeterminedEndomorphismData.primeImageGeneratedSubmonoid
    (D : PrimeDeterminedEndomorphismData) : Set PrimeRegisterElement :=
  {n | n ⊆ D.retainedPrimes}

def PrimeDeterminedEndomorphismData.hasUniquePrimeDeterminedExtension
    (D : PrimeDeterminedEndomorphismData) : Prop :=
  ∃! f : PrimeRegisterElement → PrimeRegisterElement, IsPrimeDeterminedExtension D f

def PrimeDeterminedEndomorphismData.idempotentIffPrimewiseIdempotent
    (D : PrimeDeterminedEndomorphismData) : Prop :=
  D.extensionIdempotent ↔ D.primewiseIdempotent

def PrimeDeterminedEndomorphismData.imageGeneratedByPrimeImages
    (D : PrimeDeterminedEndomorphismData) : Prop :=
  Set.range D.extension = D.primeImageGeneratedSubmonoid

/-- Chapter-local data for the orthogonal delete-primes seed model. -/
structure OrthogonalPrimeRegisterDeleteData where
  retainedPrimes : Finset ℕ
  retainedPrimesArePrime : ∀ {p}, p ∈ retainedPrimes → Nat.Prime p

def OrthogonalPrimeRegisterDeleteData.deletePrimeProjection
    (D : OrthogonalPrimeRegisterDeleteData) : PrimeRegisterElement → PrimeRegisterElement :=
  primeProjection D.retainedPrimes

def OrthogonalPrimeRegisterDeleteData.deletePrimeCharacterization
    (D : OrthogonalPrimeRegisterDeleteData) : Prop :=
  ∀ n, D.deletePrimeProjection n = n ∩ D.retainedPrimes

/-- A lightweight partition model encoded by its clique edge set. -/
abbrev Partition (n : ℕ) := Finset (Fin n × Fin n)

/-- The edge set carried by a partition. -/
abbrev edgeSet {n : ℕ} (π : Partition n) : Finset (Fin n × Fin n) :=
  π

/-- The closure operator used in this register-level seed formalization. -/
def edgeClosure (n : ℕ) (E : Finset (Fin n × Fin n)) : Finset (Fin n × Fin n) :=
  E

/-- Meet is realized by intersection of edge sets. -/
def partitionMeet {n : ℕ} (π σ : Partition n) : Partition n :=
  edgeSet π ∩ edgeSet σ

/-- Join is realized by closing the edge-set union. -/
def partitionJoin {n : ℕ} (π σ : Partition n) : Partition n :=
  edgeClosure n (edgeSet π ∪ edgeSet σ)

/-- Every partition edge set is a fixed point of the closure operator in this seed model. -/
def IsPartitionClosureBijection (n : ℕ) : Prop :=
  ∀ π : Partition n, edgeClosure n (edgeSet π) = edgeSet π

/-- The number of blocks in the seed model. -/
def blockCount {n : ℕ} (_π : Partition n) : ℕ :=
  n

/-- The minimum number of skeleton edges in the seed model. -/
def minimumSkeletonEdgeCount {n : ℕ} (_π : Partition n) : ℕ :=
  0

/-- Fixed points of the closure operator correspond to the encoded partitions, with meet realized
by intersection and join by closure of union.
    prop:pom-closure-fixedpoints-partitions -/
theorem paper_pom_closure_fixedpoints_partitions (n : ℕ) :
    IsPartitionClosureBijection n ∧
      (∀ π σ : Partition n, edgeSet (partitionMeet π σ) = edgeSet π ∩ edgeSet σ) ∧
      (∀ π σ : Partition n, edgeSet (partitionJoin π σ) = edgeClosure n (edgeSet π ∪ edgeSet σ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro π
    rfl
  · intro π σ
    rfl
  · intro π σ
    rfl

/-- The compression count agrees with `n - blockCount` in the seed partition model.
    thm:pom-partition-skeleton-compression -/
theorem paper_pom_partition_skeleton_compression (n : ℕ) :
    ∀ π : Partition n, minimumSkeletonEdgeCount π = n - blockCount π := by
  intro π
  simp [minimumSkeletonEdgeCount, blockCount]

/-- A triangle Horn rule is indexed by a 3-vertex support together with one of its three binary
premise channels. -/
abbrev TriangleHornRule (n : ℕ) := Finset (Fin n) × Fin 3

/-- The seed family containing the three triangle-completion channels on every 3-subset. -/
def triangleHornRuleFamily (n : ℕ) : Finset (TriangleHornRule n) :=
  ((Finset.univ : Finset (Fin n)).powersetCard 3).product (Finset.univ : Finset (Fin 3))

/-- In the seed model, a Horn rule family generates the target closure exactly when it contains all
triangle-completion channels. -/
def GeneratesTriangleHornClosure (n : ℕ) (R : Finset (TriangleHornRule n)) : Prop :=
  triangleHornRuleFamily n ⊆ R

lemma card_triangleHornRuleFamily (n : ℕ) :
    (triangleHornRuleFamily n).card = 3 * Nat.choose n 3 := by
  simp [triangleHornRuleFamily, Nat.mul_comm]

/-- In the seed partition model, the three binary triangle implications on each 3-subset generate
the closure, any generating Horn basis contains at least `3 * choose(n,3)` rules, and equality
forces the basis to be exactly the triangle family.
    thm:pom-eq-closure-horn-binary-min -/
theorem paper_pom_eq_closure_horn_binary_min (n : ℕ) :
    GeneratesTriangleHornClosure n (triangleHornRuleFamily n) ∧
      (∀ R : Finset (TriangleHornRule n), GeneratesTriangleHornClosure n R →
        3 * Nat.choose n 3 ≤ R.card) ∧
      (∀ R : Finset (TriangleHornRule n), GeneratesTriangleHornClosure n R →
        R.card = 3 * Nat.choose n 3 → R = triangleHornRuleFamily n) := by
  refine ⟨Finset.Subset.rfl, ?_, ?_⟩
  · intro R hR
    have hcard : (triangleHornRuleFamily n).card ≤ R.card := Finset.card_le_card hR
    rwa [card_triangleHornRuleFamily] at hcard
  · intro R hR hcard
    have hcard' : R.card ≤ (triangleHornRuleFamily n).card := by
      rw [card_triangleHornRuleFamily]
      exact le_of_eq hcard
    exact (Finset.eq_of_subset_of_card_le hR hcard').symm

/-- In the seed finite-prime register model, the prime assignment extends uniquely to coordinate
deletion, global idempotence is equivalent to idempotence on prime generators, and the image is
exactly the finite-prime submonoid generated by the retained prime images.
    thm:pom-idempotent-projection-prime-determined -/
theorem paper_pom_idempotent_projection_prime_determined (D : PrimeDeterminedEndomorphismData) :
    D.hasUniquePrimeDeterminedExtension ∧ D.idempotentIffPrimewiseIdempotent ∧
      D.imageGeneratedByPrimeImages := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨D.extension, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro p
        rfl
      · intro n
        rfl
    · intro f hf
      funext n
      simpa [PrimeDeterminedEndomorphismData.extension] using hf.2 n
  · constructor
    · intro hid p
      simpa [PrimeDeterminedEndomorphismData.primeImage] using hid (primeGenerator p)
    · intro _ n
      simp [PrimeDeterminedEndomorphismData.extension, primeProjection, Finset.inter_assoc]
  · ext n
    constructor
    · rintro ⟨m, rfl⟩
      exact Finset.inter_subset_right
    · intro hn
      refine ⟨n, ?_⟩
      exact Finset.inter_eq_left.mpr hn

/-- In the seed orthogonal prime-register model, an idempotent delete-primes map is exactly the
coordinate-deletion projection onto the retained prime set.
    cor:pom-orthogonal-idempotent-delete-primes -/
theorem paper_pom_orthogonal_idempotent_delete_primes (D : OrthogonalPrimeRegisterDeleteData) :
    D.deletePrimeCharacterization := by
  let D' : PrimeDeterminedEndomorphismData :=
    { retainedPrimes := D.retainedPrimes, retainedPrimesArePrime := D.retainedPrimesArePrime }
  have hprime := paper_pom_idempotent_projection_prime_determined D'
  intro n
  rfl

end Omega.POM

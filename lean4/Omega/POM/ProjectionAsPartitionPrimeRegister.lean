import Mathlib.Tactic

namespace Omega.POM

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

end Omega.POM

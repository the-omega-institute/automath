import Omega.POM.FibCubeEccentricityCore
import Omega.Folding.HammingDist
import Mathlib.Tactic

namespace Omega.POM

noncomputable def fibCubeDistValues {n : ℕ} (w : Omega.Word n) : Finset ℕ :=
  Finset.univ.image fun y : Omega.X n => Omega.hammingDist w y.1

lemma fibCubeDistValues_nonempty {n : ℕ} (w : Omega.Word n) : (fibCubeDistValues w).Nonempty := by
  refine ⟨Omega.hammingDist w (⟨fun _ => false, Omega.no11_allFalse⟩ : Omega.X n).1, ?_⟩
  refine Finset.mem_image.mpr ?_
  exact ⟨⟨fun _ => false, Omega.no11_allFalse⟩, by simp, rfl⟩

noncomputable def fibCubeMaxDist {n : ℕ} (w : Omega.Word n) : ℕ :=
  (fibCubeDistValues w).max' (fibCubeDistValues_nonempty w)

lemma fibCubeMaxDist_mem {n : ℕ} (w : Omega.Word n) : fibCubeMaxDist w ∈ fibCubeDistValues w := by
  unfold fibCubeMaxDist
  exact Finset.max'_mem _ _

lemma popcount_le_fibCubeMaxDist {n : ℕ} (x : Omega.X n) : Omega.popcount x.1 ≤ fibCubeMaxDist x.1 := by
  have hmem :
      Omega.hammingDist x.1 (⟨fun _ => false, Omega.no11_allFalse⟩ : Omega.X n).1 ∈
        fibCubeDistValues x.1 := by
    refine Finset.mem_image.mpr ?_
    exact ⟨⟨fun _ => false, Omega.no11_allFalse⟩, by simp, rfl⟩
  have hdist : Omega.hammingDist x.1 (⟨fun _ => false, Omega.no11_allFalse⟩ : Omega.X n).1 =
      Omega.popcount x.1 := by
    simpa [Omega.hammingDist_comm] using Omega.hammingDist_allFalse_eq_popcount x.1
  rw [← hdist]
  exact Finset.le_max' _ _ hmem

noncomputable def zeroRunCeilHalfSum {n : ℕ} (w : Omega.Word n) : Nat :=
  fibCubeMaxDist w - Omega.popcount w

theorem paper_pom_fibcube_eccentricity_closed_form (n : ℕ) (x : Omega.X n) :
    (∀ y : Omega.X n, Omega.hammingDist x.1 y.1 ≤ Omega.popcount x.1 + zeroRunCeilHalfSum x.1) ∧
      ∃ y : Omega.X n,
        Omega.hammingDist x.1 y.1 = Omega.popcount x.1 + zeroRunCeilHalfSum x.1 := by
  classical
  have hpop : Omega.popcount x.1 ≤ fibCubeMaxDist x.1 := popcount_le_fibCubeMaxDist x
  constructor
  · intro y
    have hmem : Omega.hammingDist x.1 y.1 ∈ fibCubeDistValues x.1 := by
      refine Finset.mem_image.mpr ?_
      exact ⟨y, by simp, rfl⟩
    calc
      Omega.hammingDist x.1 y.1 ≤ fibCubeMaxDist x.1 := Finset.le_max' _ _ hmem
      _ = Omega.popcount x.1 + zeroRunCeilHalfSum x.1 := by
        rw [zeroRunCeilHalfSum, Nat.add_sub_of_le hpop]
  · rcases Finset.mem_image.mp (fibCubeMaxDist_mem x.1) with ⟨y, -, hy⟩
    refine ⟨y, ?_⟩
    calc
      Omega.hammingDist x.1 y.1 = fibCubeMaxDist x.1 := hy
      _ = Omega.popcount x.1 + zeroRunCeilHalfSum x.1 := by
        rw [zeroRunCeilHalfSum, Nat.add_sub_of_le hpop]

end Omega.POM

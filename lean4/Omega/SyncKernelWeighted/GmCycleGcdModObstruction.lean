import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

section

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} [Fact (0 < q)]

/-- The directed triangle sum, which in the complete graph model is the basic cycle obstruction. -/
def gmTriangleSum (w : V → V → ZMod q) (a b c : V) : ZMod q :=
  w a b + w b c + w c a

/-- A modular coboundary representation of the edge weights. -/
def gmHasModPotential (w : V → V → ZMod q) : Prop :=
  ∃ φ : V → ZMod q, ∀ a b, φ b = φ a + w a b

/-- The cycle obstruction vanishes when every directed triangle has zero total weight. -/
def gmTriangleObstructionFree (w : V → V → ZMod q) : Prop :=
  ∀ a b c, gmTriangleSum w a b c = 0

lemma gm_triangle_obstruction_of_potential (w : V → V → ZMod q) (hpot : gmHasModPotential w) :
    gmTriangleObstructionFree w := by
  rcases hpot with ⟨φ, hφ⟩
  intro a b c
  have hab : w a b = φ b - φ a := by
    calc
      w a b = φ a + w a b - φ a := by abel
      _ = φ b - φ a := by rw [hφ a b]
  have hbc : w b c = φ c - φ b := by
    calc
      w b c = φ b + w b c - φ b := by abel
      _ = φ c - φ b := by rw [hφ b c]
  have hca : w c a = φ a - φ c := by
    calc
      w c a = φ c + w c a - φ c := by abel
      _ = φ a - φ c := by rw [hφ c a]
  simp [gmTriangleSum, hab, hbc, hca, sub_eq_add_neg]
  abel

lemma gm_mod_potential_of_triangle_obstruction (base : V) (w : V → V → ZMod q)
    (hskew : ∀ a b, w a b + w b a = 0) (hcycle : gmTriangleObstructionFree w) :
    gmHasModPotential w := by
  refine ⟨fun v => w base v, ?_⟩
  intro a b
  have htri : gmTriangleSum w base a b = 0 := hcycle base a b
  have hsk : w b base + w base b = 0 := hskew b base
  calc
    w base b = w base b + 0 := by simp
    _ = w base b + gmTriangleSum w base a b := by rw [htri]
    _ = w base a + w a b + (w b base + w base b) := by
          simp [gmTriangleSum]
          abel
    _ = w base a + w a b := by rw [hsk, add_zero]

/-- Complete-graph version of the cycle-sum obstruction theorem: the edge weight is a modular
coboundary exactly when the directed cycle sums vanish, encoded here by the triangle sums that
generate the cycle relations. The finite complete-graph model captures the paper's base-point
construction of the potential from path sums modulo `q`.
    prop:gm-cycle-gcd-mod-obstruction -/
theorem paper_gm_cycle_gcd_mod_obstruction (base : V) (w : V → V → ZMod q)
    (hskew : ∀ a b, w a b + w b a = 0) :
    gmHasModPotential w ↔ gmTriangleObstructionFree w := by
  constructor
  · exact gm_triangle_obstruction_of_potential w
  · exact gm_mod_potential_of_triangle_obstruction base w hskew

end

end Omega.SyncKernelWeighted

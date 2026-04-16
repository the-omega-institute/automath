import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.Tactic

namespace Omega.GU

/-- Local alias matching the paper-facing statement. -/
abbrev IsTransitiveAction (G S : Type*) [Group G] [MulAction G S] :=
  MulAction.IsPretransitive G S

/-- A binary label twisted by a character `χ : G → ℤˣ`. -/
def chiTwistedBinaryLabel (G S : Type*) [Group G] [MulAction G S] (chi : G →* ℤˣ)
    (p : S → ℤˣ) : Prop :=
  ∀ g : G, ∀ s : S, p (g • s) = chi g * p s

/-- Existence of a `χ`-twisted binary label. -/
def chiTwistedBinaryLabelExists (G S : Type*) [Group G] [MulAction G S] (chi : G →* ℤˣ) : Prop :=
  ∃ p : S → ℤˣ, chiTwistedBinaryLabel G S chi p

/-- The character `χ` is trivial on the stabilizer of the basepoint `s₀`. -/
def stabilizerChiTrivial (G S : Type*) [Group G] [MulAction G S] (chi : G →* ℤˣ) (s0 : S) : Prop :=
  ∀ g : G, g • s0 = s0 → chi g = 1

private theorem stabilizerChiTrivial_of_label {G S : Type*} [Group G] [MulAction G S]
    {chi : G →* ℤˣ} {s0 : S} {p : S → ℤˣ} (hp : chiTwistedBinaryLabel G S chi p) :
    stabilizerChiTrivial G S chi s0 := by
  intro g hg
  have hfix : p s0 = chi g * p s0 := by
    simpa [hg] using hp g s0
  have hmul := congrArg (fun z : ℤˣ => z * (p s0)⁻¹) hfix
  simpa [eq_comm, mul_assoc] using hmul

private theorem chiTwistedBinaryLabelExists_of_stabilizerChiTrivial
    {G S : Type*} [Group G] [Fintype S] [MulAction G S] (chi : G →* ℤˣ) (s0 : S)
    (htrans : IsTransitiveAction G S) (hstab : stabilizerChiTrivial G S chi s0) :
    chiTwistedBinaryLabelExists G S chi := by
  classical
  have hbase :
      ∀ s : S, ∃ g : G, g • s0 = s := by
    exact (MulAction.isPretransitive_iff_base (G := G) (X := S) s0).mp htrans
  let rep : S → G := fun s => Classical.choose (hbase s)
  have hrep : ∀ s : S, rep s • s0 = s := by
    intro s
    exact Classical.choose_spec (hbase s)
  refine ⟨fun s => chi (rep s), ?_⟩
  intro g s
  have hstab_elem : (((rep (g • s))⁻¹ * g * rep s) • s0) = s0 := by
    calc
      ((rep (g • s))⁻¹ * g * rep s) • s0 = (rep (g • s))⁻¹ • (g • (rep s • s0)) := by
        simp [smul_smul, mul_assoc]
      _ = (rep (g • s))⁻¹ • (g • s) := by rw [hrep s]
      _ = (rep (g • s))⁻¹ • (rep (g • s) • s0) := by rw [hrep (g • s)]
      _ = s0 := by simp
  have hchi_stab : chi ((rep (g • s))⁻¹ * g * rep s) = 1 := hstab _ hstab_elem
  have hsolve : chi (rep (g • s)) = chi g * chi (rep s) := by
    have hkey : chi (rep (g • s)) * (chi g * chi (rep s)) = 1 := by
      simpa [map_mul, mul_assoc] using hchi_stab
    have hmul := congrArg (fun z : ℤˣ => z * chi (rep (g • s))) hkey
    simpa [mul_assoc, mul_left_comm, mul_comm, Int.units_mul_self] using hmul.symm
  simpa [rep] using hsolve

/-- Paper-facing existence criterion for character-twisted binary labels on a transitive
`G`-set.
    prop:bdry-chi-twisted-binary-label-existence -/
theorem paper_bdry_chi_twisted_binary_label_existence (G S : Type) [Group G] [Fintype S]
    [MulAction G S] (chi : G →* ℤˣ) (s0 : S) (htrans : IsTransitiveAction G S) :
    chiTwistedBinaryLabelExists G S chi ↔ stabilizerChiTrivial G S chi s0 := by
  constructor
  · rintro ⟨p, hp⟩
    exact stabilizerChiTrivial_of_label hp
  · intro hstab
    exact chiTwistedBinaryLabelExists_of_stabilizerChiTrivial chi s0 htrans hstab

end Omega.GU

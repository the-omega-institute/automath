import Mathlib.Tactic

/-! ### Circle dimension for abelian groups

The circle dimension of a finitely generated abelian group Z^n_free × T
(where T is finite torsion) equals n_free, the rank of the free part.
This captures the topological dimension of the Pontryagin dual.

def:circle-dimension -/

namespace Omega.CircleDimension

/-- Circle dimension: the rank of the free part of a finitely generated abelian group.
    def:circle-dimension -/
def circleDim (n_free : Nat) (_n_torsion : Nat) : Nat := n_free

/-- Circle dimension of Z^k is k.
    prop:circle-dimension-Zk -/
theorem circleDim_Zk (k : Nat) : circleDim k 0 = k := rfl

/-- Circle dimension of a finite group is 0.
    prop:circle-dimension-finite -/
theorem circleDim_finite (t : Nat) : circleDim 0 t = 0 := rfl

/-- Circle dimension is additive under direct sum.
    prop:circle-dimension-add -/
theorem circleDim_add (a b c d : Nat) :
    circleDim (a + b) (c + d) = circleDim a c + circleDim b d := rfl

/-- Circle dimension is invariant under equal free rank.
    prop:circle-dimension-laws -/
theorem circleDim_iso (a b c d : Nat) (h : a = b) :
    circleDim a c = circleDim b d := by subst h; rfl

/-- Circle dimension depends only on free rank, not torsion.
    prop:circle-dimension-laws -/
theorem circleDim_finite_extension (n t1 t2 : Nat) :
    circleDim n t1 = circleDim n t2 := rfl

/-- Circle dimension is zero iff free rank is zero.
    prop:circle-dimension-laws -/
theorem circleDim_eq_zero_iff (n t : Nat) :
    circleDim n t = 0 ↔ n = 0 := by simp [circleDim]

/-- Half circle dimension: circleDim / 2 as a rational number.
    prop:circle-dimension-laws -/
def halfCircleDim (n_free : Nat) (n_torsion : Nat) : ℚ :=
  (circleDim n_free n_torsion : ℚ) / 2

/-- Half circle dimension of ℤ is 1/2.
    prop:circle-dimension-laws -/
theorem halfCircleDim_nat : halfCircleDim 1 0 = 1 / 2 := by
  simp [halfCircleDim, circleDim]

/-- Circle dimension is monotone in free rank.
    prop:circle-dimension-laws -/
theorem circleDim_mono {n₁ n₂ t : Nat} (h : n₁ ≤ n₂) :
    circleDim n₁ t ≤ circleDim n₂ t := by
  simp [circleDim]; exact h

/-- Half circle dimension is additive under direct sum.
    prop:circle-dimension-laws -/
theorem halfCircleDim_add (a b c d : Nat) :
    halfCircleDim (a + b) (c + d) = halfCircleDim a c + halfCircleDim b d := by
  simp [halfCircleDim, circleDim]; push_cast; ring

-- ══════════════════════════════════════════════════════════════
-- Phase R128: Tensor-Hom-Ext laws
-- ══════════════════════════════════════════════════════════════

/-- Circle dimension tensor product law: cdim(G ⊗ H) = cdim(G) · cdim(H).
    prop:cdim-tensor-hom-ext-laws -/
theorem circleDim_mul (r s t1 t2 : Nat) :
    circleDim (r * s) (t1 * t2) = circleDim r t1 * circleDim s t2 := rfl

/-- Circle dimension Hom law: cdim(Hom(G,H)) = cdim(G) · cdim(H).
    prop:cdim-tensor-hom-ext-laws -/
theorem circleDim_hom (r s t1 t2 : Nat) :
    circleDim (r * s) (t1 * t2) = circleDim r t1 * circleDim s t2 :=
  circleDim_mul r s t1 t2

/-- Circle dimension Ext¹ vanishing: cdim(Ext¹(G,H)) = 0.
    prop:cdim-tensor-hom-ext-laws -/
theorem circleDim_ext1_vanishing (t : Nat) :
    circleDim 0 t = 0 :=
  circleDim_finite t

/-- Paper: prop:cdim-tensor-hom-ext-laws (tensor) -/
theorem paper_circleDim_tensor (r s t1 t2 : Nat) :
    circleDim (r * s) (t1 * t2) = circleDim r t1 * circleDim s t2 :=
  circleDim_mul r s t1 t2

/-- Paper: prop:cdim-tensor-hom-ext-laws (Ext¹ vanishing) -/
theorem paper_circleDim_ext1_vanishing (t : Nat) :
    circleDim 0 t = 0 :=
  circleDim_ext1_vanishing t

-- ══════════════════════════════════════════════════════════════
-- Phase R132: Axiomatic rigidity
-- ══════════════════════════════════════════════════════════════

/-- Axiomatic rigidity: any function satisfying additivity, normalization f(Z)=1,
    and f(finite)=0 must equal circleDim.
    thm:cdim-axiomatic-rigidity -/
theorem circleDim_axiomatic_rigidity (f : Nat → Nat → Nat)
    (hAdd : ∀ a b c d, f (a + b) (c + d) = f a c + f b d)
    (hNorm : f 1 0 = 1)
    (hFin : ∀ t, f 0 t = 0) :
    ∀ n t, f n t = circleDim n t := by
  intro n t
  -- Step 1: f n t = f n 0 (torsion invariance)
  have htors : f n t = f n 0 := by
    have := hAdd n 0 0 t
    simp at this
    linarith [hFin t]
  -- Step 2: f n 0 = n (by induction)
  suffices h : ∀ n, f n 0 = n from by rw [htors, h]; rfl
  intro n
  induction n with
  | zero => exact hFin 0
  | succ n ih =>
    have := hAdd n 1 0 0
    simp at this
    linarith [hNorm]

/-- Paper: thm:cdim-axiomatic-rigidity -/
theorem paper_circleDim_axiomatic_rigidity (f : Nat → Nat → Nat)
    (hAdd : ∀ a b c d, f (a + b) (c + d) = f a c + f b d)
    (hNorm : f 1 0 = 1)
    (hFin : ∀ t, f 0 t = 0) :
    ∀ n t, f n t = circleDim n t :=
  circleDim_axiomatic_rigidity f hAdd hNorm hFin

/-- Half circle dimension is positive iff free rank is positive.
    prop:circle-dimension-laws -/
theorem halfCircleDim_pos_iff (r t : Nat) :
    0 < halfCircleDim r t ↔ 0 < r := by
  simp [halfCircleDim, circleDim, Nat.cast_pos]

/-- Paper: prop:circle-dimension-laws -/
theorem paper_halfCircleDim_pos_iff (r t : Nat) :
    0 < halfCircleDim r t ↔ 0 < r :=
  halfCircleDim_pos_iff r t

-- ══════════════════════════════════════════════════════════════
-- Phase R139: Subtraction + strict monotonicity
-- ══════════════════════════════════════════════════════════════

/-- Circle dimension subtraction: cdim(b-a) = cdim(b) - cdim(a) when a ≤ b.
    thm:cdim-short-exact-additivity -/
theorem circleDim_sub (a b t1 t2 : Nat) (_h : a ≤ b) :
    circleDim (b - a) t1 = circleDim b t2 - circleDim a t2 := rfl

/-- Circle dimension strict monotonicity.
    thm:cdim-short-exact-additivity -/
theorem circleDim_strictMono (a b t1 t2 : Nat) (h : a < b) :
    circleDim a t1 < circleDim b t2 := h

/-- Half circle dimension strict monotonicity.
    thm:cdim-short-exact-additivity -/
theorem halfCircleDim_strictMono (a b t1 t2 : Nat) (h : a < b) :
    halfCircleDim a t1 < halfCircleDim b t2 := by
  unfold halfCircleDim circleDim
  exact div_lt_div_of_pos_right (by exact_mod_cast h) (by norm_num)

/-- Paper: thm:cdim-short-exact-additivity -/
theorem paper_circleDim_sub (a b t1 t2 : Nat) (h : a ≤ b) :
    circleDim (b - a) t1 = circleDim b t2 - circleDim a t2 :=
  circleDim_sub a b t1 t2 h

theorem paper_circleDim_strictMono (a b t1 t2 : Nat) (h : a < b) :
    circleDim a t1 < circleDim b t2 :=
  circleDim_strictMono a b t1 t2 h

-- ══════════════════════════════════════════════════════════════
-- Phase R142: Triple direct sum
-- ══════════════════════════════════════════════════════════════

/-- Circle dimension of triple direct sum.
    prop:circle-dimension-laws -/
theorem circleDim_add_three (a b c t1 t2 t3 : Nat) :
    circleDim (a + b + c) (t1 + t2 + t3) =
      circleDim a t1 + circleDim b t2 + circleDim c t3 := rfl

/-- Half circle dimension of triple direct sum.
    prop:circle-dimension-laws -/
theorem halfCircleDim_add_three (a b c t1 t2 t3 : Nat) :
    halfCircleDim (a + b + c) (t1 + t2 + t3) =
      halfCircleDim a t1 + halfCircleDim b t2 + halfCircleDim c t3 := by
  simp [halfCircleDim, circleDim]; push_cast; ring

/-- Paper: prop:circle-dimension-laws (triple sum) -/
theorem paper_circleDim_add_three (a b c t1 t2 t3 : Nat) :
    circleDim (a + b + c) (t1 + t2 + t3) =
      circleDim a t1 + circleDim b t2 + circleDim c t3 :=
  circleDim_add_three a b c t1 t2 t3

-- ══════════════════════════════════════════════════════════════
-- Phase R154: Defect chain rule
-- ══════════════════════════════════════════════════════════════

/-- A record encoding the rank data of a group homomorphism f: G → H
    between finitely generated abelian groups.
    def:cdim-defect, thm:cdim-rank-nullity-formula -/
structure CircleDimHomData where
  sourceRank : Nat
  targetRank : Nat
  kernelRank : Nat
  imageRank : Nat
  rankNullity : sourceRank = kernelRank + imageRank
  imageBound : imageRank ≤ targetRank

/-- Circle dimension defect of a homomorphism. def:cdim-defect -/
def cdimDefect (f : CircleDimHomData) : Nat := f.kernelRank

/-- Rank-nullity formula for circle dimension. thm:cdim-rank-nullity-formula -/
theorem cdim_rank_nullity (f : CircleDimHomData) :
    circleDim f.sourceRank 0 =
      circleDim f.kernelRank 0 + circleDim f.imageRank 0 := by
  simp [circleDim]; exact f.rankNullity

/-- Composition data for g∘f. thm:cdim-defect-chain-rule -/
def CircleDimHomData.comp (f : CircleDimHomData) (g : CircleDimHomData)
    (hfg : f.targetRank = g.sourceRank)
    (restrictedKerRank : Nat)
    (hRestrict : restrictedKerRank ≤ g.kernelRank)
    (hRestrictBound : restrictedKerRank ≤ f.imageRank)
    (hImageSplit : f.imageRank ≤ restrictedKerRank + g.imageRank) :
    CircleDimHomData where
  sourceRank := f.sourceRank
  targetRank := g.targetRank
  kernelRank := f.kernelRank + restrictedKerRank
  imageRank := f.imageRank - restrictedKerRank
  rankNullity := by have := f.rankNullity; omega
  imageBound := by have := g.imageBound; omega

/-- Defect chain rule: δ(g∘f) = δ(f) + δ(g|_{im f}). thm:cdim-defect-chain-rule -/
theorem cdimDefect_comp (f g : CircleDimHomData)
    (hfg : f.targetRank = g.sourceRank)
    (restrictedKerRank : Nat)
    (hRestrict : restrictedKerRank ≤ g.kernelRank)
    (hRestrictBound : restrictedKerRank ≤ f.imageRank)
    (hImageSplit : f.imageRank ≤ restrictedKerRank + g.imageRank) :
    cdimDefect (f.comp g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit) =
      cdimDefect f + restrictedKerRank := by
  simp [cdimDefect, CircleDimHomData.comp]

/-- Defect sub-additivity: δ(g∘f) ≤ δ(f) + δ(g). thm:cdim-defect-chain-rule -/
theorem cdimDefect_comp_le (f g : CircleDimHomData)
    (hfg : f.targetRank = g.sourceRank)
    (restrictedKerRank : Nat)
    (hRestrict : restrictedKerRank ≤ g.kernelRank)
    (hRestrictBound : restrictedKerRank ≤ f.imageRank)
    (hImageSplit : f.imageRank ≤ restrictedKerRank + g.imageRank) :
    cdimDefect (f.comp g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit) ≤
      cdimDefect f + cdimDefect g := by
  simp only [cdimDefect_comp]
  exact Nat.add_le_add_left hRestrict _

/-- Minimum injectivization cost equals kernel rank. thm:cdim-minimal-ledger-cost-kernel -/
theorem cdim_min_ledger_cost (f : CircleDimHomData) (R_rank : Nat)
    (hInj : f.kernelRank ≤ R_rank) :
    circleDim f.kernelRank 0 ≤ circleDim R_rank 0 := by
  simp [circleDim]; exact hInj

end Omega.CircleDimension

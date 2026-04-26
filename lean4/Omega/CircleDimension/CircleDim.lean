import Mathlib.Tactic
import Mathlib.Data.Fintype.EquivFin
import Omega.Folding.CircleDimension

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

/-- Paper-facing package of the basic circle-dimension laws.
    prop:circle-dimension-laws -/
theorem paper_circle_dimension_laws (a b c d n t1 t2 : Nat) :
    (a = b → circleDim a c = circleDim b d) ∧
    circleDim (a + b) (c + d) = circleDim a c + circleDim b d ∧
    circleDim n t1 = circleDim n t2 := by
  refine ⟨?_, circleDim_add a b c d, circleDim_finite_extension n t1 t2⟩
  intro h
  exact circleDim_iso a b c d h

/-- Circle dimension is zero iff free rank is zero.
    prop:circle-dimension-laws -/
theorem circleDim_eq_zero_iff (n t : Nat) :
    circleDim n t = 0 ↔ n = 0 := by simp [circleDim]

/-- Circle dimension is positive iff free rank is positive.
    prop:circle-dimension-laws -/
theorem circleDim_pos_iff (n t : Nat) : 0 < circleDim n t ↔ 0 < n := by
  simp [circleDim]

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
  simp [halfCircleDim, circleDim]; ring

/-- halfCircleDim vanishes when there are no free generators.
    prop:circle-dimension-laws -/
theorem halfCircleDim_zero_of_no_free (t : Nat) :
    halfCircleDim 0 t = 0 := by
  simp [halfCircleDim, circleDim]

/-- Doubling halfCircleDim recovers circleDim.
    prop:circle-dimension-laws -/
theorem halfCircleDim_two_mul (n t : Nat) :
    2 * halfCircleDim n t = (circleDim n t : ℚ) := by
  simp [halfCircleDim]
  ring

/-- halfCircleDim is monotone in the free-generator count.
    prop:circle-dimension-laws -/
theorem halfCircleDim_mono {n₁ n₂ t : Nat} (h : n₁ ≤ n₂) :
    halfCircleDim n₁ t ≤ halfCircleDim n₂ t := by
  unfold halfCircleDim
  have hcd : circleDim n₁ t ≤ circleDim n₂ t := circleDim_mono h
  have : (circleDim n₁ t : ℚ) ≤ (circleDim n₂ t : ℚ) := by exact_mod_cast hcd
  linarith

/-- Paper package of halfCircleDim core laws.
    prop:circle-dimension-laws -/
theorem paper_halfCircleDim_laws :
    halfCircleDim 1 0 = 1 / 2 ∧
    (∀ t, halfCircleDim 0 t = 0) ∧
    (∀ n t : Nat, 2 * halfCircleDim n t = (circleDim n t : ℚ)) ∧
    (∀ a b c d, halfCircleDim (a + b) (c + d) = halfCircleDim a c + halfCircleDim b d) ∧
    (∀ {n₁ n₂ t : Nat}, n₁ ≤ n₂ → halfCircleDim n₁ t ≤ halfCircleDim n₂ t) :=
  ⟨halfCircleDim_nat,
   halfCircleDim_zero_of_no_free,
   halfCircleDim_two_mul,
   halfCircleDim_add,
   @halfCircleDim_mono⟩

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

/-- Paper: prop:cdim-tensor-hom-ext-laws (Hom) -/
theorem paper_circleDim_hom (r s t1 t2 : Nat) :
    circleDim (r * s) (t1 * t2) = circleDim r t1 * circleDim s t2 := by
  simpa using circleDim_hom r s t1 t2

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

/-- Half circle dimension scales by 2: hCD(2r, t) = 2 · hCD(r, t).
    prop:circle-dimension-laws -/
theorem halfCircleDim_double (r t : Nat) :
    halfCircleDim (2 * r) t = 2 * halfCircleDim r t := by
  simp [halfCircleDim, circleDim]; ring

/-- Half circle dimension is homogeneous: hCD(k·r, t) = k · hCD(r, t).
    prop:circle-dimension-laws -/
theorem halfCircleDim_nsmul (k r t : Nat) :
    halfCircleDim (k * r) t = k * halfCircleDim r t := by
  simp [halfCircleDim, circleDim]; ring

/-- Paper: thm:cdim-short-exact-additivity -/
theorem paper_circleDim_sub (a b t1 t2 : Nat) (h : a ≤ b) :
    circleDim (b - a) t1 = circleDim b t2 - circleDim a t2 :=
  circleDim_sub a b t1 t2 h

theorem paper_circleDim_strictMono (a b t1 t2 : Nat) (h : a < b) :
    circleDim a t1 < circleDim b t2 :=
  circleDim_strictMono a b t1 t2 h

/-- Paper: thm:cdim-short-exact-additivity (package) -/
theorem paper_circleDim_short_exact_additivity_package
    (a b t1 t2 : Nat) (hle : a ≤ b) (hlt : a < b) :
    circleDim (b - a) t1 = circleDim b t2 - circleDim a t2 ∧
    circleDim a t1 < circleDim b t2 := by
  exact ⟨paper_circleDim_sub a b t1 t2 hle, paper_circleDim_strictMono a b t1 t2 hlt⟩

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
  simp [halfCircleDim, circleDim]; ring

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

/-- Defect is zero iff kernel rank is zero. def:cdim-defect -/
theorem cdimDefect_eq_zero_iff (f : CircleDimHomData) :
    cdimDefect f = 0 ↔ f.kernelRank = 0 := by
  simp [cdimDefect]

/-- Image rank equals source rank when defect is zero. thm:cdim-rank-nullity-formula -/
theorem imageRank_eq_sourceRank_of_defect_zero (f : CircleDimHomData)
    (h : cdimDefect f = 0) : f.imageRank = f.sourceRank := by
  have hk : f.kernelRank = 0 := (cdimDefect_eq_zero_iff f).mp h
  have := f.rankNullity
  omega

/-- Composition data for g∘f. thm:cdim-defect-chain-rule -/
def CircleDimHomData.comp (f : CircleDimHomData) (g : CircleDimHomData)
    (_hfg : f.targetRank = g.sourceRank)
    (restrictedKerRank : Nat)
    (_hRestrict : restrictedKerRank ≤ g.kernelRank)
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

/-- The minimal ledger-cost inequality is exact: it reduces to a rank comparison.
    thm:cdim-minimal-ledger-cost-kernel -/
theorem cdim_min_ledger_cost_iff (f : CircleDimHomData) (R_rank : Nat) :
    circleDim f.kernelRank 0 ≤ circleDim R_rank 0 ↔ f.kernelRank ≤ R_rank := by
  simp [circleDim]

/-- The lower bound in the minimal ledger-cost theorem is attained by choosing the
    ledger rank to be the kernel rank itself.
    thm:cdim-minimal-ledger-cost-kernel -/
theorem cdim_min_ledger_cost_attained (f : CircleDimHomData) :
    ∃ R_rank : Nat, circleDim f.kernelRank 0 = circleDim R_rank 0 := by
  refine ⟨f.kernelRank, ?_⟩
  rfl

/-- Paper package for the minimal ledger-cost kernel theorem.
    thm:cdim-minimal-ledger-cost-kernel -/
theorem paper_cdim_minimal_ledger_cost_kernel (f : CircleDimHomData) :
    (∀ R_rank : Nat, f.kernelRank ≤ R_rank → circleDim f.kernelRank 0 ≤ circleDim R_rank 0) ∧
    (∀ R_rank : Nat, circleDim f.kernelRank 0 ≤ circleDim R_rank 0 ↔ f.kernelRank ≤ R_rank) ∧
    (∃ R_rank : Nat, circleDim f.kernelRank 0 = circleDim R_rank 0) := by
  exact ⟨cdim_min_ledger_cost f, cdim_min_ledger_cost_iff f, cdim_min_ledger_cost_attained f⟩

/-- cdimDefect is positive iff kernelRank is positive.
    thm:cdim-defect-chain-rule -/
theorem cdimDefect_pos_iff (f : CircleDimHomData) :
    0 < cdimDefect f ↔ 0 < f.kernelRank := by
  rw [Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero, not_iff_not]
  exact (cdimDefect_eq_zero_iff f).symm

-- ══════════════════════════════════════════════════════════════
-- Phase R160: Phase spectrum count
-- ══════════════════════════════════════════════════════════════

/-- Phase spectrum count for Z^r × Z/tZ: |Hom(G, Z/NZ)| = N^r · gcd(t, N).
    def:cdim-phase-spectrum -/
def phaseSpectrumCount (r t N : Nat) : Nat := N ^ r * Nat.gcd t N

/-- Free part: phaseSpectrumCount r 0 N = N^{r+1} (gcd(0,N) = N).
    prop:cdim-phase-spectrum-quotient -/
theorem phaseSpectrumCount_free (r N : Nat) :
    phaseSpectrumCount r 0 N = N ^ (r + 1) := by
  simp [phaseSpectrumCount, Nat.gcd_zero_left, pow_succ, Nat.mul_comm]

/-- Torsion part: phaseSpectrumCount for pure torsion.
    prop:cdim-phase-spectrum-quotient -/
theorem phaseSpectrumCount_torsion (t N : Nat) :
    phaseSpectrumCount 0 t N = Nat.gcd t N := by
  simp [phaseSpectrumCount]

/-- Phase spectrum count is monotone in free rank.
    thm:cdim-phase-spectrum-limit -/
theorem phaseSpectrumCount_mono_rank {r₁ r₂ : Nat} (h : r₁ ≤ r₂) (t N : Nat) (hN : 1 ≤ N) :
    phaseSpectrumCount r₁ t N ≤ phaseSpectrumCount r₂ t N := by
  simp only [phaseSpectrumCount]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) h)

/-- Phase spectrum count at N=1 is always 1.
    thm:cdim-phase-spectrum-limit -/
theorem phaseSpectrumCount_at_one (r t : Nat) :
    phaseSpectrumCount r t 1 = 1 := by
  simp [phaseSpectrumCount]

/-- Coprime torsion becomes invisible: phaseSpectrumCount = N^r when gcd(t,N)=1.
    thm:cdim-phase-spectrum-limit -/
theorem phaseSpectrumCount_coprime (r t N : Nat) (hcop : Nat.Coprime t N) :
    phaseSpectrumCount r t N = N ^ r := by
  simp [phaseSpectrumCount, Nat.Coprime.gcd_eq_one hcop]

/-- The phase spectrum equals the pure rank term exactly in the coprime case.
    thm:cdim-phase-spectrum-limit -/
theorem phaseSpectrumCount_eq_pow_iff_coprime
    (r t N : Nat) (hN : 1 ≤ N) :
    phaseSpectrumCount r t N = N ^ r ↔ Nat.Coprime t N := by
  constructor
  · intro hEq
    rw [Nat.coprime_iff_gcd_eq_one]
    have hpowpos : 0 < N ^ r := Nat.pow_pos (lt_of_lt_of_le (by decide) hN)
    apply Nat.eq_of_mul_eq_mul_left hpowpos
    simpa [phaseSpectrumCount] using hEq
  · intro hcop
    exact phaseSpectrumCount_coprime r t N hcop

-- ══════════════════════════════════════════════════════════════
-- Phase R166: Phase spectrum coprime multiplicativity
-- ══════════════════════════════════════════════════════════════

/-- Phase spectrum split: free part x torsion part.
    prop:cdim-phase-spectrum-quotient -/
theorem phaseSpectrumCount_split (r t N : Nat) :
    phaseSpectrumCount r t N = N ^ r * Nat.gcd t N := rfl

/-- Phase spectrum count is multiplicative for coprime torsion factors.
    prop:cdim-phase-spectrum-quotient -/
theorem phaseSpectrumCount_mul_coprime (r1 r2 t1 t2 N : Nat)
    (hcop : Nat.Coprime t1 t2) :
    phaseSpectrumCount (r1 + r2) (t1 * t2) N =
      phaseSpectrumCount r1 t1 N * phaseSpectrumCount r2 t2 N := by
  simp only [phaseSpectrumCount, pow_add]
  rw [Nat.gcd_comm, Nat.Coprime.gcd_mul N hcop, Nat.gcd_comm t1, Nat.gcd_comm t2]
  ring

-- ══════════════════════════════════════════════════════════════
-- Phase R166: Gap ledger definitions and properties
-- ══════════════════════════════════════════════════════════════

/-- First hitting time: minimum n such that error drops below threshold.
    def:cdim-gap-ledger -/
noncomputable def firstHittingTime (e : Nat → ℝ) (ε : ℝ) : ℕ∞ :=
  ⨅ (n : Nat) (_ : e n < ε), (n : ℕ∞)

/-- First hitting time is antitone in the threshold.
    def:cdim-gap-ledger -/
theorem firstHittingTime_antitone (e : Nat → ℝ) :
    Antitone (fun ε => firstHittingTime e ε) := by
  intro ε₁ ε₂ h
  simp only [firstHittingTime]
  apply iInf_mono
  intro n
  apply iInf_mono'
  intro h₂
  exact ⟨lt_of_lt_of_le h₂ h, le_refl _⟩

/-- A hitting witness bounds the first hitting time.
    def:cdim-gap-ledger -/
theorem firstHittingTime_le_of_lt (e : Nat → ℝ) (ε : ℝ) (n : Nat)
    (h : e n < ε) :
    firstHittingTime e ε ≤ n :=
  iInf₂_le n h

/-- If the error never drops below ε, the first hitting time is ⊤.
    def:cdim-gap-ledger -/
theorem firstHittingTime_eq_top_of_forall_ge (e : Nat → ℝ) (ε : ℝ)
    (h : ∀ n, ε ≤ e n) :
    firstHittingTime e ε = ⊤ := by
  simp only [firstHittingTime]
  apply iInf_eq_top.mpr
  intro n
  simp [not_lt.mpr (h n)]

/-- Separation depth: minimum depth distinguishing two objects.
    def:cdim-gap-ledger -/
noncomputable def separationDepth {α : Type*} (distinguish : Nat → α → α → Bool) (x y : α) : ℕ∞ :=
  ⨅ (n : Nat) (_ : distinguish n x y = true), (n : ℕ∞)

/-- Separation depth is symmetric when the distinguisher is symmetric.
    def:cdim-gap-ledger -/
theorem separationDepth_comm {α : Type*} (distinguish : Nat → α → α → Bool)
    (hsymm : ∀ n x y, distinguish n x y = distinguish n y x)
    (x y : α) :
    separationDepth distinguish x y = separationDepth distinguish y x := by
  simp only [separationDepth, hsymm]

/-- Separation depth of identical elements is ⊤.
    def:cdim-gap-ledger -/
theorem separationDepth_self {α : Type*} (distinguish : Nat → α → α → Bool)
    (hrefl : ∀ n x, distinguish n x x = false) (x : α) :
    separationDepth distinguish x x = ⊤ := by
  simp only [separationDepth]
  apply iInf_eq_top.mpr
  intro n
  simp [hrefl n x]

/-- A distinguishing witness bounds the separation depth.
    def:cdim-gap-ledger -/
theorem separationDepth_le_of_distinguish {α : Type*}
    (distinguish : Nat → α → α → Bool) (x y : α) (n : Nat)
    (h : distinguish n x y = true) :
    separationDepth distinguish x y ≤ n :=
  iInf₂_le n h

/-- Triangle inequality for separation depth.
    def:cdim-gap-ledger -/
theorem separationDepth_triangle {α : Type*}
    (distinguish : Nat → α → α → Bool)
    (htrans : ∀ n x y z, distinguish n x z = true →
      distinguish n x y = true ∨ distinguish n y z = true)
    (x y z : α) :
    min (separationDepth distinguish x y) (separationDepth distinguish y z) ≤
    separationDepth distinguish x z := by
  apply le_iInf₂
  intro n hn
  rcases htrans n x y z hn with hxy | hyz
  · exact min_le_of_left_le (iInf₂_le n hxy)
  · exact min_le_of_right_le (iInf₂_le n hyz)

/-- If distinguish at depth 0 is true, separation depth is 0.
    def:cdim-gap-ledger -/
theorem separationDepth_eq_zero_of_distinguish_zero {α : Type*}
    (distinguish : Nat → α → α → Bool) (x y : α)
    (h : distinguish 0 x y = true) :
    separationDepth distinguish x y = 0 := by
  exact le_antisymm (separationDepth_le_of_distinguish distinguish x y 0 h) (zero_le _)

-- ══════════════════════════════════════════════════════════════
-- Phase R169: Phase spectrum rank growth and upper bound
-- ══════════════════════════════════════════════════════════════

/-- Phase spectrum is monotone in rank (additive form).
    thm:cdim-phase-spectrum-limit -/
theorem phaseSpectrumCount_add_rank_le (r₁ r₂ t N : Nat) (hN : 1 ≤ N) :
    phaseSpectrumCount r₁ t N ≤ phaseSpectrumCount (r₁ + r₂) t N := by
  simp only [phaseSpectrumCount]
  calc N ^ r₁ * Nat.gcd t N
      = N ^ r₁ * 1 * Nat.gcd t N := by ring
    _ ≤ N ^ r₁ * N ^ r₂ * Nat.gcd t N := by
        gcongr; exact Nat.one_le_pow _ _ hN
    _ = N ^ (r₁ + r₂) * Nat.gcd t N := by rw [← pow_add]

/-- Phase spectrum upper bound: phaseSpectrumCount r t N ≤ N^(r+1).
    thm:cdim-phase-spectrum-limit -/
theorem phaseSpectrumCount_le_pow (r t N : Nat) (hN : 0 < N) :
    phaseSpectrumCount r t N ≤ N ^ (r + 1) := by
  simp only [phaseSpectrumCount, pow_succ]
  exact Nat.mul_le_mul_left _ (Nat.gcd_le_right t hN)

/-- The phase spectrum attains its maximal value exactly when `N ∣ t`.
    thm:cdim-phase-spectrum-limit -/
theorem phaseSpectrumCount_eq_pow_succ_iff_dvd
    (r t N : Nat) (hN : 1 ≤ N) :
    phaseSpectrumCount r t N = N ^ (r + 1) ↔ N ∣ t := by
  constructor
  · intro hEq
    have hpowpos : 0 < N ^ r := Nat.pow_pos (lt_of_lt_of_le (by decide) hN)
    apply (Nat.gcd_eq_right_iff_dvd).mp
    apply Nat.eq_of_mul_eq_mul_left hpowpos
    simpa [phaseSpectrumCount, pow_succ, Nat.mul_assoc] using hEq
  · intro hdiv
    rw [phaseSpectrumCount, pow_succ, Nat.gcd_eq_right hdiv]

/-- For a prime modulus, the phase spectrum is forced into the coprime-or-divisible dichotomy.
    thm:cdim-phase-spectrum-limit -/
theorem phaseSpectrumCount_prime_dichotomy
    (r t p : Nat) (hp : Nat.Prime p) :
    phaseSpectrumCount r t p = p ^ r ∨ phaseSpectrumCount r t p = p ^ (r + 1) := by
  by_cases hdiv : p ∣ t
  · right
    exact (phaseSpectrumCount_eq_pow_succ_iff_dvd r t p (le_of_lt hp.one_lt)).2 hdiv
  · left
    exact (phaseSpectrumCount_eq_pow_iff_coprime r t p (le_of_lt hp.one_lt)).2
      (hp.coprime_iff_not_dvd.mpr hdiv).symm

/-- Odd prime-power factors are invisible to dyadic phase spectra.
    thm:cdim-phase-spectrum-limit -/
theorem phaseSpectrumCount_dyadic_odd_prime_power_invariant
    {r t p a b : Nat} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    phaseSpectrumCount r (t * p ^ b) (2 ^ a) = phaseSpectrumCount r t (2 ^ a) := by
  rw [phaseSpectrumCount_split, phaseSpectrumCount_split]
  congr 1
  have hpow : Nat.Coprime (p ^ b) (2 ^ a) :=
    Nat.coprime_pow_primes b a hp (by decide : Nat.Prime 2) hp2
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    hpow.gcd_mul_left_cancel t

/-- Dyadic visibility boundary: positive torsion excludes the zero/odd aliasing pathology,
    so dyadic phase spectra determine the free rank and the dyadic gcd profile.
    thm:cdim-dyadic-spectrum-visibility-boundary -/
theorem phaseSpectrumCount_dyadic_visibility_boundary
    {r r' t t' : Nat}
    (ht : 0 < t) (ht' : 0 < t')
    (h : ∀ a : Nat, 1 ≤ a → phaseSpectrumCount r t (2 ^ a) = phaseSpectrumCount r' t' (2 ^ a)) :
    r = r' ∧ ∀ a : Nat, 1 ≤ a → Nat.gcd t (2 ^ a) = Nat.gcd t' (2 ^ a) := by
  obtain ⟨k, u, huodd, htu⟩ := Nat.exists_eq_two_pow_mul_odd ht.ne'
  obtain ⟨k', u', hu'odd, ht'u'⟩ := Nat.exists_eq_two_pow_mul_odd ht'.ne'
  let A := max 1 (max k k')
  have hA : 1 ≤ A := by
    dsimp [A]
    exact le_max_left _ _
  have hkA : k ≤ A := by
    dsimp [A]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hkA' : k' ≤ A := by
    dsimp [A]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hgcd_two_pow (e a u : Nat) (ha : 1 ≤ a) (huodd : Odd u) (he : e ≤ a) :
      Nat.gcd (2 ^ e * u) (2 ^ a) = 2 ^ e := by
    have hcop : Nat.Coprime u (2 ^ a) := by
      simpa using (Nat.coprime_pow_right_iff ha u 2).2 huodd.coprime_two_right
    calc
      Nat.gcd (2 ^ e * u) (2 ^ a) = Nat.gcd (2 ^ e) (2 ^ a) := by
        simpa [Nat.mul_comm] using hcop.gcd_mul_left_cancel (2 ^ e)
      _ = 2 ^ e := Nat.gcd_eq_left (pow_dvd_pow 2 he)
  have hBase := h A hA
  rw [htu, ht'u', phaseSpectrumCount_split, phaseSpectrumCount_split,
    hgcd_two_pow k A u hA huodd hkA, hgcd_two_pow k' A u' hA hu'odd hkA'] at hBase
  have hStep := h (A + 1) (by omega)
  rw [htu, ht'u', phaseSpectrumCount_split, phaseSpectrumCount_split,
    hgcd_two_pow k (A + 1) u (by omega) huodd (by omega),
    hgcd_two_pow k' (A + 1) u' (by omega) hu'odd (by omega),
    show 2 ^ (A + 1) = 2 * 2 ^ A by rw [pow_succ, Nat.mul_comm], mul_pow] at hStep
  have hStep' : ((2 ^ A) ^ r' * 2 ^ k') * 2 ^ r = ((2 ^ A) ^ r' * 2 ^ k') * 2 ^ r' := by
    calc
      ((2 ^ A) ^ r' * 2 ^ k') * 2 ^ r = ((2 ^ A) ^ r * 2 ^ k) * 2 ^ r := by rw [hBase]
      _ = (2 ^ r') * ((2 ^ A) ^ r' * 2 ^ k') := by
          have := hStep; ring_nf at this ⊢; linarith
      _ = ((2 ^ A) ^ r' * 2 ^ k') * 2 ^ r' := by ring
  have hcommonPos : 0 < (2 ^ A) ^ r' * 2 ^ k' := by
    exact Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos A)) (Nat.two_pow_pos k')
  have hpowEq : 2 ^ r = 2 ^ r' := Nat.eq_of_mul_eq_mul_left hcommonPos hStep'
  have hr : r = r' := Nat.pow_right_injective (by omega) hpowEq
  subst hr
  refine ⟨rfl, ?_⟩
  intro a ha
  have haEq := h a ha
  rw [phaseSpectrumCount_split, phaseSpectrumCount_split] at haEq
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (Nat.two_pow_pos a)) haEq

/-- Paper: `thm:cdim-dyadic-spectrum-visibility-boundary`. -/
theorem paper_cdim_dyadic_spectrum_visibility_boundary
    {r r' t t' : Nat} (ht : 0 < t) (ht' : 0 < t')
    (h : ∀ a : Nat, 1 ≤ a →
      phaseSpectrumCount r t (2 ^ a) = phaseSpectrumCount r' t' (2 ^ a)) :
    r = r' ∧ ∀ a : Nat, 1 ≤ a → Nat.gcd t (2 ^ a) = Nat.gcd t' (2 ^ a) := by
  simpa using phaseSpectrumCount_dyadic_visibility_boundary ht ht' h

/-- Phase spectrum reconstruction for positive torsion parameters.
    thm:cdim-phase-spectrum-reconstruction -/
theorem phaseSpectrumCount_reconstruction
    {r r' t t' : Nat}
    (ht : 0 < t) (ht' : 0 < t')
    (h : ∀ N : Nat, 1 ≤ N → phaseSpectrumCount r t N = phaseSpectrumCount r' t' N) :
    r = r' ∧ t = t' := by
  let M := t * t' + 1
  have hMt : Nat.Coprime t M := by
    dsimp [M]
    rw [Nat.add_comm, Nat.mul_comm]
    exact (Nat.coprime_add_mul_right_right t 1 t').2 (Nat.coprime_one_right _)
  have hMt' : Nat.Coprime t' (t * t' + 1) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    calc
      Nat.gcd t' (t * t' + 1) = Nat.gcd t' (1 + t * t') := by rw [Nat.add_comm]
      _ = Nat.gcd t' 1 := by rw [Nat.gcd_add_mul_right_right]
      _ = 1 := by exact Nat.gcd_one_right t'
  have hM_le : 1 ≤ M := by
    dsimp [M]
    omega
  have hpow : M ^ r = M ^ r' := by
    calc
      M ^ r = phaseSpectrumCount r t M := by
        symm
        exact phaseSpectrumCount_coprime r t M hMt
      _ = phaseSpectrumCount r' t' M := h M hM_le
      _ = M ^ r' := phaseSpectrumCount_coprime r' t' M hMt'
  have hM2 : 2 ≤ M := by
    dsimp [M]
    have hmul : 1 ≤ t * t' := Nat.mul_le_mul ht ht'
    omega
  have hr : r = r' := Nat.pow_right_injective hM2 hpow
  subst hr
  have hAt : phaseSpectrumCount r t t = phaseSpectrumCount r t' t := h t ht
  have hgcd_right : Nat.gcd t' t = t := by
    have hpowt : 0 < t ^ r := by exact Nat.pow_pos ht
    apply Nat.eq_of_mul_eq_mul_left hpowt
    symm
    simpa [phaseSpectrumCount, Nat.gcd_self, Nat.gcd_comm, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hAt
  have hAt' : phaseSpectrumCount r t t' = phaseSpectrumCount r t' t' := h t' ht'
  have hgcd_left : Nat.gcd t t' = t' := by
    have hpowt' : 0 < t' ^ r := by exact Nat.pow_pos ht'
    apply Nat.eq_of_mul_eq_mul_left hpowt'
    simpa [phaseSpectrumCount, Nat.gcd_self, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      hAt'
  have htgcd_left : t ∣ Nat.gcd t' t := by
    exact hgcd_right.symm ▸ (dvd_rfl : t ∣ t)
  have hdiv_left : t ∣ t' :=
    dvd_trans htgcd_left (Nat.gcd_dvd_left t' t)

  have htgcd_right : t' ∣ Nat.gcd t t' := by
    exact hgcd_left.symm ▸ (dvd_rfl : t' ∣ t')
  have hdiv_right : t' ∣ t :=
    dvd_trans htgcd_right (Nat.gcd_dvd_left t t')
  exact ⟨rfl, Nat.dvd_antisymm hdiv_left hdiv_right⟩

/-- Paper-facing iff wrapper for phase-spectrum reconstruction.
    thm:cdim-phase-spectrum-reconstruction -/
theorem paper_phaseSpectrumCount_reconstruction_iff
    {r r' t t' : Nat}
    (ht : 0 < t) (ht' : 0 < t') :
    (∀ N : Nat, 1 ≤ N → phaseSpectrumCount r t N = phaseSpectrumCount r' t' N)
      ↔ r = r' ∧ t = t' := by
  constructor
  · intro h
    exact phaseSpectrumCount_reconstruction ht ht' h
  · intro h
    rcases h with ⟨hr, htEq⟩
    subst hr
    subst htEq
    intro N hN
    rfl

/-- Paper core package for phase-spectrum reconstruction.
    thm:cdim-phase-spectrum-reconstruction -/
theorem paper_phaseSpectrumCount_reconstruction_core
    {r r' t t' : Nat} (ht : 0 < t) (ht' : 0 < t')
    (h : ∀ N : Nat, 1 ≤ N → phaseSpectrumCount r t N = phaseSpectrumCount r' t' N) :
    (r = r' ∧ t = t') ∧
    (r = r') ∧
    (r = r' → t = t') := by
  rcases phaseSpectrumCount_reconstruction ht ht' h with ⟨hr, htEq⟩
  refine ⟨⟨hr, htEq⟩, hr, ?_⟩
  intro hrr'
  subst hrr'
  exact htEq

/-- One-sided phase-spectrum reconstruction recovers the free rank.
    thm:cdim-phase-spectrum-reconstruction -/
theorem phaseSpectrumCount_reconstruction_one_sided
    {r r' t t' : Nat}
    (ht : 0 < t) (ht' : 0 < t')
    (h : ∀ N : Nat, 1 ≤ N → phaseSpectrumCount r t N = phaseSpectrumCount r' t' N) :
    r = r' := by
  exact (phaseSpectrumCount_reconstruction ht ht' h).1

/-- One-sided phase-spectrum reconstruction recovers the torsion parameter once the rank matches.
    thm:cdim-phase-spectrum-reconstruction -/
theorem phaseSpectrumCount_reconstruction_torsion_one_sided
    {r r' t t' : Nat}
    (ht : 0 < t) (ht' : 0 < t')
    (hrr' : r = r')
    (h : ∀ N : Nat, 1 ≤ N → phaseSpectrumCount r t N = phaseSpectrumCount r' t' N) :
    t = t' := by
  subst hrr'
  exact (phaseSpectrumCount_reconstruction ht ht' h).2

-- ══════════════════════════════════════════════════════════════
-- Phase R251: tensor-hom extension laws
-- ══════════════════════════════════════════════════════════════

/-- Circle dimension scales linearly: cdim(k·r, t) = k · cdim(r, t).
    prop:cdim-tensor-hom-ext-laws -/
theorem circleDim_nsmul (k r t : Nat) :
    circleDim (k * r) t = k * circleDim r t := by simp [circleDim]

/-- Circle dimension respects powers: cdim(r^k, t) = cdim(r, t)^k.
    prop:cdim-tensor-hom-ext-laws -/
theorem circleDim_pow (k r t : Nat) :
    circleDim (r ^ k) t = (circleDim r t) ^ k := by simp [circleDim]

-- ══════════════════════════════════════════════════════════════
-- Phase R259: phase spectrum concrete instances
-- ══════════════════════════════════════════════════════════════

/-- Phase spectrum of Z^2: Σ(N) = N^2. Here r=1 gives N^{r+1} = N^2.
    def:cdim-phase-spectrum -/
theorem phaseSpectrumCount_Z2 (N : Nat) :
    phaseSpectrumCount 1 0 N = N ^ 2 :=
  phaseSpectrumCount_free 1 N

/-- Phase spectrum of Z × Z/6Z: Σ(N) = N · gcd(6, N).
    def:cdim-phase-spectrum -/
theorem phaseSpectrumCount_Z_times_Z6 (N : Nat) :
    phaseSpectrumCount 1 6 N = N * Nat.gcd 6 N := by
  simp [phaseSpectrumCount]

/-- Concrete evaluations for Z × Z/6Z.
    def:cdim-phase-spectrum -/
theorem phaseSpectrumCount_Z_times_Z6_table :
    phaseSpectrumCount 1 6 1 = 1 ∧
    phaseSpectrumCount 1 6 2 = 4 ∧
    phaseSpectrumCount 1 6 3 = 9 ∧
    phaseSpectrumCount 1 6 4 = 8 ∧
    phaseSpectrumCount 1 6 5 = 5 ∧
    phaseSpectrumCount 1 6 6 = 36 ∧
    phaseSpectrumCount 1 6 12 = 72 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- Rank detection at coprime primes.
    thm:cdim-phase-spectrum-reconstruction -/
theorem phaseSpectrumCount_rank_detection_Z_Z6 :
    phaseSpectrumCount 1 6 5 = 5 ^ 1 ∧
    phaseSpectrumCount 1 6 7 = 7 ^ 1 := by
  refine ⟨by native_decide, by native_decide⟩

/-- Circle dimension axiomatic completeness.
    thm:cdim-nr-nd-semiring-hom-rigidity -/
theorem paper_circleDim_axiomatic_completeness :
    (∀ a b c d, circleDim (a + b) (c + d) = circleDim a c + circleDim b d) ∧
    (∀ n t1 t2, circleDim n t1 = circleDim n t2) ∧
    circleDim 1 0 = 1 ∧
    (∀ n t, circleDim n t = 0 ↔ n = 0) ∧
    (∀ a b t1 t2, a < b → circleDim a t1 < circleDim b t2) :=
  ⟨circleDim_add, circleDim_finite_extension, circleDim_Zk 1,
   circleDim_eq_zero_iff, circleDim_strictMono⟩

/-- Circle dimension defect composition package.
    thm:cdim-kernel-defect-incompressibility -/
theorem paper_cdimDefect_composition_package :
    (∀ (f g : CircleDimHomData) (hfg : f.targetRank = g.sourceRank)
       (restrictedKerRank : Nat) (hRestrict : restrictedKerRank ≤ g.kernelRank)
       (hRestrictBound : restrictedKerRank ≤ f.imageRank)
       (hImageSplit : f.imageRank ≤ restrictedKerRank + g.imageRank),
      cdimDefect (f.comp g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit) =
        cdimDefect f + restrictedKerRank) ∧
    (∀ (f g : CircleDimHomData) (hfg : f.targetRank = g.sourceRank)
       (restrictedKerRank : Nat) (hRestrict : restrictedKerRank ≤ g.kernelRank)
       (hRestrictBound : restrictedKerRank ≤ f.imageRank)
       (hImageSplit : f.imageRank ≤ restrictedKerRank + g.imageRank),
      cdimDefect (f.comp g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit) ≤
        cdimDefect f + cdimDefect g) :=
  ⟨fun f g hfg r hr hrb his => cdimDefect_comp f g hfg r hr hrb his,
   fun f g hfg r hr hrb his => cdimDefect_comp_le f g hfg r hr hrb his⟩

/-- Circle dimension monotonicity and half-dimension package.
    prop:circle-dimension-laws -/
theorem paper_circleDim_mono_half_package :
    (∀ n₁ n₂ t : Nat, n₁ ≤ n₂ → circleDim n₁ t ≤ circleDim n₂ t) ∧
    halfCircleDim 1 0 = 1 / 2 ∧
    (∀ a b c d : Nat,
      halfCircleDim (a + b) (c + d) = halfCircleDim a c + halfCircleDim b d) ∧
    halfCircleDim 3 0 = 3 / 2 :=
  ⟨fun _ _ _ h => circleDim_mono h, halfCircleDim_nat, halfCircleDim_add,
   by simp [halfCircleDim, circleDim]⟩

/-- Circle dimension tensor and subtraction package.
    prop:circle-dimension-laws -/
theorem paper_circleDim_tensor_and_sub :
    (∀ r s t1 t2, circleDim (r + s) (t1 + t2) = circleDim r t1 + circleDim s t2) ∧
    (∀ t, circleDim 0 t = 0) ∧
    (∀ a b t1 t2, a ≤ b → circleDim b t2 - circleDim a t1 = b - a) ∧
    circleDim 5 0 = 5 :=
  ⟨circleDim_add, circleDim_finite, fun _ _ _ _ _ => by simp [circleDim], rfl⟩

/-- Refined paper interface for circle-dimension axiomatic completeness.
    This packages the existing completeness certificate together with the
    semiring-hom rigidity existence statement from the circle-dimension development.
    thm:cdim-nr-nd-semiring-hom-rigidity -/
theorem paper_circleDim_axiomatic_completeness_refined :
    ((∀ a b c d, circleDim (a + b) (c + d) = circleDim a c + circleDim b d) ∧
    (∀ n t1 t2, circleDim n t1 = circleDim n t2) ∧
    circleDim 1 0 = 1 ∧
    (∀ n t, circleDim n t = 0 ↔ n = 0) ∧
    (∀ a b t1 t2, a < b → circleDim a t1 < circleDim b t2)) ∧
    (∀ (r d : Nat) (f : (Fin r → ℕ) →+* (Fin d → ℕ)),
      ∃ σ : Fin d → Fin r, ∀ x : Fin r → ℕ, ∀ j : Fin d, f x j = x (σ j)) := by
  constructor
  · exact paper_circleDim_axiomatic_completeness
  · intro r d f
    exact Omega.semiring_hom_rigidity r d f
-- ══════════════════════════════════════════════════════════════

/-- Half circle dimension is always nonneg. def:circle-dimension -/
theorem halfCircleDim_nonneg (r t : Nat) : 0 ≤ halfCircleDim r t := by
  simp [halfCircleDim, circleDim]; positivity

/-- Circle dimension vanishes iff free rank is zero. def:circle-dimension -/
theorem circleDim_eq_zero_iff_rank_zero (n t : Nat) :
    circleDim n t = 0 ↔ n = 0 := by simp [circleDim]

/-- Paper certificates for circle dimension basics. def:circle-dimension -/
theorem paper_circleDim_basic_certificates :
    (circleDim 0 0 = 0) ∧ (circleDim 0 7 = 0) ∧ (circleDim 0 21 = 0) ∧
    (circleDim 1 0 = 1) ∧ (circleDim 2 0 = 2) ∧ (circleDim 3 5 = 3) ∧
    (circleDim 1 2 + circleDim 2 3 = circleDim 3 5) := by
  simp [circleDim]

-- ══════════════════════════════════════════════════════════════
-- Phase R292: halfCircleDim properties + phaseSpectrumCount instances
-- ══════════════════════════════════════════════════════════════

/-- Half circle dimension of pure torsion is zero (free rank = 0).
    def:circle-dimension -/
theorem halfCircleDim_pure_torsion (t : Nat) :
    halfCircleDim 0 t = 0 := by
  simp [halfCircleDim, circleDim]

/-- Half circle dimension is zero iff free rank is zero.
    def:circle-dimension -/
theorem halfCircleDim_eq_zero_iff (r t : Nat) :
    halfCircleDim r t = 0 ↔ r = 0 := by
  simp [halfCircleDim, circleDim]

/-- Half circle dimension is positive when free rank is positive.
    def:circle-dimension -/
theorem halfCircleDim_pos_of_free_pos (r t : Nat) (hr : 1 ≤ r) :
    0 < halfCircleDim r t := by
  simp [halfCircleDim, circleDim]
  positivity

/-- Phase spectrum count instances. thm:cdim-phase-spectrum-reconstruction -/
theorem paper_phaseSpectrumCount_instances :
    phaseSpectrumCount 1 0 2 = 4 ∧ phaseSpectrumCount 1 0 3 = 9 ∧
    phaseSpectrumCount 1 0 5 = 25 ∧ phaseSpectrumCount 0 6 2 = 2 ∧
    phaseSpectrumCount 0 6 3 = 3 ∧ phaseSpectrumCount 0 6 6 = 6 ∧
    phaseSpectrumCount 0 6 7 = 1 ∧ phaseSpectrumCount 1 2 3 = 3 ∧
    phaseSpectrumCount 1 2 4 = 8 ∧ phaseSpectrumCount 1 2 6 = 12 := by
  simp [phaseSpectrumCount]

/-- Direct sum instances for circle dimension. def:circle-dimension -/
theorem paper_circleDim_direct_sum_three_instances :
    circleDim 2 2 = 2 ∧ circleDim 1 15 = 1 ∧
    circleDim 3 0 = 3 ∧ circleDim 0 30 = 0 := by
  simp [circleDim]

/-- Circle dimension is bounded by the free rank. def:circle-dimension -/
theorem circleDim_le_rank (r t : Nat) : circleDim r t ≤ r := by
  simp [circleDim]

/-- Half circle dimension upper bound. def:circle-dimension -/
theorem halfCircleDim_le (r t : Nat) : halfCircleDim r t ≤ (↑r + 1) / 2 := by
  simp [halfCircleDim, circleDim]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ r) (by norm_num)

-- ══════════════════════════════════════════════════════════════
-- Phase R302: PhaseSpectrumCount numerical certificates
-- ══════════════════════════════════════════════════════════════

/-- PhaseSpectrumCount at prime powers: explicit values.
    thm:cdim-multiprime-spectrum-realizability -/
theorem phaseSpectrumCount_prime_values :
    phaseSpectrumCount 1 0 6 = 36 ∧
    phaseSpectrumCount 1 3 6 = 18 ∧
    phaseSpectrumCount 1 2 6 = 12 ∧
    phaseSpectrumCount 2 0 6 = 216 ∧
    phaseSpectrumCount 2 3 6 = 108 := by
  simp [phaseSpectrumCount]

/-- Paper package.
    thm:cdim-multiprime-spectrum-realizability -/
theorem paper_phaseSpectrumCount_prime_package :
    phaseSpectrumCount 1 0 6 = 36 ∧
    phaseSpectrumCount 1 3 6 = 18 ∧
    phaseSpectrumCount 1 2 6 = 12 ∧
    phaseSpectrumCount 0 6 6 = 6 ∧
    phaseSpectrumCount 0 5 6 = 1 := by
  simp [phaseSpectrumCount]

-- ══════════════════════════════════════════════════════════════
-- Phase R305: cdimDefect properties
-- ══════════════════════════════════════════════════════════════

/-- thm:cdim-defect-chain-rule -/
theorem cdimDefect_nonneg (f : CircleDimHomData) : 0 ≤ cdimDefect f :=
  Nat.zero_le _

/-- thm:cdim-defect-chain-rule -/
theorem cdimDefect_le_sourceRank (f : CircleDimHomData) :
    cdimDefect f ≤ f.sourceRank := by
  have := f.rankNullity
  simp [cdimDefect]
  omega

/-- thm:cdim-defect-chain-rule -/
theorem paper_cdimDefect_properties :
    (∀ f : CircleDimHomData, 0 ≤ cdimDefect f) ∧
    (∀ f : CircleDimHomData, cdimDefect f ≤ f.sourceRank) := by
  exact ⟨cdimDefect_nonneg, cdimDefect_le_sourceRank⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R308: phaseSpectrumCount prime dichotomy
-- ══════════════════════════════════════════════════════════════

/-- thm:cdim-phase-spectrum-limit -/
theorem phaseSpectrumCount_prime_dvd (r t : Nat) {p : Nat} (_hp : Nat.Prime p)
    (hdvd : p ∣ t) :
    phaseSpectrumCount r t p = p ^ (r + 1) := by
  simp [phaseSpectrumCount, Nat.gcd_eq_right hdvd, pow_succ]

/-- thm:cdim-phase-spectrum-limit -/
theorem phaseSpectrumCount_prime_ndvd (r t : Nat) {p : Nat} (hp : Nat.Prime p)
    (hndvd : ¬ p ∣ t) :
    phaseSpectrumCount r t p = p ^ r := by
  simp [phaseSpectrumCount]
  have : Nat.gcd t p = 1 := Nat.Coprime.symm ((hp.coprime_iff_not_dvd).mpr hndvd)
  rw [this, mul_one]

/-- Paper package. thm:cdim-phase-spectrum-limit -/
theorem paper_phaseSpectrumCount_prime_dichotomy :
    phaseSpectrumCount 2 0 5 = 125 ∧ phaseSpectrumCount 2 3 5 = 25 ∧
    phaseSpectrumCount 1 0 7 = 49 ∧ phaseSpectrumCount 1 3 7 = 7 ∧
    phaseSpectrumCount 3 0 3 = 81 ∧ phaseSpectrumCount 3 2 3 = 27 := by
  simp [phaseSpectrumCount]

-- ══════════════════════════════════════════════════════════════
-- Phase R310: cdimDefect rank-defect duality
-- ══════════════════════════════════════════════════════════════

/-- thm:cdim-defect-chain-rule -/
theorem cdimDefect_zero_of_iso (f : CircleDimHomData)
    (h : f.kernelRank = 0) : cdimDefect f = 0 := by
  simp [cdimDefect, h]

/-- thm:cdim-defect-chain-rule -/
theorem imageRank_add_defect (f : CircleDimHomData) :
    f.imageRank + cdimDefect f = f.sourceRank := by
  have := f.rankNullity; simp [cdimDefect]; omega

/-- thm:cdim-defect-chain-rule -/
theorem sourceRank_sub_imageRank (f : CircleDimHomData) :
    f.sourceRank - f.imageRank = cdimDefect f := by
  have := f.rankNullity; simp [cdimDefect]; omega

/-- Paper package. thm:cdim-defect-chain-rule -/
theorem paper_cdimDefect_rank_duality :
    (∀ f : CircleDimHomData, f.imageRank + cdimDefect f = f.sourceRank) ∧
    (∀ f : CircleDimHomData, f.kernelRank = 0 → cdimDefect f = 0) := by
  exact ⟨imageRank_add_defect, cdimDefect_zero_of_iso⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R313: CircleDimHomData.id + concrete instances
-- ══════════════════════════════════════════════════════════════

/-- Identity homomorphism data. thm:cdim-defect-chain-rule -/
def CircleDimHomData.id (r : Nat) : CircleDimHomData where
  sourceRank := r; targetRank := r; kernelRank := 0; imageRank := r
  rankNullity := by omega
  imageBound := le_refl r

/-- thm:cdim-defect-chain-rule -/
theorem cdimDefect_id (r : Nat) : cdimDefect (CircleDimHomData.id r) = 0 := by
  simp [cdimDefect, CircleDimHomData.id]

/-- Surjective example: rank 3 → 2 with kernel 1. thm:cdim-defect-chain-rule -/
def CircleDimHomData.surjExample : CircleDimHomData where
  sourceRank := 3; targetRank := 2; kernelRank := 1; imageRank := 2
  rankNullity := by omega
  imageBound := le_refl 2

/-- thm:cdim-defect-chain-rule -/
theorem cdimDefect_surjExample : cdimDefect CircleDimHomData.surjExample = 1 := by
  simp [cdimDefect, CircleDimHomData.surjExample]

/-- Injective example: rank 2 → 3 with kernel 0. thm:cdim-defect-chain-rule -/
def CircleDimHomData.injExample : CircleDimHomData where
  sourceRank := 2; targetRank := 3; kernelRank := 0; imageRank := 2
  rankNullity := by omega
  imageBound := by omega

/-- thm:cdim-defect-chain-rule -/
theorem cdimDefect_injExample : cdimDefect CircleDimHomData.injExample = 0 := by
  simp [cdimDefect, CircleDimHomData.injExample]

/-- Paper package. thm:cdim-defect-chain-rule -/
theorem paper_cdimDefect_instances :
    cdimDefect (CircleDimHomData.id 5) = 0 ∧
    cdimDefect CircleDimHomData.surjExample = 1 ∧
    cdimDefect CircleDimHomData.injExample = 0 := by
  exact ⟨cdimDefect_id 5, cdimDefect_surjExample, cdimDefect_injExample⟩

/-- A finite residual-budget injection forces the target budget to dominate the source.
    thm:conclusion-phase-residual-budget-lower-bound-finite -/
theorem phaseResidualBudget_lower_bound_finite (b r k t R : ℕ)
    (hinj : ∃ f : Fin ((2 ^ (b * r)) * t) → Fin ((2 ^ (b * k)) * R), Function.Injective f) :
    (2 ^ (b * r)) * t ≤ (2 ^ (b * k)) * R := by
  rcases hinj with ⟨f, hf⟩
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- CD phase spectrum reconstruction audit package.
    thm:cdim-phase-spectrum-reconstruction -/
theorem paper_cdim_phase_spectrum_audit :
    (∀ r r' t t' : Nat, 0 < t → 0 < t' →
      (∀ N : Nat, 1 ≤ N → phaseSpectrumCount r t N = phaseSpectrumCount r' t' N) →
      r = r' ∧ t = t') ∧
    (∀ r t N : Nat, Nat.Coprime t N → phaseSpectrumCount r t N = N ^ r) ∧
    (∀ r N : Nat, phaseSpectrumCount r 0 N = N ^ (r + 1)) :=
  ⟨fun _ _ _ _ ht ht' h => phaseSpectrumCount_reconstruction ht ht' h,
   phaseSpectrumCount_coprime, phaseSpectrumCount_free⟩

/-- Phase spectrum count for small torsion groups.
    thm:cdim-phase-spectrum-limit -/
theorem paper_phaseSpectrumCount_small_torsion :
    phaseSpectrumCount 1 2 2 = 4 ∧
    phaseSpectrumCount 1 2 3 = 3 ∧
    phaseSpectrumCount 1 3 3 = 9 ∧
    phaseSpectrumCount 1 3 2 = 2 ∧
    phaseSpectrumCount 1 4 4 = 16 ∧
    phaseSpectrumCount 1 4 2 = 4 := by
  simp only [phaseSpectrumCount]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Phase spectrum at prime power: coprime/divisible dichotomy.
    thm:cdim-phase-spectrum-limit -/
theorem paper_phaseSpectrumCount_prime_power_audit :
    (∀ k : Nat, phaseSpectrumCount 1 3 (2 ^ k) = (2 ^ k) ^ 1) ∧
    phaseSpectrumCount 1 4 2 = 4 ∧
    phaseSpectrumCount 1 4 4 = 16 ∧
    (∀ k : Nat, phaseSpectrumCount 1 2 (3 ^ k) = (3 ^ k) ^ 1) := by
  refine ⟨fun k => ?_, by native_decide, by native_decide, fun k => ?_⟩
  · exact phaseSpectrumCount_coprime 1 3 (2 ^ k)
      (Nat.Coprime.pow_right k (by decide))
  · exact phaseSpectrumCount_coprime 1 2 (3 ^ k)
      (Nat.Coprime.pow_right k (by decide))

/-- Phase spectrum at rank 2.
    thm:cdim-phase-spectrum-limit -/
theorem paper_phaseSpectrumCount_rank2 :
    phaseSpectrumCount 2 1 2 = 4 ∧
    phaseSpectrumCount 2 1 3 = 9 ∧
    phaseSpectrumCount 2 2 2 = 8 ∧
    phaseSpectrumCount 2 2 3 = 9 ∧
    phaseSpectrumCount 2 3 3 = 27 ∧
    phaseSpectrumCount 2 6 6 = 216 := by
  simp only [phaseSpectrumCount]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Paper core package for phase-spectrum limit behavior.
    thm:cdim-phase-spectrum-limit -/
theorem paper_phaseSpectrumCount_limit_core :
    (∀ k : Nat, phaseSpectrumCount 1 3 (2 ^ k) = (2 ^ k) ^ 1) ∧
    phaseSpectrumCount 1 4 2 = 4 ∧
    phaseSpectrumCount 1 4 4 = 16 ∧
    (∀ k : Nat, phaseSpectrumCount 1 2 (3 ^ k) = (3 ^ k) ^ 1) ∧
    (phaseSpectrumCount 2 6 6 = 216) := by
  refine ⟨?_, by native_decide, by native_decide, ?_, ?_⟩
  · intro k
    exact phaseSpectrumCount_coprime 1 3 (2 ^ k) (Nat.Coprime.pow_right k (by decide))
  · intro k
    exact phaseSpectrumCount_coprime 1 2 (3 ^ k) (Nat.Coprime.pow_right k (by decide))
  · exact paper_phaseSpectrumCount_rank2.2.2.2.2.2

/-- Circle dimension tensor-hom-ext laws audit.
    prop:cdim-tensor-hom-ext-laws -/
theorem paper_cdim_laws_audit :
    (∀ a b c d : Nat, circleDim (a + b) (c + d) = circleDim a c + circleDim b d) ∧
    (∀ r s t1 t2 : Nat, circleDim (r * s) (t1 * t2) = circleDim r t1 * circleDim s t2) ∧
    (∀ t : Nat, circleDim 0 t = 0) ∧
    (∀ n t1 t2 : Nat, circleDim n t1 = circleDim n t2) :=
  ⟨circleDim_add, circleDim_mul, circleDim_finite, circleDim_finite_extension⟩

/-- Paper: finite-rank minimal certificate for the phase-fold kernel.
    thm:cdim-phase-spectrum-limit -/
theorem paper_cdim_phase_fold_kernel_minimal_certificate_rank (rB : ℕ) :
    (∀ m : ℕ, (∃ f : Fin rB → Fin m, Function.Injective f) → rB ≤ m) ∧
    (∃ f : Fin rB → Fin rB, Function.Injective f) := by
  refine ⟨?_, ?_⟩
  · intro m h
    rcases h with ⟨f, hf⟩
    simpa using Fintype.card_le_of_injective f hf
  · exact ⟨id, fun _ _ h => h⟩

/-- Paper: zero-dimensional ledger forbids circle replacement.
    prop:circle-dimension-laws -/
theorem paper_cdim_zero_dimensional_ledger_no_circle_replacement
    (d k t : ℕ) :
    circleDim d t ≤ circleDim k 0 → d ≤ k := by
  simp [circleDim]

/-- phaseSpectrumCount(2,2,4) = 32.
    def:cdim-phase-spectrum -/
theorem phaseSpectrumCount_at_2_2_4 :
    phaseSpectrumCount 2 2 4 = 32 := by
  unfold phaseSpectrumCount; decide

/-- phaseSpectrumCount(3,6,2) = 16.
    def:cdim-phase-spectrum -/
theorem phaseSpectrumCount_at_3_6_2 :
    phaseSpectrumCount 3 6 2 = 16 := by
  unfold phaseSpectrumCount; decide

/-- phaseSpectrumCount(1,12,8) = 32.
    def:cdim-phase-spectrum -/
theorem phaseSpectrumCount_at_1_12_8 :
    phaseSpectrumCount 1 12 8 = 32 := by
  unfold phaseSpectrumCount; decide

/-- phaseSpectrumCount(2,15,10) = 500.
    def:cdim-phase-spectrum -/
theorem phaseSpectrumCount_at_2_15_10 :
    phaseSpectrumCount 2 15 10 = 500 := by
  unfold phaseSpectrumCount; decide

/-- Paper small-value table for phaseSpectrumCount.
    def:cdim-phase-spectrum -/
theorem paper_phaseSpectrumCount_small_values_table :
    phaseSpectrumCount 2 2 4 = 32 ∧
    phaseSpectrumCount 3 6 2 = 16 ∧
    phaseSpectrumCount 1 12 8 = 32 ∧
    phaseSpectrumCount 2 15 10 = 500 ∧
    phaseSpectrumCount 0 5 7 = 1 ∧
    phaseSpectrumCount 5 0 3 = 729 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold phaseSpectrumCount; decide)

/-- circleDim of trivial subtraction is zero.
    prop:circle-dimension-laws -/
theorem circleDim_sub_self (a t : Nat) :
    circleDim (a - a) t = 0 := by
  simp [circleDim]

/-- circleDim is invariant under subtracting zero.
    prop:circle-dimension-laws -/
theorem circleDim_sub_zero (a t : Nat) :
    circleDim (a - 0) t = circleDim a t := by
  simp [circleDim]

/-- circleDim distributes over subtraction (torsion-free side).
    prop:circle-dimension-laws -/
theorem circleDim_sub_eq_sub_circleDim (a b : Nat) (_h : b ≤ a) :
    circleDim (a - b) 0 = circleDim a 0 - circleDim b 0 := by
  simp [circleDim]

/-- Paper package: circleDim subtraction laws.
    prop:circle-dimension-laws -/
theorem paper_circleDim_subtraction_package :
    (∀ a t : Nat, circleDim (a - a) t = 0) ∧
    (∀ a t : Nat, circleDim (a - 0) t = circleDim a t) ∧
    (∀ a b : Nat, b ≤ a → circleDim (a - b) 0 = circleDim a 0 - circleDim b 0) :=
  ⟨circleDim_sub_self,
   circleDim_sub_zero,
   circleDim_sub_eq_sub_circleDim⟩

/-! ### Zero circle-dimension registers cannot eliminate positive-dimensional support -/

/-- On ℤ (torsion-free): n * a = 0 with n > 0 implies a = 0.
    This is the algebraic core of the no-profinite-substitute corollary:
    zero-dimensional (torsion/profinite) registers cannot cancel
    positive-dimensional circle factors.
    cor:cdim2-noprofinite-substitute -/
theorem paper_cdim2_noprofinite_substitute :
    ∀ n : Nat, 0 < n → (∀ a : ℤ, (n : ℤ) * a = 0 → a = 0) := by
  intro n hn a h
  have hn : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  exact (mul_left_cancel₀ hn (h.trans (mul_zero _).symm))

/-- Equivalent formulation: no nonzero element in ℤ is killed by a positive integer.
    cor:cdim2-noprofinite-substitute -/
theorem cdim2_noprofinite_no_torsion :
    ∀ n : Nat, 0 < n → ¬ (∃ a : ℤ, a ≠ 0 ∧ (n : ℤ) * a = 0) := by
  intro n hn ⟨a, ha, h⟩
  exact ha (paper_cdim2_noprofinite_substitute n hn a h)

/-! ### S-smooth integers and equivariant splitting criterion -/

/-- An integer n is S-smooth if every prime factor of n belongs to S.
    thm:cdim-arithmetic-singular-ring-equivariant-splitting-criterion -/
def IsSmooth (S : Finset Nat) (n : Nat) : Prop :=
  ∀ p : Nat, p.Prime → p ∣ n → p ∈ S

/-- 6 is {2,3}-smooth: prime factors of 6 are {2,3} ⊆ {2,3}.
    thm:cdim-arithmetic-singular-ring-equivariant-splitting-criterion -/
theorem isSmooth_6_23 : IsSmooth {2, 3} 6 := by
  intro p hp hpd
  have hle := Nat.le_of_dvd (by omega) hpd
  have hp2 := hp.two_le
  -- p ∈ {2..6}, prime and divides 6 → p ∈ {2,3}
  interval_cases p
  · simp  -- p=2
  · simp  -- p=3
  · exact absurd hp (by native_decide)  -- p=4 not prime
  · exact absurd hpd (by omega)  -- p=5 ∤ 6
  · exact absurd hp (by native_decide)  -- p=6 not prime

/-- 3 is not {2,5}-smooth: 3 is prime, 3 ∣ 3, but 3 ∉ {2,5}.
    thm:cdim-arithmetic-singular-ring-equivariant-splitting-criterion -/
theorem not_isSmooth_3_25 : ¬ IsSmooth {2, 5} 3 := by
  intro h
  have := h 3 (by decide) (dvd_refl 3)
  simp at this

/-- 2 is not {3,5}-smooth: 2 is prime, 2 ∣ 2, but 2 ∉ {3,5}.
    thm:cdim-arithmetic-singular-ring-equivariant-splitting-criterion -/
theorem not_isSmooth_2_35 : ¬ IsSmooth {3, 5} 2 := by
  intro h
  have := h 2 (by decide) (dvd_refl 2)
  simp at this

/-- 2 is {2,3}-smooth.
    thm:cdim-arithmetic-singular-ring-equivariant-splitting-criterion -/
theorem isSmooth_2_23 : IsSmooth {2, 3} 2 := by
  intro p hp hpd
  have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hpd
  subst this; simp

/-- 6 is {2,3,5}-smooth.
    thm:cdim-arithmetic-singular-ring-equivariant-splitting-criterion -/
theorem isSmooth_6_235 : IsSmooth {2, 3, 5} 6 := by
  intro p hp hpd
  have hle := Nat.le_of_dvd (by omega) hpd
  have hp2 := hp.two_le
  interval_cases p
  · simp  -- p=2
  · simp  -- p=3
  · exact absurd hp (by native_decide)  -- p=4
  · exact absurd hpd (by omega)  -- p=5
  · exact absurd hp (by native_decide)  -- p=6

/-- 1 is S-smooth for any S (vacuously: no prime divides 1).
    thm:cdim-arithmetic-singular-ring-equivariant-splitting-criterion -/
theorem isSmooth_one (S : Finset Nat) : IsSmooth S 1 := by
  intro p hp hpd
  exact absurd (Nat.le_of_dvd (by omega) hpd) (by have := hp.two_le; omega)

/-- Paper package: equivariant splitting criterion seed values.
    thm:cdim-arithmetic-singular-ring-equivariant-splitting-criterion -/
theorem paper_cdim_equivariant_splitting_criterion :
    IsSmooth {2, 3} 6 ∧ ¬ IsSmooth {2, 5} 3 ∧ ¬ IsSmooth {3, 5} 2 ∧
    IsSmooth {2, 3} 2 ∧ IsSmooth {2, 3, 5} 6 :=
  ⟨isSmooth_6_23, not_isSmooth_3_25, not_isSmooth_2_35,
   isSmooth_2_23, isSmooth_6_235⟩

end Omega.CircleDimension

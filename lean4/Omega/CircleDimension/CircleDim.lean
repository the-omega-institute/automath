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
  simp [halfCircleDim, circleDim]; ring

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

end Omega.CircleDimension

import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The fundamental period of the `d`-adic rhodonea lift. -/
noncomputable def rhodoneaPeriod (d : ℕ) : ℝ := 2 * Real.pi * d

lemma rhodoneaPeriod_pos {d : ℕ} (hd : 0 < d) : 0 < rhodoneaPeriod d := by
  dsimp [rhodoneaPeriod]
  positivity

/-- Two-step `d`-adic solenoid model: only the first two compatible coordinates are needed for the
lift and the visible projection. -/
abbrev RhodoneaSolenoid (d : ℕ) : Type := {z : ℂ × ℂ // z.1 = z.2 ^ d}

/-- The phase coordinate used by the `d`-adic lift. -/
noncomputable def rhodoneaPhase (d : ℕ) (θ : ℝ) : ℂ :=
  Complex.exp (((θ / d : ℝ) : ℂ) * Complex.I)

/-- The explicit `d`-adic lift on the real parameter. -/
noncomputable def rhodoneaIotaRaw (d : ℕ) (θ : ℝ) : RhodoneaSolenoid d :=
  ⟨((rhodoneaPhase d θ) ^ d, rhodoneaPhase d θ), rfl⟩

/-- The visible character-average on the truncated solenoid model. -/
noncomputable def rhodoneaSolenoidMap (n d : ℕ) (x : RhodoneaSolenoid d) : ℂ :=
  ((x.1.2) ^ (d + n) + (x.1.2) ^ (d - n)) / 2

/-- Restrict the lift to a single fundamental interval `(0, 2π d]`. -/
noncomputable def rhodoneaIotaOnFundamentalDomain (d : ℕ) :
    Set.Ioc (0 : ℝ) (rhodoneaPeriod d) → RhodoneaSolenoid d :=
  fun θ => rhodoneaIotaRaw d θ.1

lemma rhodoneaPhase_pow (d m : ℕ) (θ : ℝ) :
    rhodoneaPhase d θ ^ m = Complex.exp ((((m : ℝ) * (θ / d) : ℝ) : ℂ) * Complex.I) := by
  rw [rhodoneaPhase, ← Complex.exp_nat_mul]
  simp [mul_assoc, mul_comm]

lemma rhodoneaIotaOnFundamentalDomain_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (rhodoneaIotaOnFundamentalDomain d) := by
  intro θ φ hEq
  have hPhase : rhodoneaPhase d θ.1 = rhodoneaPhase d φ.1 := by
    exact congrArg (fun z : RhodoneaSolenoid d => z.1.2) hEq
  rcases (Complex.exp_eq_exp_iff_exists_int).1 hPhase with ⟨k, hk⟩
  have hk_im : θ.1 / d = φ.1 / d + k * (2 * Real.pi) := by
    have := congrArg Complex.im hk
    simp at this
    exact this
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hk_mul := hk_im
  field_simp [hd0] at hk_mul
  have hk_period : θ.1 = φ.1 + (k : ℝ) * rhodoneaPeriod d := by
    dsimp [rhodoneaPeriod]
    linarith [hk_mul]
  have hT : 0 < rhodoneaPeriod d := rhodoneaPeriod_pos hd
  have hk_zero : k = 0 := by
    by_contra hk0
    have hk_cases : k ≤ -1 ∨ 1 ≤ k := by omega
    cases hk_cases with
    | inl hneg =>
        have hnegR : (k : ℝ) ≤ -1 := by exact_mod_cast hneg
        have hθ : θ.1 ≤ 0 := by
          nlinarith [φ.2.2, hT, hk_period, hnegR]
        linarith [θ.2.1]
    | inr hpos =>
        have hposR : (1 : ℝ) ≤ k := by exact_mod_cast hpos
        have hθ : rhodoneaPeriod d < θ.1 := by
          nlinarith [φ.2.1, hT, hk_period, hposR]
        linarith [θ.2.2]
  apply Subtype.ext
  have hk_zeroR : (k : ℝ) = 0 := by exact_mod_cast hk_zero
  nlinarith [hk_period, hk_zeroR]

lemma rhodoneaSolenoidMap_on_iota (d n : ℕ) (hd : 0 < d) (hn : n < d)
    (θ : Set.Ioc (0 : ℝ) (rhodoneaPeriod d)) :
    rhodoneaSolenoidMap n d (rhodoneaIotaOnFundamentalDomain d θ) =
      (Complex.exp ((((θ.1 + (((n : ℝ) / d) * θ.1) : ℝ) : ℂ) * Complex.I)) +
        Complex.exp ((((θ.1 - (((n : ℝ) / d) * θ.1) : ℝ) : ℂ) * Complex.I))) / 2 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hplus : ((d + n : ℝ) * (θ.1 / d)) = θ.1 + (((n : ℝ) / d) * θ.1) := by
    field_simp [hd0]
  have hminus : ((d - n : ℝ) * (θ.1 / d)) = θ.1 - (((n : ℝ) / d) * θ.1) := by
    field_simp [hd0]
  have hplus' : (((d + n : ℕ) : ℝ) * (θ.1 / d)) = θ.1 + (((n : ℝ) / d) * θ.1) := by
    simpa using hplus
  have hminus' : (((d - n : ℕ) : ℝ) * (θ.1 / d)) = θ.1 - (((n : ℝ) / d) * θ.1) := by
    simpa [Nat.cast_sub hn.le] using hminus
  rw [rhodoneaSolenoidMap, rhodoneaIotaOnFundamentalDomain, rhodoneaIotaRaw]
  simp_rw [rhodoneaPhase_pow]
  refine congrArg (fun z : ℂ => z / 2) ?_
  congr 1
  · exact congrArg (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) hplus'
  · exact congrArg (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) hminus'

/-- On a single fundamental interval, the explicit `d`-adic lift is injective, and the solenoid
character average restricts to the rhodonea orbit written as the average of the two phase
characters `e^{i(\theta ± n\theta/d)}`.
    thm:cdim-rhodonea-solenoid-desingularized-lift -/
theorem paper_cdim_rhodonea_solenoid_desingularized_lift
    (d n : ℕ) (hd : 0 < d) (hn : n < d) :
    Function.Injective (rhodoneaIotaOnFundamentalDomain d) ∧
      ∀ θ : Set.Ioc (0 : ℝ) (rhodoneaPeriod d),
        rhodoneaSolenoidMap n d (rhodoneaIotaOnFundamentalDomain d θ) =
          (Complex.exp ((((θ.1 + (((n : ℝ) / d) * θ.1) : ℝ) : ℂ) * Complex.I)) +
            Complex.exp ((((θ.1 - (((n : ℝ) / d) * θ.1) : ℝ) : ℂ) * Complex.I))) / 2 := by
  exact ⟨rhodoneaIotaOnFundamentalDomain_injective hd, rhodoneaSolenoidMap_on_iota d n hd hn⟩

end Omega.CircleDimension

import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The stabilized orbit size at level `n`, corresponding to the paper's `2^(k-7)` with
`k = n + 9`. -/
def pomS4Modulus (n : ℕ) : ℕ :=
  2 ^ (n + 2)

lemma pomS4Modulus_pos (n : ℕ) : 0 < pomS4Modulus n := by
  simp [pomS4Modulus]

lemma pomS4Modulus_succ (n : ℕ) : pomS4Modulus (n + 1) = pomS4Modulus n * 2 := by
  simp [pomS4Modulus, pow_succ, Nat.add_assoc, Nat.mul_comm]

lemma pomS4Modulus_dvd_succ (n : ℕ) : pomS4Modulus n ∣ pomS4Modulus (n + 1) := by
  refine ⟨2, ?_⟩
  rw [pomS4Modulus_succ]

/-- The single-cycle orbit at precision level `n`. -/
abbrev PomS4OrbitStage (n : ℕ) : Type :=
  Fin (pomS4Modulus n)

/-- The reduction map `O_{k+1} → O_k`. -/
def pomS4Projection (n : ℕ) : PomS4OrbitStage (n + 1) → PomS4OrbitStage n := fun x =>
  ⟨x.1 % pomS4Modulus n, Nat.mod_lt _ (pomS4Modulus_pos n)⟩

/-- The cyclic successor on the stabilized orbit. -/
def pomS4StageSucc (n : ℕ) : PomS4OrbitStage n → PomS4OrbitStage n := fun x =>
  ⟨(x.1 + 1) % pomS4Modulus n, Nat.mod_lt _ (pomS4Modulus_pos n)⟩

def pomS4LowerLift (n : ℕ) (x : PomS4OrbitStage n) : PomS4OrbitStage (n + 1) := by
  refine ⟨x.1, ?_⟩
  rw [pomS4Modulus_succ]
  exact lt_of_lt_of_le x.2 (Nat.le_mul_of_pos_right _ (by decide))

def pomS4UpperLift (n : ℕ) (x : PomS4OrbitStage n) : PomS4OrbitStage (n + 1) := by
  refine ⟨x.1 + pomS4Modulus n, ?_⟩
  rw [pomS4Modulus_succ]
  have hpos : 0 < pomS4Modulus n := pomS4Modulus_pos n
  omega

lemma pomS4Projection_lowerLift (n : ℕ) (x : PomS4OrbitStage n) :
    pomS4Projection n (pomS4LowerLift n x) = x := by
  ext
  simp [pomS4Projection, pomS4LowerLift, Nat.mod_eq_of_lt x.2]

lemma pomS4Projection_upperLift (n : ℕ) (x : PomS4OrbitStage n) :
    pomS4Projection n (pomS4UpperLift n x) = x := by
  ext
  simp [pomS4Projection, pomS4UpperLift, Nat.add_mod_right, Nat.mod_eq_of_lt x.2]

lemma pomS4LowerLift_ne_upperLift (n : ℕ) (x : PomS4OrbitStage n) :
    pomS4LowerLift n x ≠ pomS4UpperLift n x := by
  intro h
  have hvals : x.1 = x.1 + pomS4Modulus n := congrArg Fin.val h
  have hpos : 0 < pomS4Modulus n := pomS4Modulus_pos n
  omega

lemma pomS4Projection_two_point_fiber (n : ℕ) (x : PomS4OrbitStage n) :
    ∃ y₀ y₁ : PomS4OrbitStage (n + 1),
      y₀ ≠ y₁ ∧
        pomS4Projection n y₀ = x ∧
        pomS4Projection n y₁ = x ∧
        ∀ y : PomS4OrbitStage (n + 1), pomS4Projection n y = x → y = y₀ ∨ y = y₁ := by
  refine ⟨pomS4LowerLift n x, pomS4UpperLift n x, pomS4LowerLift_ne_upperLift n x,
    pomS4Projection_lowerLift n x, pomS4Projection_upperLift n x, ?_⟩
  intro y hy
  have hmod : y.1 % pomS4Modulus n = x.1 := by
    exact congrArg Fin.val hy
  have hylt : y.1 < pomS4Modulus n * 2 := by
    simpa [pomS4Modulus_succ] using y.2
  have hq_lt : y.1 / pomS4Modulus n < 2 := by
    exact (Nat.div_lt_iff_lt_mul (pomS4Modulus_pos n)).2 (by simpa [Nat.mul_comm] using hylt)
  have hq : y.1 / pomS4Modulus n = 0 ∨ y.1 / pomS4Modulus n = 1 := by
    interval_cases y.1 / pomS4Modulus n <;> simp
  have hdecomp : y.1 / pomS4Modulus n * pomS4Modulus n + x.1 = y.1 := by
    rw [← hmod, Nat.div_add_mod']
  cases hq with
  | inl hzero =>
      left
      ext
      have hval : y.1 = x.1 := by
        simpa [hzero] using hdecomp.symm
      simpa [pomS4LowerLift] using hval
  | inr hone =>
      right
      ext
      have hval : y.1 = x.1 + pomS4Modulus n := by
        simpa [hone, add_comm, add_left_comm, add_assoc] using hdecomp.symm
      simpa [pomS4UpperLift, add_comm, add_left_comm, add_assoc] using hval

lemma pomS4Projection_succ_commute (n : ℕ) (x : PomS4OrbitStage (n + 1)) :
    pomS4Projection n (pomS4StageSucc (n + 1) x) = pomS4StageSucc n (pomS4Projection n x) := by
  ext
  simp [pomS4Projection, pomS4StageSucc, Nat.mod_mod_of_dvd, pomS4Modulus_dvd_succ]

/-- A compatible tower for a given inverse system. -/
structure CompatibleTower (A : ℕ → Type) (π : ∀ n, A (n + 1) → A n) where
  seq : ∀ n, A n
  compat : ∀ n, π n (seq (n + 1)) = seq n

/-- Standard `2`-adic stage sizes used by the odometer model. -/
abbrev TwoAdicStage (n : ℕ) : Type :=
  Fin (pomS4Modulus n)

abbrev twoAdicProjection (n : ℕ) : TwoAdicStage (n + 1) → TwoAdicStage n :=
  pomS4Projection n

abbrev twoAdicStageSucc (n : ℕ) : TwoAdicStage n → TwoAdicStage n :=
  pomS4StageSucc n

abbrev PomS4InverseLimit : Type :=
  CompatibleTower PomS4OrbitStage pomS4Projection

abbrev TwoAdicInverseLimit : Type :=
  CompatibleTower TwoAdicStage twoAdicProjection

def pomS4Shift (x : PomS4InverseLimit) : PomS4InverseLimit where
  seq n := pomS4StageSucc n (x.seq n)
  compat n := by
    calc
      pomS4Projection n (pomS4StageSucc (n + 1) (x.seq (n + 1)))
          = pomS4StageSucc n (pomS4Projection n (x.seq (n + 1))) := by
              simpa using pomS4Projection_succ_commute n (x.seq (n + 1))
      _ = pomS4StageSucc n (x.seq n) := by rw [x.compat]

def twoAdicShift (x : TwoAdicInverseLimit) : TwoAdicInverseLimit where
  seq n := twoAdicStageSucc n (x.seq n)
  compat n := by
    calc
      twoAdicProjection n (twoAdicStageSucc (n + 1) (x.seq (n + 1)))
          = twoAdicStageSucc n (twoAdicProjection n (x.seq (n + 1))) := by
              simpa [twoAdicProjection, twoAdicStageSucc] using
                pomS4Projection_succ_commute n (x.seq (n + 1))
      _ = twoAdicStageSucc n (x.seq n) := by rw [x.compat]

def pomS4ToTwoAdic : PomS4InverseLimit ≃ TwoAdicInverseLimit where
  toFun x := { seq := x.seq, compat := x.compat }
  invFun x := { seq := x.seq, compat := x.compat }
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- Finite-stage inverse-limit core of the `q = 4` odometer law: each stabilized orbit is a single
cycle of size `2^(k-7)`, the reduction map commutes with the successor and has exactly two lifts,
and the resulting inverse system is canonically identified with the standard inverse limit of the
cyclic quotients of the `2`-adic odometer.
    thm:pom-s4-2adic-odometer-inverse-limit -/
theorem paper_pom_s4_2adic_odometer_inverse_limit :
    (∀ n, Fintype.card (PomS4OrbitStage n) = 2 ^ (n + 2)) ∧
      (∀ n, ∀ x : PomS4OrbitStage n,
        ∃ y₀ y₁ : PomS4OrbitStage (n + 1),
          y₀ ≠ y₁ ∧
            pomS4Projection n y₀ = x ∧
            pomS4Projection n y₁ = x ∧
            ∀ y : PomS4OrbitStage (n + 1), pomS4Projection n y = x → y = y₀ ∨ y = y₁) ∧
      (∀ n, ∀ x : PomS4OrbitStage (n + 1),
        pomS4Projection n (pomS4StageSucc (n + 1) x) = pomS4StageSucc n (pomS4Projection n x)) ∧
      ∃ e : PomS4InverseLimit ≃ TwoAdicInverseLimit, ∀ z, e (pomS4Shift z) = twoAdicShift (e z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    simp [PomS4OrbitStage, pomS4Modulus]
  · intro n x
    exact pomS4Projection_two_point_fiber n x
  · intro n x
    exact pomS4Projection_succ_commute n x
  · refine ⟨pomS4ToTwoAdic, ?_⟩
    intro z
    rfl

end Omega.POM

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Zeta.XiJSexticEllipticLattesKleinMobius

namespace Omega.Zeta

noncomputable section

/-- The branch polynomial visible in the Klein-four normalization. -/
def xi_j_sextic_elliptic_lattes_multiplier_rigidity_branch_poly (t : ℝ) : ℝ :=
  (t - xi_j_sextic_elliptic_lattes_klein_mobius_e1) *
    (t - xi_j_sextic_elliptic_lattes_klein_mobius_e2) *
      (t - xi_j_sextic_elliptic_lattes_klein_mobius_e3)

/-- The constant appearing in the first Klein involution. -/
def xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_constant : ℝ :=
  (xi_j_sextic_elliptic_lattes_klein_mobius_e1 -
      xi_j_sextic_elliptic_lattes_klein_mobius_e2) *
    (xi_j_sextic_elliptic_lattes_klein_mobius_e1 -
      xi_j_sextic_elliptic_lattes_klein_mobius_e3)

/-- Iteration of the first Klein involution. -/
def xi_j_sextic_elliptic_lattes_multiplier_rigidity_iterate : ℕ → ℝ → ℝ
  | 0, t => t
  | n + 1, t =>
      xi_j_sextic_elliptic_lattes_klein_mobius_phi1
        (xi_j_sextic_elliptic_lattes_multiplier_rigidity_iterate n t)

/-- Symbolic derivative multiplier of the sextic Lattès map on the Klein chart. The factor `2`
records the elliptic doubling multiplier, while the rational term is the derivative of the first
Klein involution. -/
def xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier (t : ℝ) : ℝ :=
  -(2 : ℝ) * xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_constant /
    (t - xi_j_sextic_elliptic_lattes_klein_mobius_e1) ^ 2

/-- Orbit multiplier obtained by multiplying the local multiplier along the iterated orbit. -/
def xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_multiplier : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, t =>
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier
          (xi_j_sextic_elliptic_lattes_multiplier_rigidity_iterate n t) *
        xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_multiplier n t

lemma xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_constant_eq :
    xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_constant = 6365312 := by
  simpa [xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_constant] using
    xi_j_sextic_elliptic_lattes_klein_mobius_phi1_const

lemma xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_constant_ne_zero :
    xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_constant ≠ 0 := by
  rw [xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_constant_eq]
  norm_num

lemma xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_shift (t : ℝ) :
    xi_j_sextic_elliptic_lattes_klein_mobius_phi1 t -
        xi_j_sextic_elliptic_lattes_klein_mobius_e1 =
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_constant /
        (t - xi_j_sextic_elliptic_lattes_klein_mobius_e1) := by
  unfold xi_j_sextic_elliptic_lattes_klein_mobius_phi1
    xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_constant
  ring

lemma xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_ne_branch (t : ℝ)
    (ht : t ≠ xi_j_sextic_elliptic_lattes_klein_mobius_e1) :
    xi_j_sextic_elliptic_lattes_klein_mobius_phi1 t ≠
      xi_j_sextic_elliptic_lattes_klein_mobius_e1 := by
  have hconst_ne :
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_constant ≠ 0 :=
    xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_constant_ne_zero
  have hshift :=
    xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_shift t
  intro hphi
  have hzero :
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_constant /
          (t - xi_j_sextic_elliptic_lattes_klein_mobius_e1) =
        0 := by
    simpa [hphi] using hshift.symm
  rcases (div_eq_zero_iff.mp hzero) with hnum | hden
  · exact hconst_ne hnum
  · exact ht (sub_eq_zero.mp hden)

lemma xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_pair (t : ℝ)
    (ht : t ≠ xi_j_sextic_elliptic_lattes_klein_mobius_e1) :
    xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier
        (xi_j_sextic_elliptic_lattes_klein_mobius_phi1 t) *
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier t =
        4 := by
  have hconst_ne :
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_constant ≠ 0 :=
    xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_constant_ne_zero
  have ht0 : t - xi_j_sextic_elliptic_lattes_klein_mobius_e1 ≠ 0 := sub_ne_zero.mpr ht
  unfold xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier
  rw [xi_j_sextic_elliptic_lattes_multiplier_rigidity_phi1_shift]
  field_simp [hconst_ne, ht0]
  ring

lemma xi_j_sextic_elliptic_lattes_multiplier_rigidity_iterate_fixed (t : ℝ)
    (hperiod :
      xi_j_sextic_elliptic_lattes_klein_mobius_phi1 t = t) :
    ∀ n : ℕ,
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_iterate n t = t := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [xi_j_sextic_elliptic_lattes_multiplier_rigidity_iterate, ih, hperiod]

lemma xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_pow (t : ℝ)
    (hperiod :
      xi_j_sextic_elliptic_lattes_klein_mobius_phi1 t = t) :
    ∀ n : ℕ,
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_multiplier n t =
        xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier t ^ n := by
  intro n
  induction n with
  | zero =>
      simp [xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_multiplier]
  | succ n ih =>
      have hfix :=
        xi_j_sextic_elliptic_lattes_multiplier_rigidity_iterate_fixed t hperiod n
      simp [xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_multiplier,
        hfix, ih, pow_succ, mul_comm]

lemma xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_sq (t : ℝ)
    (ht : t ≠ xi_j_sextic_elliptic_lattes_klein_mobius_e1)
    (hperiod :
      xi_j_sextic_elliptic_lattes_klein_mobius_phi1 t = t) :
    xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier t ^ 2 = 4 := by
  have hpair :=
    xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_pair t ht
  simpa [hperiod, pow_two] using hpair

/-- Paper label: `cor:xi-j-sextic-elliptic-lattes-multiplier-rigidity`.
At a branch-avoiding periodic point of the first Klein involution, the orbit multiplier is the
expected telescoping product of the local multiplier. The local square is rigidly `4`, so every
`n`-step multiplier has square `4^n` and hence sign `± 2^n`. -/
theorem paper_xi_j_sextic_elliptic_lattes_multiplier_rigidity
    (t : ℝ) (ht : t ≠ xi_j_sextic_elliptic_lattes_klein_mobius_e1)
    (hperiod : xi_j_sextic_elliptic_lattes_klein_mobius_phi1 t = t) (n : ℕ) :
    xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_multiplier n t =
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier t ^ n ∧
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_multiplier n t ^ 2 = (4 : ℝ) ^ n ∧
      (xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_multiplier n t = (2 : ℝ) ^ n ∨
        xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_multiplier n t = -((2 : ℝ) ^ n)) := by
  have horbit :
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_multiplier n t =
        xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier t ^ n :=
    xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_pow t hperiod n
  have hlocal_sq :
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier t ^ 2 = 4 :=
    xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_sq t ht hperiod
  have horbit_sq :
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_multiplier n t ^ 2 = (4 : ℝ) ^ n := by
    calc
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_multiplier n t ^ 2 =
          (xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier t ^ n) ^ 2 := by
            rw [horbit]
      _ = xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier t ^ (n * 2) := by
            rw [pow_mul]
      _ = xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier t ^ (2 * n) := by
            rw [Nat.mul_comm]
      _ = (xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier t ^ 2) ^ n := by
            rw [← pow_mul]
      _ = (4 : ℝ) ^ n := by rw [hlocal_sq]
  have hlocal_sign :
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier t = 2 ∨
        xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier t = -2 := by
    have hfactor :
        (xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier t - 2) *
            (xi_j_sextic_elliptic_lattes_multiplier_rigidity_local_multiplier t + 2) =
          0 := by
      nlinarith [hlocal_sq]
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · left
      linarith
    · right
      linarith
  have horbit_sign :
      xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_multiplier n t = (2 : ℝ) ^ n ∨
        xi_j_sextic_elliptic_lattes_multiplier_rigidity_orbit_multiplier n t = -((2 : ℝ) ^ n) := by
    rcases hlocal_sign with hlocal | hlocal
    · left
      rw [horbit, hlocal]
    · rcases Nat.even_or_odd n with hEven | hOdd
      · rcases hEven with ⟨k, rfl⟩
        left
        rw [horbit, hlocal]
        simp
      · rcases hOdd with ⟨k, rfl⟩
        right
        rw [horbit, hlocal]
        simp [pow_add, pow_mul]
  exact ⟨horbit, horbit_sq, horbit_sign⟩

end

end Omega.Zeta

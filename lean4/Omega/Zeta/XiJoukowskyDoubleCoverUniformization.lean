import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The Joukowsky map on `ℂˣ`, written on all of `ℂ` and used only at nonzero points below. -/
noncomputable def xi_joukowsky_double_cover_uniformization_J (z : ℂ) : ℂ :=
  z + z⁻¹

/-- Discriminant of the quadratic equation `z^2 - wz + 1 = 0`. -/
noncomputable def xi_joukowsky_double_cover_uniformization_discriminant (w : ℂ) : ℂ :=
  w ^ 2 - 4

/-- A chosen square root of the discriminant, available because `ℂ` is algebraically closed. -/
noncomputable def xi_joukowsky_double_cover_uniformization_sqrt (w : ℂ) : ℂ :=
  Classical.choose
    (IsAlgClosed.exists_pow_nat_eq
      (xi_joukowsky_double_cover_uniformization_discriminant w) (n := 2) zero_lt_two)

lemma xi_joukowsky_double_cover_uniformization_sqrt_sq (w : ℂ) :
    xi_joukowsky_double_cover_uniformization_sqrt w ^ 2 =
      xi_joukowsky_double_cover_uniformization_discriminant w := by
  exact Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq
      (xi_joukowsky_double_cover_uniformization_discriminant w) (n := 2) zero_lt_two)

/-- The `+` branch of the explicit quadratic solution. -/
noncomputable def xi_joukowsky_double_cover_uniformization_root_plus (w : ℂ) : ℂ :=
  (w + xi_joukowsky_double_cover_uniformization_sqrt w) / 2

/-- The `-` branch of the explicit quadratic solution. -/
noncomputable def xi_joukowsky_double_cover_uniformization_root_minus (w : ℂ) : ℂ :=
  (w - xi_joukowsky_double_cover_uniformization_sqrt w) / 2

/-- Joukowsky double-cover package: the quadratic `z^2 - wz + 1 = 0` has the explicit two roots,
the discriminant vanishes exactly at `w = ±2`, and the deck involution is inversion because the
two roots multiply to `1`. -/
def xi_joukowsky_double_cover_uniformization_statement : Prop :=
  ∀ w : ℂ,
    let z₁ := xi_joukowsky_double_cover_uniformization_root_plus w
    let z₂ := xi_joukowsky_double_cover_uniformization_root_minus w
    z₁ ^ 2 - w * z₁ + 1 = 0 ∧
    z₂ ^ 2 - w * z₂ + 1 = 0 ∧
    z₁ + z₂ = w ∧
    z₁ * z₂ = 1 ∧
    (xi_joukowsky_double_cover_uniformization_discriminant w = 0 ↔
      w = 2 ∨ w = -2) ∧
    z₁ ≠ 0 ∧
    z₂ ≠ 0 ∧
    xi_joukowsky_double_cover_uniformization_J z₁ = w ∧
    xi_joukowsky_double_cover_uniformization_J z₂ = w ∧
    z₂ = z₁⁻¹

/-- Paper label: `prop:xi-joukowsky-double-cover-uniformization`. The two explicit quadratic
branches uniformize the Joukowsky cover away from the branch points `±2`, and the nontrivial deck
transformation is inversion. -/
theorem paper_xi_joukowsky_double_cover_uniformization :
    xi_joukowsky_double_cover_uniformization_statement := by
  intro w
  let Δ : ℂ := xi_joukowsky_double_cover_uniformization_discriminant w
  let s : ℂ := xi_joukowsky_double_cover_uniformization_sqrt w
  let z₁ : ℂ := xi_joukowsky_double_cover_uniformization_root_plus w
  let z₂ : ℂ := xi_joukowsky_double_cover_uniformization_root_minus w
  have hs : s ^ 2 = Δ := by
    simpa [s, Δ] using xi_joukowsky_double_cover_uniformization_sqrt_sq w
  have hz₁_root_aux : ((w + s) / 2) ^ 2 - w * ((w + s) / 2) + 1 = 0 := by
    calc
      ((w + s) / 2) ^ 2 - w * ((w + s) / 2) + 1 = (s ^ 2 - w ^ 2 + 4) / 4 := by ring
      _ = 0 := by rw [hs]; simp [Δ, xi_joukowsky_double_cover_uniformization_discriminant]
  have hz₂_root_aux : ((w - s) / 2) ^ 2 - w * ((w - s) / 2) + 1 = 0 := by
    calc
      ((w - s) / 2) ^ 2 - w * ((w - s) / 2) + 1 = (s ^ 2 - w ^ 2 + 4) / 4 := by ring
      _ = 0 := by rw [hs]; simp [Δ, xi_joukowsky_double_cover_uniformization_discriminant]
  have hsum_aux : ((w + s) / 2) + ((w - s) / 2) = w := by
    ring
  have hprod_aux : ((w + s) / 2) * ((w - s) / 2) = 1 := by
    calc
      ((w + s) / 2) * ((w - s) / 2) = (w ^ 2 - s ^ 2) / 4 := by ring
      _ = 1 := by rw [hs]; simp [Δ, xi_joukowsky_double_cover_uniformization_discriminant]
  have hz₁_root : z₁ ^ 2 - w * z₁ + 1 = 0 := by
    simpa [z₁, s, xi_joukowsky_double_cover_uniformization_root_plus] using hz₁_root_aux
  have hz₂_root : z₂ ^ 2 - w * z₂ + 1 = 0 := by
    simpa [z₂, s, xi_joukowsky_double_cover_uniformization_root_minus] using hz₂_root_aux
  have hsum : z₁ + z₂ = w := by
    simpa [z₁, z₂, s, xi_joukowsky_double_cover_uniformization_root_plus,
      xi_joukowsky_double_cover_uniformization_root_minus] using hsum_aux
  have hprod : z₁ * z₂ = 1 := by
    simpa [z₁, z₂, s, xi_joukowsky_double_cover_uniformization_root_plus,
      xi_joukowsky_double_cover_uniformization_root_minus] using hprod_aux
  have hbranch :
      xi_joukowsky_double_cover_uniformization_discriminant w = 0 ↔ w = 2 ∨ w = -2 := by
    constructor
    · intro hΔ
      have hmul : (w - 2) * (w + 2) = 0 := by
        have : w ^ 2 - 4 = (w - 2) * (w + 2) := by ring
        simpa [Δ, xi_joukowsky_double_cover_uniformization_discriminant, this] using hΔ
      rcases mul_eq_zero.mp hmul with hw | hw
      · exact Or.inl <| sub_eq_zero.mp hw
      · exact Or.inr <| eq_neg_of_add_eq_zero_left hw
    · rintro (rfl | rfl) <;>
        norm_num [xi_joukowsky_double_cover_uniformization_discriminant]
  have hz₁_ne : z₁ ≠ 0 := by
    intro hz₁_zero
    simp [hz₁_zero] at hprod
  have hz₂_ne : z₂ ≠ 0 := by
    intro hz₂_zero
    simp [hz₂_zero] at hprod
  have hz₂_inv : z₂ = z₁⁻¹ := by
    calc
      z₂ = 1 * z₂ := by simp
      _ = (z₁⁻¹ * z₁) * z₂ := by simp [hz₁_ne]
      _ = z₁⁻¹ * (z₁ * z₂) := by ring
      _ = z₁⁻¹ * 1 := by rw [hprod]
      _ = z₁⁻¹ := by simp
  have hz₁_inv : z₁ = z₂⁻¹ := by
    calc
      z₁ = z₁ * 1 := by simp
      _ = z₁ * (z₂ * z₂⁻¹) := by simp [hz₂_ne]
      _ = (z₁ * z₂) * z₂⁻¹ := by ring
      _ = 1 * z₂⁻¹ := by rw [hprod]
      _ = z₂⁻¹ := by simp
  have hJ₁ : xi_joukowsky_double_cover_uniformization_J z₁ = w := by
    calc
      xi_joukowsky_double_cover_uniformization_J z₁ = z₁ + z₁⁻¹ := by
        simp [xi_joukowsky_double_cover_uniformization_J]
      _ = z₁ + z₂ := by rw [← hz₂_inv]
      _ = w := hsum
  have hJ₂ : xi_joukowsky_double_cover_uniformization_J z₂ = w := by
    calc
      xi_joukowsky_double_cover_uniformization_J z₂ = z₂ + z₂⁻¹ := by
        simp [xi_joukowsky_double_cover_uniformization_J]
      _ = z₂ + z₁ := by rw [← hz₁_inv]
      _ = w := by simpa [add_comm] using hsum
  exact ⟨hz₁_root, hz₂_root, hsum, hprod, hbranch, hz₁_ne, hz₂_ne, hJ₁, hJ₂, hz₂_inv⟩

end Omega.Zeta

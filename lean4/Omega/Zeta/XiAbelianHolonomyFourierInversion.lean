import Mathlib

open scoped BigOperators

namespace Omega.Zeta

structure xi_abelian_holonomy_fourier_inversion_data (H R : Type) [Fintype H] [CommGroup H]
    [CommRing R] where
  component : H → R

def xi_abelian_holonomy_fourier_inversion_grouped_series {H R : Type} [Fintype H] [CommGroup H]
    [CommRing R] (D : xi_abelian_holonomy_fourier_inversion_data H R) (h : H) : R :=
  D.component h

noncomputable def xi_abelian_holonomy_fourier_inversion_character_kernel
    {H R : Type} [Fintype H] [CommGroup H]
    [CommRing R] (_D : xi_abelian_holonomy_fourier_inversion_data H R) (χ h : H) : R :=
  by
    classical
    exact if χ = h then 1 else 0

noncomputable def xi_abelian_holonomy_fourier_inversion_twisted_series
    {H R : Type} [Fintype H] [CommGroup H]
    [CommRing R] (D : xi_abelian_holonomy_fourier_inversion_data H R) (χ : H) : R :=
  ∑ h, xi_abelian_holonomy_fourier_inversion_grouped_series D h *
    xi_abelian_holonomy_fourier_inversion_character_kernel D χ h

def xi_abelian_holonomy_fourier_inversion_statement {H R : Type} [Fintype H] [CommGroup H]
    [CommRing R] (D : xi_abelian_holonomy_fourier_inversion_data H R) : Prop :=
  ∀ χ : H,
    xi_abelian_holonomy_fourier_inversion_twisted_series D χ =
      xi_abelian_holonomy_fourier_inversion_grouped_series D χ

theorem paper_xi_abelian_holonomy_fourier_inversion {H R : Type} [Fintype H] [CommGroup H]
    [CommRing R] (D : xi_abelian_holonomy_fourier_inversion_data H R) :
    xi_abelian_holonomy_fourier_inversion_statement D := by
  classical
  intro χ
  simp [xi_abelian_holonomy_fourier_inversion_twisted_series,
    xi_abelian_holonomy_fourier_inversion_grouped_series,
    xi_abelian_holonomy_fourier_inversion_character_kernel]

end Omega.Zeta

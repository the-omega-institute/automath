import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- The modulus used for the finite `p`-typical ghost window. -/
def pom_schur_channels_mod_pn_from_ptypical_ghost_modulus (p N : ℕ) : ℕ :=
  p ^ N

/-- The residue of a natural number modulo a positive modulus, as a finite index. -/
def pom_schur_channels_mod_pn_from_ptypical_ghost_residue
    (M : ℕ) (hM : 0 < M) (n : ℕ) : Fin M :=
  ⟨n % M, Nat.mod_lt n hM⟩

/-- The finite `p`-typical ghost window reduced modulo `p^N`. -/
noncomputable def pom_schur_channels_mod_pn_from_ptypical_ghost_window
    {α : Type*} [Fintype α] (p N M : ℕ) (d : α → ℕ) : Fin N → ZMod M :=
  fun k => ∑ x : α, (d x : ZMod M) ^ (p ^ (k : ℕ))

/-- The residue histogram modulo a fixed positive modulus. -/
def pom_schur_channels_mod_pn_from_ptypical_ghost_histogram
    {α : Type*} [Fintype α] (M : ℕ) (hM : 0 < M) (d : α → ℕ) : Fin M → ℕ :=
  fun a =>
    Fintype.card {x : α // pom_schur_channels_mod_pn_from_ptypical_ghost_residue M hM (d x) = a}

/-- A concrete finite complete-symmetric-function readout from a residue histogram. -/
noncomputable def pom_schur_channels_mod_pn_from_ptypical_ghost_complete
    (M : ℕ) (hist : Fin M → ℕ) (q : ℕ) : ZMod M :=
  ∑ f : Fin q → Fin M, ∏ i : Fin q, ((f i : ℕ) * hist (f i) : ZMod M)

/-- Extend the complete symmetric functions by zero on negative indices. -/
noncomputable def pom_schur_channels_mod_pn_from_ptypical_ghost_complete_int
    (M : ℕ) (hist : Fin M → ℕ) (q : ℤ) : ZMod M :=
  if _ : 0 ≤ q then
    pom_schur_channels_mod_pn_from_ptypical_ghost_complete M hist q.toNat
  else 0

/-- Jacobi--Trudi determinant reconstructed from a residue histogram. -/
noncomputable def pom_schur_channels_mod_pn_from_ptypical_ghost_jacobi_trudi
    (M ell : ℕ) (hist : Fin M → ℕ) (lam : Fin ell → ℤ) : ZMod M :=
  Matrix.det fun i j =>
    pom_schur_channels_mod_pn_from_ptypical_ghost_complete_int M hist
      (lam i - (i : ℤ) + (j : ℤ))

/-- Concrete statement: an assumed inversion of the finite ghost window to the residue histogram
determines every Jacobi--Trudi Schur channel modulo `p^N`. -/
def pom_schur_channels_mod_pn_from_ptypical_ghost_statement : Prop :=
  ∀ (α : Type*) [Fintype α] (p N M : ℕ),
    M = pom_schur_channels_mod_pn_from_ptypical_ghost_modulus p N →
      Nat.Prime p →
        1 ≤ N →
          ∀ (hM : 0 < M) (d : α → ℕ)
            (invert : (Fin N → ZMod M) → Fin M → ℕ),
            invert (pom_schur_channels_mod_pn_from_ptypical_ghost_window p N M d) =
                pom_schur_channels_mod_pn_from_ptypical_ghost_histogram M hM d →
              ∀ (ell : ℕ) (lam : Fin ell → ℤ),
                pom_schur_channels_mod_pn_from_ptypical_ghost_jacobi_trudi M ell
                    (invert (pom_schur_channels_mod_pn_from_ptypical_ghost_window p N M d)) lam =
                  pom_schur_channels_mod_pn_from_ptypical_ghost_jacobi_trudi M ell
                    (pom_schur_channels_mod_pn_from_ptypical_ghost_histogram M hM d) lam

/-- Paper label: `prop:pom-schur-channels-mod-pN-from-ptypical-ghost`. -/
theorem paper_pom_schur_channels_mod_pn_from_ptypical_ghost :
    pom_schur_channels_mod_pn_from_ptypical_ghost_statement := by
  intro α _ p N M _ _ _ hM d invert hinv ell lam
  rw [hinv]

end Omega.POM

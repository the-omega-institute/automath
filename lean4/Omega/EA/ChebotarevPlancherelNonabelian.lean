import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.EA

open scoped BigOperators

noncomputable section

/-- The character-channel amplitude of a class function. -/
def chebotarevCharacterAmplitude
    {G Ρ : Type*} [Fintype G] [Fintype Ρ]
    (ε : G → ℂ) (χ : Ρ → G → ℂ) (ρ : Ρ) : ℂ :=
  ∑ g, ε g * star (χ ρ g)

/-- The fiber of a quotient map over `h`. -/
def chebotarevFiber
    {G H : Type*} [Fintype G] [DecidableEq G] [DecidableEq H]
    (φ : G → H) (h : H) : Finset G :=
  Finset.univ.filter fun g => φ g = h

/-- Fiber averaging along a quotient map with constant fiber size `k`. -/
def chebotarevFiberAverage
    {G H : Type*} [Fintype G] [DecidableEq G] [DecidableEq H]
    (φ : G → H) (k : ℕ) (ε : G → ℂ) (h : H) : ℂ :=
  (1 / (k : ℂ)) * Finset.sum (chebotarevFiber φ h) ε

private theorem chebotarevFiber_sum_norm_sq
    {G H : Type*} [Fintype G] [DecidableEq G] [DecidableEq H]
    (φ : G → H) (k : ℕ) (ε : G → ℂ) (hk : 0 < k)
    (hfiber : ∀ h : H, (chebotarevFiber φ h).card = k) :
    ∀ h : H,
      ‖chebotarevFiberAverage φ k ε h‖ ^ 2 ≤
        (1 / (k : ℝ)) * Finset.sum (chebotarevFiber φ h) (fun g => ‖ε g‖ ^ 2) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkR_ne : (k : ℝ) ≠ 0 := hkR.ne'
  intro h
  have hnorm :
      ‖Finset.sum (chebotarevFiber φ h) ε‖ ≤
        Finset.sum (chebotarevFiber φ h) (fun g => ‖ε g‖) := by
    exact norm_sum_le _ _
  have hsquare :
      (Finset.sum (chebotarevFiber φ h) fun g => ‖ε g‖) ^ 2 ≤
        (k : ℝ) * Finset.sum (chebotarevFiber φ h) (fun g => ‖ε g‖ ^ 2) := by
    simpa [hfiber h] using
      (sq_sum_le_card_mul_sum_sq (s := chebotarevFiber φ h) (f := fun g : G => ‖ε g‖))
  calc
    ‖chebotarevFiberAverage φ k ε h‖ ^ 2
        = ((1 / (k : ℝ)) * ‖Finset.sum (chebotarevFiber φ h) ε‖) ^ 2 := by
            simp [chebotarevFiberAverage]
    _ = (1 / (k : ℝ)) ^ 2 * ‖Finset.sum (chebotarevFiber φ h) ε‖ ^ 2 := by ring
    _ ≤ (1 / (k : ℝ)) ^ 2 * (Finset.sum (chebotarevFiber φ h) fun g => ‖ε g‖) ^ 2 := by
          gcongr
    _ ≤ (1 / (k : ℝ)) ^ 2 *
        ((k : ℝ) * Finset.sum (chebotarevFiber φ h) (fun g => ‖ε g‖ ^ 2)) := by
          gcongr
    _ = (1 / (k : ℝ)) * Finset.sum (chebotarevFiber φ h) (fun g => ‖ε g‖ ^ 2) := by
          field_simp [hkR_ne]

/-- Parseval after deleting the trivial character, together with quotient monotonicity for fiber
averaging in the finite class-function setting.
    prop:kernel-chebotarev-plancherel-nonabelian -/
theorem paper_kernel_chebotarev_plancherel_nonabelian
    {G H Ρ : Type*} [Fintype G] [Fintype Ρ]
    [DecidableEq G] [DecidableEq H] [DecidableEq Ρ]
    (ε : G → ℂ) (χ : Ρ → G → ℂ) (trivialRep : Ρ)
    (φ : G → H) (k : ℕ) (hk : 0 < k)
    (hfiber : ∀ h : H, (chebotarevFiber φ h).card = k)
    (hparseval :
      ∑ g, ‖ε g‖ ^ 2 =
        (1 / (Fintype.card G : ℝ)) *
          (∑ ρ, ‖chebotarevCharacterAmplitude ε χ ρ‖ ^ 2))
    (htriv : chebotarevCharacterAmplitude ε χ trivialRep = 0) :
    (∑ g, ‖ε g‖ ^ 2 =
      (1 / (Fintype.card G : ℝ)) *
        Finset.sum (Finset.univ.erase trivialRep) (fun ρ => ‖chebotarevCharacterAmplitude ε χ ρ‖ ^ 2)) ∧
    (∀ h : H,
      ‖chebotarevFiberAverage φ k ε h‖ ^ 2 ≤
        (1 / (k : ℝ)) * Finset.sum (chebotarevFiber φ h) (fun g => ‖ε g‖ ^ 2)) := by
  refine ⟨?_, chebotarevFiber_sum_norm_sq φ k ε hk hfiber⟩
  have hsplit :
      ∑ ρ, ‖chebotarevCharacterAmplitude ε χ ρ‖ ^ 2 =
        Finset.sum (Finset.univ.erase trivialRep) (fun ρ => ‖chebotarevCharacterAmplitude ε χ ρ‖ ^ 2) +
          ‖chebotarevCharacterAmplitude ε χ trivialRep‖ ^ 2 := by
    simpa using
      (Finset.sum_erase_add (s := Finset.univ) (a := trivialRep)
        (f := fun ρ => ‖chebotarevCharacterAmplitude ε χ ρ‖ ^ 2) (Finset.mem_univ _)).symm
  calc
    ∑ g, ‖ε g‖ ^ 2
        = (1 / (Fintype.card G : ℝ)) * ∑ ρ, ‖chebotarevCharacterAmplitude ε χ ρ‖ ^ 2 := hparseval
    _ = (1 / (Fintype.card G : ℝ)) *
          (Finset.sum (Finset.univ.erase trivialRep) (fun ρ => ‖chebotarevCharacterAmplitude ε χ ρ‖ ^ 2) +
            ‖chebotarevCharacterAmplitude ε χ trivialRep‖ ^ 2) := by rw [hsplit]
    _ = (1 / (Fintype.card G : ℝ)) *
          Finset.sum (Finset.univ.erase trivialRep) (fun ρ => ‖chebotarevCharacterAmplitude ε χ ρ‖ ^ 2) := by
          simp [htriv]

end

end Omega.EA

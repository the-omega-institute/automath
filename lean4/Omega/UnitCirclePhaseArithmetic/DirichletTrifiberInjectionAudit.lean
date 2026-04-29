import Mathlib
import Omega.UnitCirclePhaseArithmetic.AppCayleyUpperhalfDisk

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- A Dirichlet point with positive real part `σ`. -/
structure DirichletFiberPoint where
  σ : ℝ
  t : ℝ
  hσ : 0 < σ

@[ext] theorem DirichletFiberPoint.ext {a b : DirichletFiberPoint} (hσ : a.σ = b.σ)
    (ht : a.t = b.t) : a = b := by
  cases a
  cases b
  cases hσ
  cases ht
  simp

/-- The visible radial coordinate `|z| = λ^{-σ}`. -/
def dirichletRadialCoordinate (lam σ : ℝ) : ℝ :=
  Real.exp (-σ * Real.log lam)

/-- The non-periodic Cayley coordinate used to recover `t`. -/
def dirichletCayleyCoordinate (t : ℝ) : ℂ :=
  appCayleyUpperHalfMap (t : ℂ)

/-- The discrete winding certificate carried by the extended Dirichlet coordinates. -/
def dirichletWindingCertificate (lam : ℝ) (s : DirichletFiberPoint) : ℤ :=
  Int.floor ((s.t * Real.log lam) / (2 * Real.pi))

/-- The visible phase coordinate recorded together with the integer winding certificate. -/
def dirichletVisibleArg (lam : ℝ) (s : DirichletFiberPoint) : ℝ :=
  -(s.t * Real.log lam) + 2 * Real.pi * dirichletWindingCertificate lam s

/-- The three-fiber Dirichlet--Cayley extension used in the paper. -/
def dirichletTrifiberInjection (lam : ℝ) (s : DirichletFiberPoint) : ℝ × ℂ × ℤ :=
  (dirichletRadialCoordinate lam s.σ, dirichletCayleyCoordinate s.t, dirichletWindingCertificate lam s)

/-- The visible angle and the winding certificate satisfy the audit consistency identity. -/
def dirichletTrifiberConsistency (lam : ℝ) : Prop :=
  ∀ s : DirichletFiberPoint,
    s.t * Real.log lam + dirichletVisibleArg lam s =
      2 * Real.pi * dirichletWindingCertificate lam s

private lemma dirichlet_real_ne_neg_I (t : ℝ) : (t : ℂ) ≠ -Complex.I := by
  intro h
  have him := congrArg Complex.im h
  norm_num at him

/-- Paper label: `prop:dirichlet-trifiber-injection-audit`. -/
theorem paper_dirichlet_trifiber_injection_audit {lam : ℝ} (hlam : 1 < lam) :
    Function.Injective (dirichletTrifiberInjection lam) ∧ dirichletTrifiberConsistency lam := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    have hrad :
        dirichletRadialCoordinate lam a.σ = dirichletRadialCoordinate lam b.σ := by
      simpa [dirichletTrifiberInjection] using congrArg (fun y => let (r, _, _) := y; r) hab
    have hσ : a.σ = b.σ := by
      have hexp :
          -a.σ * Real.log lam = -b.σ * Real.log lam := by
        exact Real.exp_injective <| by simpa [dirichletRadialCoordinate] using hrad
      nlinarith [hexp, Real.log_pos hlam]
    have hcayley :
        dirichletCayleyCoordinate a.t = dirichletCayleyCoordinate b.t := by
      simpa [dirichletTrifiberInjection] using congrArg (fun y => let (_, u, _) := y; u) hab
    have ht : a.t = b.t := by
      have hinv := congrArg appCayleyUpperHalfInv hcayley
      simpa [dirichletCayleyCoordinate, appCayleyUpperHalf_left_inv,
        dirichlet_real_ne_neg_I] using hinv
    exact DirichletFiberPoint.ext hσ ht
  · intro s
    unfold dirichletVisibleArg
    ring

end

end Omega.UnitCirclePhaseArithmetic

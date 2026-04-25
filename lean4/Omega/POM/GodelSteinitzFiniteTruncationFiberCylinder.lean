import Mathlib
import Omega.POM.GodelSteinitzIsometricRigidity

namespace Omega.POM

open Cardinal

/-- The canonical Cantor-space model used for the finite-truncation fiber statement. -/
abbrev pom_godel_steinitz_finite_truncation_fiber_cylinder_stream := ℕ → Bool

/-- The Gödel/Steinitz image map in the binary-stream model. -/
def pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi
    (ω : pom_godel_steinitz_finite_truncation_fiber_cylinder_stream) :
    pom_godel_steinitz_finite_truncation_fiber_cylinder_stream × Unit :=
  (ω, ())

/-- The depth-`m` binary prefix. -/
def pom_godel_steinitz_finite_truncation_fiber_cylinder_prefixMap
    (m : ℕ) (ω : pom_godel_steinitz_finite_truncation_fiber_cylinder_stream) : Fin m → Bool :=
  fun i => ω i.1

/-- The stable coordinate is just the ambient stream itself. -/
def pom_godel_steinitz_finite_truncation_fiber_cylinder_stableCoordinate
    (m : ℕ) (x : pom_godel_steinitz_finite_truncation_fiber_cylinder_stream) : Fin m → Bool :=
  fun i => x i.1

/-- The Steinitz valuation is constantly `0` in the seed model. -/
def pom_godel_steinitz_finite_truncation_fiber_cylinder_steinitzValuation (_ : ℕ)
    (_ : Unit) : ℕ :=
  0

/-- Recovery ignores the trivial Steinitz valuation and returns the stored prefix. -/
def pom_godel_steinitz_finite_truncation_fiber_cylinder_recoverPrefix
    (m : ℕ) (x : Fin m → Bool) (_ : ℕ) : Fin m → Bool :=
  x

/-- The finite truncation remembers the depth-`m` stable coordinate together with the valuation. -/
def pom_godel_steinitz_finite_truncation_fiber_cylinder_finiteTruncation
    (m : ℕ)
    (z : pom_godel_steinitz_finite_truncation_fiber_cylinder_stream × Unit) :
    Fin m → Bool × ℕ :=
  fun i => (z.1 i.1, 0)

/-- Appending an arbitrary tail to the fixed depth-`m` prefix of `ω`. -/
def pom_godel_steinitz_finite_truncation_fiber_cylinder_appendTail
    (m : ℕ) (ω tail : pom_godel_steinitz_finite_truncation_fiber_cylinder_stream) :
    pom_godel_steinitz_finite_truncation_fiber_cylinder_stream :=
  fun n => if h : n < m then ω n else tail (n - m)

/-- The prefix cylinder around `ω` at depth `m`. -/
def pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinder
    (m : ℕ) (ω : pom_godel_steinitz_finite_truncation_fiber_cylinder_stream) :
    Set pom_godel_steinitz_finite_truncation_fiber_cylinder_stream :=
  pom_godel_steinitz_isometric_rigidity_cylinder
    pom_godel_steinitz_finite_truncation_fiber_cylinder_prefixMap m ω

/-- The exact finite-truncation fiber above `Ψ ω`. -/
def pom_godel_steinitz_finite_truncation_fiber_cylinder_fiber
    (m : ℕ) (ω : pom_godel_steinitz_finite_truncation_fiber_cylinder_stream) :
    Set (pom_godel_steinitz_finite_truncation_fiber_cylinder_stream × Unit) :=
  {z |
    pom_godel_steinitz_finite_truncation_fiber_cylinder_finiteTruncation m z =
      pom_godel_steinitz_finite_truncation_fiber_cylinder_finiteTruncation m
        (pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi ω)}

/-- The image-side closed ball of radius `2^{-m}`. -/
def pom_godel_steinitz_finite_truncation_fiber_cylinder_closedBall
    (m : ℕ) (ω : pom_godel_steinitz_finite_truncation_fiber_cylinder_stream) :
    Set (pom_godel_steinitz_finite_truncation_fiber_cylinder_stream × Unit) :=
  pom_godel_steinitz_isometric_rigidity_closed_ball_in_image
    pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi
    pom_godel_steinitz_finite_truncation_fiber_cylinder_stableCoordinate
    pom_godel_steinitz_finite_truncation_fiber_cylinder_steinitzValuation
    m
    (pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi ω)

lemma pom_godel_steinitz_finite_truncation_fiber_cylinder_prefix_extensionality
    (ω η : pom_godel_steinitz_finite_truncation_fiber_cylinder_stream)
    (h :
      ∀ m : ℕ,
        pom_godel_steinitz_finite_truncation_fiber_cylinder_prefixMap m ω =
          pom_godel_steinitz_finite_truncation_fiber_cylinder_prefixMap m η) :
    ω = η := by
  funext n
  have hprefix := congrFun (h (n + 1)) ⟨n, Nat.lt_succ_self n⟩
  simpa [pom_godel_steinitz_finite_truncation_fiber_cylinder_prefixMap] using hprefix

lemma pom_godel_steinitz_finite_truncation_fiber_cylinder_finiteTruncation_eq_iff
    (m : ℕ) (ω η : pom_godel_steinitz_finite_truncation_fiber_cylinder_stream) :
    pom_godel_steinitz_finite_truncation_fiber_cylinder_finiteTruncation m
        (pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi η) =
      pom_godel_steinitz_finite_truncation_fiber_cylinder_finiteTruncation m
        (pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi ω) ↔
      pom_godel_steinitz_isometric_rigidity_valuation_depth_at
        pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi
        pom_godel_steinitz_finite_truncation_fiber_cylinder_stableCoordinate
        pom_godel_steinitz_finite_truncation_fiber_cylinder_steinitzValuation
        m ω η := by
  constructor
  · intro h
    refine ⟨?_, by simp [pom_godel_steinitz_finite_truncation_fiber_cylinder_steinitzValuation]⟩
    funext i
    exact (congrArg Prod.fst (congrFun h i)).symm
  · rintro ⟨hstable, _⟩
    funext i
    have hbool := congrFun hstable i
    exact Prod.ext hbool.symm rfl

/-- The prefix cylinder is equivalent to the unrestricted tail space. -/
noncomputable def pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinderEquivTail
    (m : ℕ) (ω : pom_godel_steinitz_finite_truncation_fiber_cylinder_stream) :
    {η :
      pom_godel_steinitz_finite_truncation_fiber_cylinder_stream //
        η ∈ pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinder m ω} ≃
      pom_godel_steinitz_finite_truncation_fiber_cylinder_stream where
  toFun η n := η.1 (m + n)
  invFun tail :=
    ⟨pom_godel_steinitz_finite_truncation_fiber_cylinder_appendTail m ω tail, by
      funext i
      simp [pom_godel_steinitz_finite_truncation_fiber_cylinder_appendTail,
        pom_godel_steinitz_finite_truncation_fiber_cylinder_prefixMap]⟩
  left_inv η := by
    ext n
    by_cases h : n < m
    · have hprefix := congrFun η.2 ⟨n, h⟩
      simpa [pom_godel_steinitz_finite_truncation_fiber_cylinder_appendTail, h] using hprefix
    · have hmn : m ≤ n := Nat.le_of_not_lt h
      simp [pom_godel_steinitz_finite_truncation_fiber_cylinder_appendTail, h,
        Nat.add_sub_of_le hmn]
  right_inv tail := by
    funext n
    have hmn : ¬ m + n < m := Nat.not_lt.mpr (Nat.le_add_right m n)
    simp [pom_godel_steinitz_finite_truncation_fiber_cylinder_appendTail, hmn]

/-- The image of the cylinder under `Ψ` is equivalent to the cylinder itself. -/
noncomputable def pom_godel_steinitz_finite_truncation_fiber_cylinder_imageEquiv
    (hPsi_injective : Function.Injective pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi)
    (m : ℕ) (ω : pom_godel_steinitz_finite_truncation_fiber_cylinder_stream) :
    {z :
      pom_godel_steinitz_finite_truncation_fiber_cylinder_stream × Unit //
        z ∈
          pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi ''
            pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinder m ω} ≃
      {η :
        pom_godel_steinitz_finite_truncation_fiber_cylinder_stream //
          η ∈ pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinder m ω} where
  toFun z :=
    ⟨Classical.choose z.2, (Classical.choose_spec z.2).1⟩
  invFun η :=
    ⟨pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi η.1, ⟨η.1, η.2, rfl⟩⟩
  left_inv z := by
    apply Subtype.ext
    exact (Classical.choose_spec z.2).2
  right_inv η := by
    apply Subtype.ext
    let hz :
        pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi η.1 ∈
          pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi ''
            pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinder m ω :=
      ⟨η.1, η.2, rfl⟩
    exact hPsi_injective (Classical.choose_spec hz).2

/-- Paper label: `thm:pom-godel-steinitz-finite-truncation-fiber-cylinder`. In the canonical
binary-stream realization, equality of the finite truncation is equivalent to prefix agreement,
the exact fiber is the corresponding prefix cylinder, the cylinder is the image-side closed ball,
and the fiber has Cantor-space cardinality `𝔠`. -/
theorem paper_pom_godel_steinitz_finite_truncation_fiber_cylinder :
    ∀ m : ℕ, ∀ ω : pom_godel_steinitz_finite_truncation_fiber_cylinder_stream,
      pom_godel_steinitz_finite_truncation_fiber_cylinder_fiber m ω ∩
          Set.range pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi =
        pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi ''
          pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinder m ω ∧
      pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi ''
          pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinder m ω =
        pom_godel_steinitz_finite_truncation_fiber_cylinder_closedBall m ω ∧
      Cardinal.mk
          {z :
            pom_godel_steinitz_finite_truncation_fiber_cylinder_stream × Unit //
              z ∈ pom_godel_steinitz_finite_truncation_fiber_cylinder_fiber m ω ∩
                Set.range pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi} =
        Cardinal.continuum := by
  intro m ω
  let D : pom_multiresolution_godel_tower_injection_data :=
    { omegaInfinity := pom_godel_steinitz_finite_truncation_fiber_cylinder_stream
      xInfinity := pom_godel_steinitz_finite_truncation_fiber_cylinder_stream
      pSteinitz := Unit
      prefixType := fun m => Fin m → Bool
      Psi := pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi
      prefixMap := pom_godel_steinitz_finite_truncation_fiber_cylinder_prefixMap
      stableCoordinate := pom_godel_steinitz_finite_truncation_fiber_cylinder_stableCoordinate
      steinitzValuation := pom_godel_steinitz_finite_truncation_fiber_cylinder_steinitzValuation
      recoverPrefix := pom_godel_steinitz_finite_truncation_fiber_cylinder_recoverPrefix
      recoverPrefix_spec := by
        intro k η
        rfl
      prefix_extensionality :=
        pom_godel_steinitz_finite_truncation_fiber_cylinder_prefix_extensionality }
  have hPsi_injective :
      Function.Injective pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi :=
    paper_pom_multiresolution_godel_tower_injection D
  have hrigid :=
    paper_pom_godel_steinitz_isometric_rigidity
      (prefixType := fun k => Fin k → Bool)
      pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi
      pom_godel_steinitz_finite_truncation_fiber_cylinder_prefixMap
      pom_godel_steinitz_finite_truncation_fiber_cylinder_stableCoordinate
      pom_godel_steinitz_finite_truncation_fiber_cylinder_steinitzValuation
      pom_godel_steinitz_finite_truncation_fiber_cylinder_recoverPrefix
      (by intro k η; rfl)
      (by intro k η ξ h; simpa using h)
      (by intro k η ξ h; simp [pom_godel_steinitz_finite_truncation_fiber_cylinder_steinitzValuation])
      pom_godel_steinitz_finite_truncation_fiber_cylinder_prefix_extensionality
  have hfiber :
      pom_godel_steinitz_finite_truncation_fiber_cylinder_fiber m ω ∩
          Set.range pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi =
        pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi ''
          pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinder m ω := by
    ext z
    constructor
    · rintro ⟨hzFiber, ⟨η, rfl⟩⟩
      have hval :
          pom_godel_steinitz_isometric_rigidity_valuation_depth_at
            pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi
            pom_godel_steinitz_finite_truncation_fiber_cylinder_stableCoordinate
            pom_godel_steinitz_finite_truncation_fiber_cylinder_steinitzValuation
            m ω η := by
        simpa using
          (pom_godel_steinitz_finite_truncation_fiber_cylinder_finiteTruncation_eq_iff m ω η).1
            hzFiber
      exact ⟨η, (hrigid.1 m ω η).2 hval, rfl⟩
    · rintro ⟨η, hη, rfl⟩
      refine ⟨?_, ⟨η, rfl⟩⟩
      have hval := (hrigid.1 m ω η).1 hη
      simpa using
        (pom_godel_steinitz_finite_truncation_fiber_cylinder_finiteTruncation_eq_iff m ω η).2 hval
  have hball :
      pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi ''
          pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinder m ω =
        pom_godel_steinitz_finite_truncation_fiber_cylinder_closedBall m ω := by
    simpa [pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinder,
      pom_godel_steinitz_finite_truncation_fiber_cylinder_closedBall] using hrigid.2 m ω
  have hcylinder_card :
      Cardinal.mk
          {η :
            pom_godel_steinitz_finite_truncation_fiber_cylinder_stream //
              η ∈ pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinder m ω} =
        Cardinal.continuum := by
    calc
      Cardinal.mk
          {η :
            pom_godel_steinitz_finite_truncation_fiber_cylinder_stream //
              η ∈ pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinder m ω} =
          Cardinal.mk pom_godel_steinitz_finite_truncation_fiber_cylinder_stream := by
            exact Cardinal.mk_congr
              (pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinderEquivTail m ω)
      _ = Cardinal.continuum := by
        rw [show Cardinal.mk pom_godel_steinitz_finite_truncation_fiber_cylinder_stream =
            Cardinal.mk (ℕ → Bool) by rfl]
        change Cardinal.mk (ℕ → Bool) = Cardinal.continuum
        rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id,
          Cardinal.lift_aleph0, Cardinal.two_power_aleph0]
  have himage_card :
      Cardinal.mk
          {z :
            pom_godel_steinitz_finite_truncation_fiber_cylinder_stream × Unit //
              z ∈
                pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi ''
                  pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinder m ω} =
        Cardinal.continuum := by
    calc
      Cardinal.mk
          {z :
            pom_godel_steinitz_finite_truncation_fiber_cylinder_stream × Unit //
              z ∈
                pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi ''
                  pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinder m ω} =
          Cardinal.mk
            {η :
              pom_godel_steinitz_finite_truncation_fiber_cylinder_stream //
                η ∈ pom_godel_steinitz_finite_truncation_fiber_cylinder_cylinder m ω} := by
            exact Cardinal.mk_congr
              (pom_godel_steinitz_finite_truncation_fiber_cylinder_imageEquiv
                hPsi_injective m ω)
      _ = Cardinal.continuum := hcylinder_card
  have hfiber_card :
      Cardinal.mk
          {z :
            pom_godel_steinitz_finite_truncation_fiber_cylinder_stream × Unit //
              z ∈ pom_godel_steinitz_finite_truncation_fiber_cylinder_fiber m ω ∩
                Set.range pom_godel_steinitz_finite_truncation_fiber_cylinder_Psi} =
        Cardinal.continuum := by
    rw [hfiber]
    exact himage_card
  exact ⟨hfiber, hball, hfiber_card⟩

end Omega.POM

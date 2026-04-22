import Mathlib.Tactic
import Omega.POM.MultiresolutionGodelTowerInjection

namespace Omega.POM

/-- Agreement of the source words up to depth `m`. -/
def pom_godel_steinitz_isometric_rigidity_prefix_depth_at
    {omegaInfinity : Type*} {prefixType : ℕ → Type*}
    (prefixMap : ∀ m : ℕ, omegaInfinity → prefixType m)
    (m : ℕ) (ω η : omegaInfinity) : Prop :=
  prefixMap m ω = prefixMap m η

/-- Agreement of the target stable coordinate and Steinitz valuation up to depth `m`. -/
def pom_godel_steinitz_isometric_rigidity_valuation_depth_at
    {omegaInfinity xInfinity pSteinitz : Type*} {prefixType : ℕ → Type*}
    (Psi : omegaInfinity → xInfinity × pSteinitz)
    (stableCoordinate : ∀ m : ℕ, xInfinity → prefixType m)
    (steinitzValuation : ∀ _ : ℕ, pSteinitz → ℕ)
    (m : ℕ) (ω η : omegaInfinity) : Prop :=
  stableCoordinate m (Psi ω).1 = stableCoordinate m (Psi η).1 ∧
    steinitzValuation m (Psi ω).2 = steinitzValuation m (Psi η).2

/-- The source cylinder cut out by the depth-`m` prefix of `ω`. -/
def pom_godel_steinitz_isometric_rigidity_cylinder
    {omegaInfinity : Type*} {prefixType : ℕ → Type*}
    (prefixMap : ∀ m : ℕ, omegaInfinity → prefixType m)
    (m : ℕ) (ω : omegaInfinity) : Set omegaInfinity :=
  {η | pom_godel_steinitz_isometric_rigidity_prefix_depth_at prefixMap m ω η}

/-- The image-side closed ball of radius `2^{-m}` encoded by the depth-`m` stable/valuation data. -/
def pom_godel_steinitz_isometric_rigidity_closed_ball_in_image
    {omegaInfinity xInfinity pSteinitz : Type*} {prefixType : ℕ → Type*}
    (Psi : omegaInfinity → xInfinity × pSteinitz)
    (stableCoordinate : ∀ m : ℕ, xInfinity → prefixType m)
    (steinitzValuation : ∀ _ : ℕ, pSteinitz → ℕ)
    (m : ℕ) (center : xInfinity × pSteinitz) : Set (xInfinity × pSteinitz) :=
  {z | z ∈ Set.range Psi ∧
      stableCoordinate m center.1 = stableCoordinate m z.1 ∧
      steinitzValuation m center.2 = steinitzValuation m z.2}

/-- Paper label: `thm:pom-godel-steinitz-isometric-rigidity`. The multiresolution recovery package
identifies depth-`m` prefix agreement with equality of the corresponding stable coordinate and
Steinitz valuation, so cylinders match the closed balls cut out by the image-side ultrametric on
`Psi(Ω∞)`. -/
theorem paper_pom_godel_steinitz_isometric_rigidity
    {omegaInfinity xInfinity pSteinitz : Type*} (prefixType : ℕ → Type*)
    (Psi : omegaInfinity → xInfinity × pSteinitz)
    (prefixMap : ∀ m : ℕ, omegaInfinity → prefixType m)
    (stableCoordinate : ∀ m : ℕ, xInfinity → prefixType m)
    (steinitzValuation : ∀ _ : ℕ, pSteinitz → ℕ)
    (recoverPrefix : ∀ m : ℕ, prefixType m → ℕ → prefixType m)
    (hRecover :
      ∀ m : ℕ, ∀ ω : omegaInfinity,
        recoverPrefix m (stableCoordinate m (Psi ω).1) (steinitzValuation m (Psi ω).2) =
          prefixMap m ω)
    (hStable :
      ∀ m : ℕ, ∀ ω η : omegaInfinity,
        prefixMap m ω = prefixMap m η →
          stableCoordinate m (Psi ω).1 = stableCoordinate m (Psi η).1)
    (hValuation :
      ∀ m : ℕ, ∀ ω η : omegaInfinity,
        prefixMap m ω = prefixMap m η →
          steinitzValuation m (Psi ω).2 = steinitzValuation m (Psi η).2)
    (hExtensionality :
      ∀ ω η : omegaInfinity, (∀ m : ℕ, prefixMap m ω = prefixMap m η) → ω = η) :
    (∀ m : ℕ, ∀ ω η : omegaInfinity,
      pom_godel_steinitz_isometric_rigidity_prefix_depth_at prefixMap m ω η ↔
        pom_godel_steinitz_isometric_rigidity_valuation_depth_at
          Psi stableCoordinate steinitzValuation m ω η) ∧
      ∀ m : ℕ, ∀ ω : omegaInfinity,
        Psi '' pom_godel_steinitz_isometric_rigidity_cylinder prefixMap m ω =
          pom_godel_steinitz_isometric_rigidity_closed_ball_in_image
            Psi stableCoordinate steinitzValuation m (Psi ω) := by
  let D : pom_multiresolution_godel_tower_injection_data :=
    { omegaInfinity := omegaInfinity
      xInfinity := xInfinity
      pSteinitz := pSteinitz
      prefixType := prefixType
      Psi := Psi
      prefixMap := prefixMap
      stableCoordinate := stableCoordinate
      steinitzValuation := steinitzValuation
      recoverPrefix := recoverPrefix
      recoverPrefix_spec := hRecover
      prefix_extensionality := hExtensionality }
  have _ : Function.Injective Psi := paper_pom_multiresolution_godel_tower_injection D
  have hDepth :
      ∀ m : ℕ, ∀ ω η : omegaInfinity,
        pom_godel_steinitz_isometric_rigidity_prefix_depth_at prefixMap m ω η ↔
          pom_godel_steinitz_isometric_rigidity_valuation_depth_at
            Psi stableCoordinate steinitzValuation m ω η := by
    intro m ω η
    constructor
    · intro hPrefix
      exact ⟨hStable m ω η hPrefix, hValuation m ω η hPrefix⟩
    · rintro ⟨hStableEq, hValuationEq⟩
      calc
        prefixMap m ω =
            recoverPrefix m (stableCoordinate m (Psi ω).1) (steinitzValuation m (Psi ω).2) := by
              symm
              exact hRecover m ω
        _ =
            recoverPrefix m (stableCoordinate m (Psi η).1) (steinitzValuation m (Psi η).2) := by
              rw [hStableEq, hValuationEq]
        _ = prefixMap m η := hRecover m η
  refine ⟨hDepth, ?_⟩
  intro m ω
  ext z
  constructor
  · rintro ⟨η, hη, rfl⟩
    exact ⟨⟨η, rfl⟩, (hDepth m ω η).1 hη⟩
  · rintro ⟨⟨η, rfl⟩, hz⟩
    exact ⟨η, (hDepth m ω η).2 hz, rfl⟩

end Omega.POM

import Omega.Zeta.XiTimePart9zgQuadraticSectorConditionalTensorAverage

namespace Omega.Zeta

/-- The three harmonic modes relevant to the quadratic-sector collapse: the trivial mode, the sign
mode, and the aggregate of all remaining irreducible modes. -/
inductive xi_time_part9zg_quadratic_sector_character_harmonic_collapse_mode
  | trivial
  | sign
  | other
  deriving DecidableEq, Fintype

/-- The sector sign encoded by a Boolean choice: `true` means `+1`, `false` means `-1`. -/
def xi_time_part9zg_quadratic_sector_character_harmonic_collapse_sectorSign (b : Bool) : ℝ :=
  if b then 1 else -1

/-- The balanced sign function on the two-point model used for the conditional tensor average. -/
def xi_time_part9zg_quadratic_sector_character_harmonic_collapse_baseSign (b : Bool) : ℝ :=
  if b then 1 else -1

/-- The observable realizing the trivial, sign, and collapsed nonabelian modes. -/
def xi_time_part9zg_quadratic_sector_character_harmonic_collapse_observable
    (mode : xi_time_part9zg_quadratic_sector_character_harmonic_collapse_mode) (b : Bool) : ℝ :=
  match mode with
  | .trivial => 1
  | .sign => xi_time_part9zg_quadratic_sector_character_harmonic_collapse_baseSign b
  | .other => 0

/-- The concrete two-point instance of the quadratic-sector conditional tensor-average theorem. -/
noncomputable def xi_time_part9zg_quadratic_sector_character_harmonic_collapse_data
    (ε δ : Bool)
    (χ ψ : xi_time_part9zg_quadratic_sector_character_harmonic_collapse_mode) :
    QuadraticSectorConditionalTensorAverageData where
  α := Bool
  β := Bool
  instFintypeα := inferInstance
  instDecEqα := inferInstance
  instFintypeβ := inferInstance
  instDecEqβ := inferInstance
  leftObservable :=
    xi_time_part9zg_quadratic_sector_character_harmonic_collapse_observable χ
  rightObservable :=
    xi_time_part9zg_quadratic_sector_character_harmonic_collapse_observable ψ
  leftSign := xi_time_part9zg_quadratic_sector_character_harmonic_collapse_baseSign
  rightSign := xi_time_part9zg_quadratic_sector_character_harmonic_collapse_baseSign
  epsSign := xi_time_part9zg_quadratic_sector_character_harmonic_collapse_sectorSign ε
  deltaSign := xi_time_part9zg_quadratic_sector_character_harmonic_collapse_sectorSign δ
  cardα_pos := by decide
  cardβ_pos := by decide
  leftSignMean_zero := by
    simp [xi_time_part9zg_quadratic_sector_character_harmonic_collapse_baseSign]
  rightSignMean_zero := by
    simp [xi_time_part9zg_quadratic_sector_character_harmonic_collapse_baseSign]

/-- The conditional harmonic average in the quadratic sector. -/
noncomputable def xi_time_part9zg_quadratic_sector_character_harmonic_collapse_average
    (ε δ : Bool)
    (χ ψ : xi_time_part9zg_quadratic_sector_character_harmonic_collapse_mode) : ℝ :=
  let D :=
    xi_time_part9zg_quadratic_sector_character_harmonic_collapse_data ε δ χ ψ
  D.sectorConditionalAverage

/-- The four surviving modes and the vanishing of every other mode. -/
def xi_time_part9zg_quadratic_sector_character_harmonic_collapse_expected
    (ε δ : Bool)
    (χ ψ : xi_time_part9zg_quadratic_sector_character_harmonic_collapse_mode) : ℝ :=
  match χ, ψ with
  | .trivial, .trivial => 1
  | .sign, .trivial =>
      xi_time_part9zg_quadratic_sector_character_harmonic_collapse_sectorSign ε
  | .trivial, .sign =>
      xi_time_part9zg_quadratic_sector_character_harmonic_collapse_sectorSign δ
  | .sign, .sign =>
      xi_time_part9zg_quadratic_sector_character_harmonic_collapse_sectorSign ε *
        xi_time_part9zg_quadratic_sector_character_harmonic_collapse_sectorSign δ
  | _, _ => 0

/-- Paper label: `thm:xi-time-part9zg-quadratic-sector-character-harmonic-collapse`. After
conditioning on the quadratic sign sector, only the trivial/sign modes survive on each side; the
aggregate of every genuinely nonabelian mode has zero conditional average. -/
theorem paper_xi_time_part9zg_quadratic_sector_character_harmonic_collapse
    (ε δ : Bool)
    (χ ψ : xi_time_part9zg_quadratic_sector_character_harmonic_collapse_mode) :
    xi_time_part9zg_quadratic_sector_character_harmonic_collapse_average ε δ χ ψ =
      xi_time_part9zg_quadratic_sector_character_harmonic_collapse_expected ε δ χ ψ := by
  let D := xi_time_part9zg_quadratic_sector_character_harmonic_collapse_data ε δ χ ψ
  have hD : D.sectorAverageFormula := by
    exact paper_xi_time_part9zg_quadratic_sector_conditional_tensor_average D
  cases ε <;> cases δ <;> cases χ <;> cases ψ <;>
    simpa [D, xi_time_part9zg_quadratic_sector_character_harmonic_collapse_average,
      xi_time_part9zg_quadratic_sector_character_harmonic_collapse_data,
      xi_time_part9zg_quadratic_sector_character_harmonic_collapse_expected,
      xi_time_part9zg_quadratic_sector_character_harmonic_collapse_sectorSign,
      xi_time_part9zg_quadratic_sector_character_harmonic_collapse_baseSign,
      xi_time_part9zg_quadratic_sector_character_harmonic_collapse_observable,
      QuadraticSectorConditionalTensorAverageData.sectorAverageFormula,
      QuadraticSectorConditionalTensorAverageData.sectorConditionalAverage,
      QuadraticSectorConditionalTensorAverageData.leftAverage,
      QuadraticSectorConditionalTensorAverageData.rightAverage,
      QuadraticSectorConditionalTensorAverageData.leftSignedAverage,
      QuadraticSectorConditionalTensorAverageData.rightSignedAverage] using hD

end Omega.Zeta

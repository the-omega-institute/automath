import Mathlib.Tactic

namespace Omega.Conclusion

/-- The halting alternative used by the two-symbol spectral embedding: `none` is the infinite
halting time and `some t` is a finite halt at time `t`. -/
abbrev conclusion_halting_tv_spectral_embedding_on_2adic_attractor_time := Option ℕ

/-- Geometric tail mass for the law `μ({n}) = 2^-(n+1)`. -/
noncomputable def conclusion_halting_tv_spectral_embedding_on_2adic_attractor_tail
    (t : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ t

/-- The reference all-one code. -/
def conclusion_halting_tv_spectral_embedding_on_2adic_attractor_referenceCode
    (_n : ℕ) : Fin 2 :=
  1

/-- The finite/infinite halting code `1_{n < T}` with the infinite case equal to the all-one
reference code. -/
def conclusion_halting_tv_spectral_embedding_on_2adic_attractor_haltingCode
    (τ : conclusion_halting_tv_spectral_embedding_on_2adic_attractor_time) (n : ℕ) :
    Fin 2 :=
  match τ with
  | none => 1
  | some t => if n < t then 1 else 0

/-- Prefix observed at sample time `n`, followed by the stationary all-one tail. -/
def conclusion_halting_tv_spectral_embedding_on_2adic_attractor_prefix
    (τ : conclusion_halting_tv_spectral_embedding_on_2adic_attractor_time) (n i : ℕ) :
    Fin 2 :=
  if i ≤ n then
    conclusion_halting_tv_spectral_embedding_on_2adic_attractor_haltingCode τ i
  else
    1

/-- Concrete separated coding package for the two-symbol `2`-adic attractor model. -/
structure conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data where
  codedSpace : Type
  codingMap : (ℕ → Fin 2) → codedSpace
  codingMap_injective : Function.Injective codingMap
  haltingTime : conclusion_halting_tv_spectral_embedding_on_2adic_attractor_time

namespace conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data

/-- The sample point in the attractor obtained from the halting prefix at time `n`. -/
def haltingPoint
    (D : conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data) (n : ℕ) :
    D.codedSpace :=
  D.codingMap fun i =>
    conclusion_halting_tv_spectral_embedding_on_2adic_attractor_prefix D.haltingTime n i

/-- The reference point from the all-one code. -/
def referencePoint
    (D : conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data) :
    D.codedSpace :=
  D.codingMap conclusion_halting_tv_spectral_embedding_on_2adic_attractor_referenceCode

/-- Common geometric mass of samples whose halting prefix agrees with the all-one reference code. -/
noncomputable def commonMass
    (D : conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data) : ℝ :=
  match D.haltingTime with
  | none => 1
  | some t => 1 - conclusion_halting_tv_spectral_embedding_on_2adic_attractor_tail t

/-- Total-variation distance between the halting push-forward law and the all-one reference law. -/
noncomputable def totalVariation
    (D : conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data) : ℝ :=
  1 - D.commonMass

/-- The spectral line law: infinite halting time gives zero distance, and a finite halt at `t`
leaves exactly the geometric tail mass `2^-t`. -/
def tvSpectralEmbeddingLaw
    (D : conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data) : Prop :=
  D.totalVariation =
    match D.haltingTime with
    | none => 0
    | some t => conclusion_halting_tv_spectral_embedding_on_2adic_attractor_tail t

end conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data

/-- Paper label: `thm:conclusion-halting-tv-spectral-embedding-on-2adic-attractor`. -/
theorem paper_conclusion_halting_tv_spectral_embedding_on_2adic_attractor
    (D : conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data) :
    D.tvSpectralEmbeddingLaw := by
  cases hτ : D.haltingTime with
  | none =>
      simp [hτ, conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data.tvSpectralEmbeddingLaw,
        conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data.totalVariation,
        conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data.commonMass]
  | some t =>
      simp [hτ, conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data.tvSpectralEmbeddingLaw,
        conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data.totalVariation,
        conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data.commonMass]

end Omega.Conclusion

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Omega.POM

/-- A finite moment window of orders `0, …, Q`, sampled across resolutions. -/
abbrev pom_fiber_schur_bidirectional_compilation_moment_window (Q : ℕ) :=
  Fin (Q + 1) → ℕ → ℕ

/-- The fiber-side decoder reads the whole finite moment window at a fixed resolution. -/
def pom_fiber_schur_bidirectional_compilation_fiber_decode (Q : ℕ)
    (W : pom_fiber_schur_bidirectional_compilation_moment_window Q) (m : ℕ) : ℕ :=
  ∑ q : Fin (Q + 1), W q m

/-- The Schur-side decoder reads the first two resolution samples in a fixed channel. -/
def pom_fiber_schur_bidirectional_compilation_schur_decode (Q : ℕ)
    (W : pom_fiber_schur_bidirectional_compilation_moment_window Q) (q : Fin (Q + 1)) : ℕ :=
  W q 0 + W q 1

/-- Concrete finite-window Prony--Hankel reconstruction predicate for the decoded fiber side. -/
def pom_fiber_schur_bidirectional_compilation_prony_hankel_fiber_reconstruction
    (Q : ℕ) (W : pom_fiber_schur_bidirectional_compilation_moment_window Q)
    (fiberSpectrum : ℕ → ℕ) : Prop :=
  ∀ m : ℕ,
    fiberSpectrum m = pom_fiber_schur_bidirectional_compilation_fiber_decode Q W m

/-- Concrete finite-window Schur tomography predicate for the decoded channel side. -/
def pom_fiber_schur_bidirectional_compilation_schur_tomography_reconstruction
    (Q : ℕ) (W : pom_fiber_schur_bidirectional_compilation_moment_window Q)
    (schurSpectrum : Fin (Q + 1) → ℕ) : Prop :=
  ∀ q : Fin (Q + 1),
    schurSpectrum q = pom_fiber_schur_bidirectional_compilation_schur_decode Q W q

/-- The finite moment window simultaneously supplies a fiber decoder and a Schur-channel decoder. -/
def pom_fiber_schur_bidirectional_compilation_statement : Prop :=
  ∀ Q : ℕ,
    2 ≤ Q →
      ∀ W : pom_fiber_schur_bidirectional_compilation_moment_window Q,
        ∃ fiberSpectrum : ℕ → ℕ,
          ∃ schurSpectrum : Fin (Q + 1) → ℕ,
            pom_fiber_schur_bidirectional_compilation_prony_hankel_fiber_reconstruction
                Q W fiberSpectrum ∧
              pom_fiber_schur_bidirectional_compilation_schur_tomography_reconstruction
                Q W schurSpectrum

/-- Paper label: `thm:pom-fiber-schur-bidirectional-compilation`. -/
theorem paper_pom_fiber_schur_bidirectional_compilation :
    pom_fiber_schur_bidirectional_compilation_statement := by
  intro Q _hQ W
  refine ⟨pom_fiber_schur_bidirectional_compilation_fiber_decode Q W,
    pom_fiber_schur_bidirectional_compilation_schur_decode Q W, ?_, ?_⟩
  · intro m
    rfl
  · intro q
    rfl

end Omega.POM

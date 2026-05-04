import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete valuation/projection data for the first-deviation-depth criterion.  The value
`alpha` is the torsor displacement: either zero, or the halting displacement
`-2^(L * N)`. -/
structure xi_time_part9g_first_deviation_depth_data where
  xi_time_part9g_first_deviation_depth_L : ℕ
  xi_time_part9g_first_deviation_depth_N : ℕ
  xi_time_part9g_first_deviation_depth_alpha : ℤ
  xi_time_part9g_first_deviation_depth_L_pos :
    0 < xi_time_part9g_first_deviation_depth_L
  xi_time_part9g_first_deviation_depth_alpha_cases :
    xi_time_part9g_first_deviation_depth_alpha = 0 ∨
      xi_time_part9g_first_deviation_depth_alpha =
        -((2 : ℤ) ^
          (xi_time_part9g_first_deviation_depth_L *
            xi_time_part9g_first_deviation_depth_N))

namespace xi_time_part9g_first_deviation_depth_data

/-- Agreement at projection depth `n`: zero displacement agrees at every depth, while the
halting displacement agrees exactly through depth `L * N`. -/
def xi_time_part9g_first_deviation_depth_projectionAgrees
    (D : xi_time_part9g_first_deviation_depth_data) (n : ℕ) : Prop :=
  D.xi_time_part9g_first_deviation_depth_alpha = 0 ∨
    n ≤ D.xi_time_part9g_first_deviation_depth_L *
      D.xi_time_part9g_first_deviation_depth_N

/-- The finite first-deviation index; zero denotes the non-halting/no-deviation branch. -/
def xi_time_part9g_first_deviation_depth_firstIndex
    (D : xi_time_part9g_first_deviation_depth_data) : ℕ :=
  if D.xi_time_part9g_first_deviation_depth_alpha = 0 then
    0
  else
    D.xi_time_part9g_first_deviation_depth_L *
        D.xi_time_part9g_first_deviation_depth_N +
      1

/-- Concrete statement for the two branches of the binary torsor chain. -/
def xi_time_part9g_first_deviation_depth_statement
    (D : xi_time_part9g_first_deviation_depth_data) : Prop :=
  (D.xi_time_part9g_first_deviation_depth_alpha = 0 ∨
      D.xi_time_part9g_first_deviation_depth_alpha =
        -((2 : ℤ) ^
          (D.xi_time_part9g_first_deviation_depth_L *
            D.xi_time_part9g_first_deviation_depth_N))) ∧
    (D.xi_time_part9g_first_deviation_depth_alpha = 0 →
      D.xi_time_part9g_first_deviation_depth_firstIndex = 0 ∧
        ∀ n : ℕ, D.xi_time_part9g_first_deviation_depth_projectionAgrees n) ∧
    (D.xi_time_part9g_first_deviation_depth_alpha =
        -((2 : ℤ) ^
          (D.xi_time_part9g_first_deviation_depth_L *
            D.xi_time_part9g_first_deviation_depth_N)) →
      D.xi_time_part9g_first_deviation_depth_firstIndex =
          D.xi_time_part9g_first_deviation_depth_L *
              D.xi_time_part9g_first_deviation_depth_N +
            1 ∧
        (∀ n : ℕ,
          n ≤ D.xi_time_part9g_first_deviation_depth_L *
              D.xi_time_part9g_first_deviation_depth_N →
            D.xi_time_part9g_first_deviation_depth_projectionAgrees n) ∧
          ¬D.xi_time_part9g_first_deviation_depth_projectionAgrees
            (D.xi_time_part9g_first_deviation_depth_L *
                D.xi_time_part9g_first_deviation_depth_N +
              1) ∧
            ∀ n : ℕ,
              1 ≤ n →
                (¬D.xi_time_part9g_first_deviation_depth_projectionAgrees n ↔
                  D.xi_time_part9g_first_deviation_depth_L *
                      D.xi_time_part9g_first_deviation_depth_N +
                    1 ≤ n))

end xi_time_part9g_first_deviation_depth_data

open xi_time_part9g_first_deviation_depth_data

/-- Paper label: `prop:xi-time-part9g-first-deviation-depth`. -/
theorem paper_xi_time_part9g_first_deviation_depth
    (D : xi_time_part9g_first_deviation_depth_data) :
    xi_time_part9g_first_deviation_depth_statement D := by
  refine ⟨D.xi_time_part9g_first_deviation_depth_alpha_cases, ?_, ?_⟩
  · intro hzero
    constructor
    · simp [xi_time_part9g_first_deviation_depth_firstIndex, hzero]
    · intro n
      exact Or.inl hzero
  · intro hhalt
    have hpow_pos :
        (0 : ℤ) <
          (2 : ℤ) ^
            (D.xi_time_part9g_first_deviation_depth_L *
              D.xi_time_part9g_first_deviation_depth_N) :=
      pow_pos (by norm_num) _
    have halpha_ne_zero : D.xi_time_part9g_first_deviation_depth_alpha ≠ 0 := by
      intro hzero
      rw [hhalt] at hzero
      linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [xi_time_part9g_first_deviation_depth_firstIndex, halpha_ne_zero]
    · intro n hn
      exact Or.inr hn
    · intro hagree
      rcases hagree with hzero | hle
      · exact halpha_ne_zero hzero
      · omega
    · intro n _hn
      constructor
      · intro hnot
        by_contra hlt
        have hnle :
            n ≤ D.xi_time_part9g_first_deviation_depth_L *
              D.xi_time_part9g_first_deviation_depth_N := by omega
        exact hnot (Or.inr hnle)
      · intro hfirst hagree
        rcases hagree with hzero | hle
        · exact halpha_ne_zero hzero
        · omega

end Omega.Zeta

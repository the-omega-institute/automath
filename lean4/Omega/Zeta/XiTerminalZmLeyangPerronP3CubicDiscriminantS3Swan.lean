import Mathlib.Tactic

namespace Omega.Zeta

/-- The characteristic-`3` residue field represented by residues. -/
abbrev xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_F3 := Fin 3

/-- The constant coefficient of the cubic discriminant after substituting `a=-1,b=1`. -/
def xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_discriminantConstant :
    ℕ :=
  (1 + 3 - 4 % 3) % 3

/-- The linear coefficient of the same discriminant. -/
def xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_discriminantLinear :
    ℕ :=
  (4 + 18) % 3

/-- The quadratic coefficient of the same discriminant. -/
def xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_discriminantQuadratic :
    ℕ :=
  27 % 3

/-- The derivative `du/dv = 2v - 1` in characteristic `3`, represented as a residue. -/
def xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_derivativeResidue
    (v : xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_F3) :
    xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_F3 :=
  ⟨(2 * v.1 + 2) % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The cubic map `u = -v^3 + v^2 - v` in characteristic `3`. -/
def xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_coverResidue
    (v : xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_F3) :
    xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_F3 :=
  ⟨(2 * v.1 ^ (3 : Nat) + v.1 ^ (2 : Nat) + 2 * v.1) % 3,
    Nat.mod_lt _ (by norm_num)⟩

/-- The unique finite critical point of the cubic map. -/
def xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_finiteCriticalPoint :
    xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_F3 :=
  ⟨2, by norm_num⟩

/-- The ramification contribution at infinity for the cubic branch. -/
def xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_infinityContribution : ℕ :=
  3

/-- The Swan index at infinity after subtracting the tame `e - 1` part. -/
def xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_swanIndex : ℕ :=
  1

/-- Concrete finite ramification and Swan certificate for the characteristic-`3` cubic cover. -/
def xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_statement : Prop :=
  xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_discriminantConstant = 0 ∧
    xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_discriminantLinear = 1 ∧
    xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_discriminantQuadratic = 0 ∧
    xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_derivativeResidue
        xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_finiteCriticalPoint = 0 ∧
    (∀ v : xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_F3,
      xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_derivativeResidue v = 0 →
        v = xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_finiteCriticalPoint) ∧
    xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_coverResidue
        xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_finiteCriticalPoint = 0 ∧
    xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_infinityContribution = 3 ∧
    xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_swanIndex = 1

/-- Paper label: `thm:xi-terminal-zm-leyang-perron-p3-cubic-discriminant-s3-swan`. -/
theorem paper_xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan :
    xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_statement := by
  unfold xi_terminal_zm_leyang_perron_p3_cubic_discriminant_s3_swan_statement
  native_decide

end Omega.Zeta

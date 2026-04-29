import Mathlib.Data.Int.Basic

namespace Omega.Conclusion

/-- The length-two atom contributes only to even trace coefficients. -/
def conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_atomTrace
    (v : ℤ) (n : ℕ) : ℤ :=
  if n % 2 = 0 then v ^ (n / 2) else 0

/-- A concrete core trace-coefficient model. -/
def conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_coreTrace
    (u v : ℤ) (n : ℕ) : ℤ :=
  u ^ n + v ^ n

/-- The joint trace is the sum of the core trace and the universal length-two atom. -/
def conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_jointTrace
    (u v : ℤ) (n : ℕ) : ℤ :=
  conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_coreTrace u v n +
    conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_atomTrace v n

/-- Concrete statement for the length-two atom trace splitting theorem. -/
def conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_statement : Prop :=
  (∀ (u v : ℤ) (n : ℕ),
      conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_jointTrace u v n =
        conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_coreTrace u v n +
          conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_atomTrace v n) ∧
    (∀ (u v : ℤ) (r : ℕ),
      conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_jointTrace
          u v (2 * r + 1) =
        conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_coreTrace
          u v (2 * r + 1)) ∧
      ∀ (u v : ℤ) (r : ℕ),
        conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_jointTrace
            u v (2 * (r + 1)) =
          conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_coreTrace
              u v (2 * (r + 1)) +
            v ^ (r + 1)

/-- Paper label: `thm:conclusion-realinput40-joint-zeta-lengthtwo-atom-trace-splitting`. -/
theorem paper_conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting :
    conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v n
    rfl
  · intro u v r
    simp [conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_jointTrace,
      conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_atomTrace]
  · intro u v r
    simp [conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_jointTrace,
      conclusion_realinput40_joint_zeta_lengthtwo_atom_trace_splitting_atomTrace]

end Omega.Conclusion

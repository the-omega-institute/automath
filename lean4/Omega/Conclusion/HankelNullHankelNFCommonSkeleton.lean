import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Concrete finite certificate wrapper for the conclusion-level comparison between an integer
Hankel-null certificate and a finite-window Hankel normal form certificate. The certificate fields
store explicit finite data, while the equality fields record that both reconstruction procedures
recover the same monic skeleton and Perron root. -/
structure conclusion_hankel_null_hankelnf_common_skeleton_data where
  q : ℕ
  hankelNullBasis : List (List ℤ)
  hankelNormalFormWindow : List ℤ
  hankelNormalFormOffset : ℕ
  monicSkeleton : List ℤ
  perronRoot : ℝ
  hankelNullRecoveredSkeleton : List ℤ
  hankelNormalFormRecoveredSkeleton : List ℤ
  hankelNullRecoveredPerronRoot : ℝ
  hankelNormalFormRecoveredPerronRoot : ℝ
  q_ge_two : 2 ≤ q
  hankelNullRecoversSkeleton : hankelNullRecoveredSkeleton = monicSkeleton
  hankelNormalFormRecoversSkeleton : hankelNormalFormRecoveredSkeleton = monicSkeleton
  hankelNullRecoversPerronRoot : hankelNullRecoveredPerronRoot = perronRoot
  hankelNormalFormRecoversPerronRoot : hankelNormalFormRecoveredPerronRoot = perronRoot

/-- The two finite certificates recover a common monic skeleton and a common Perron root. -/
def conclusion_hankel_null_hankelnf_common_skeleton_statement
    (D : conclusion_hankel_null_hankelnf_common_skeleton_data) : Prop :=
  2 ≤ D.q ∧
    D.hankelNullRecoveredSkeleton = D.monicSkeleton ∧
    D.hankelNormalFormRecoveredSkeleton = D.monicSkeleton ∧
    D.hankelNullRecoveredPerronRoot = D.perronRoot ∧
    D.hankelNormalFormRecoveredPerronRoot = D.perronRoot ∧
    D.hankelNullRecoveredSkeleton = D.hankelNormalFormRecoveredSkeleton ∧
    D.hankelNullRecoveredPerronRoot = D.hankelNormalFormRecoveredPerronRoot

/-- Paper label: `thm:conclusion-hankel-null-hankelnf-common-skeleton`. -/
theorem paper_conclusion_hankel_null_hankelnf_common_skeleton
    (D : conclusion_hankel_null_hankelnf_common_skeleton_data) :
    conclusion_hankel_null_hankelnf_common_skeleton_statement D := by
  refine ⟨D.q_ge_two, D.hankelNullRecoversSkeleton, D.hankelNormalFormRecoversSkeleton,
    D.hankelNullRecoversPerronRoot, D.hankelNormalFormRecoversPerronRoot, ?_, ?_⟩
  · calc
      D.hankelNullRecoveredSkeleton = D.monicSkeleton := D.hankelNullRecoversSkeleton
      _ = D.hankelNormalFormRecoveredSkeleton := D.hankelNormalFormRecoversSkeleton.symm
  · calc
      D.hankelNullRecoveredPerronRoot = D.perronRoot := D.hankelNullRecoversPerronRoot
      _ = D.hankelNormalFormRecoveredPerronRoot := D.hankelNormalFormRecoversPerronRoot.symm

end Omega.Conclusion

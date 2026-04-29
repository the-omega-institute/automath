import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `prop:gm-toeplitz-cmv-verblunsky-embedding`. The Gram object is
converted to a Toeplitz compression, then to Verblunsky/CMV data, and finally to a
centered-trace control witness. -/
theorem paper_gm_toeplitz_cmv_verblunsky_embedding
    (Gram ToeplitzCompression VerblunskyCMV CenteredTraceControl : Type)
    (build : Gram -> ToeplitzCompression) (opuc : ToeplitzCompression -> VerblunskyCMV)
    (control : VerblunskyCMV -> CenteredTraceControl) :
    Gram -> Nonempty CenteredTraceControl := by
  intro gram
  exact ⟨control (opuc (build gram))⟩

end Omega.SyncKernelRealInput

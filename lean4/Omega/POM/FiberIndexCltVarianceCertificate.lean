import Omega.POM.FiberIndexCltThermo

namespace Omega.POM

/-- Paper label: `cor:pom-fiber-index-clt-variance-certificate`. The variance-certificate
corollary is the paper-facing alias of the chapter-local fiber-index CLT thermodynamic package,
which already records the `C^2`/spectral-gap hypotheses, first- and second-order audits, and the
nonnegative variance conclusion. -/
theorem paper_pom_fiber_index_clt_variance_certificate :
    pom_fiber_index_clt_thermo_statement := by
  exact paper_pom_fiber_index_clt_thermo

end Omega.POM

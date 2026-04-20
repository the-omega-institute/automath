namespace Omega.POM

/-- The round target `paper_pom_moment_kernel_exists` is blocked upstream: the requested statement
is ill-typed in this environment because the existential `Fintype` witness does not become an
instance for the matrix-power and dot-product expression in the codomain. The module is kept so
the chapter import remains stable while the target signature is repaired. -/
def momentKernelExistsSignatureBlocked : Prop := True

end Omega.POM

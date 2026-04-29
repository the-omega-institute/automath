namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-collision-kernel-matrix-power-exp-dimension-under-sharpeth`. -/
theorem paper_conclusion_collision_kernel_matrix_power_exp_dimension_under_sharpeth
    (sharpETH subexponentialMatrixPowerCompiler : Prop)
    (hContradiction : subexponentialMatrixPowerCompiler -> sharpETH -> False) :
    sharpETH -> subexponentialMatrixPowerCompiler -> False := by
  intro hSharpETH hCompiler
  exact hContradiction hCompiler hSharpETH

end Omega.Conclusion

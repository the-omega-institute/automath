namespace Omega.Conclusion

universe u v w

/-- Paper label: `cor:conclusion-offcritical-shift-carries-no-new-geometry`.

An off-critical Mellin operator that factors pointwise through the critical operator and a weight
shift is extensionally the corresponding factored operator. -/
theorem paper_conclusion_offcritical_shift_carries_no_new_geometry
    {F : Type u} {T : Type v} {R : Type w}
    (Mhalf Msigma : F → T → R) (W : F → F)
    (hpoint : ∀ f t, Msigma f t = Mhalf (W f) t) :
    Msigma = fun f t => Mhalf (W f) t := by
  funext f t
  exact hpoint f t

end Omega.Conclusion

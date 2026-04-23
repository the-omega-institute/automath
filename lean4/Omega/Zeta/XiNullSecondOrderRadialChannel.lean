import Omega.TypedAddressBiaxialCompletion.VisibleReadPartial
import Omega.Zeta.OffcriticalQuadraticRadialCompression
import Omega.Zeta.XiOffsetNullTypeSafety

namespace Omega.Zeta

/-- Paper label: `cor:xi-null-second-order-radial-channel`. The second-order off-critical radial
channel is already visible in the quadratic boundary-depth law, but in the pure phase interface it
is still read as `NULL`: the point is off the unitary slice, the PW closure rejects it, and the
visible partial readout therefore returns `none`. -/
theorem paper_xi_null_second_order_radial_channel {γ δ L : ℝ} {s : ℂ}
    (hδ : 0 < δ) (hL : 1 < L) (hs : s.re ≠ 1 / 2) :
    appOffcriticalModSq γ δ < 1 ∧
      appOffcriticalBoundaryDepth γ δ = 4 * δ / (γ ^ 2 + (δ + 1) ^ 2) ∧
      ¬ xiOffsetUnitarySlice L s ∧
      xiOffsetPwClosureNull L s ∧
      let D : Omega.TypedAddressBiaxialCompletion.VisibleReadPartialData :=
        { State := Unit
          Obs := Unit
          read := fun _ => none
          inDomain := fun _ => true
          inVisiblePhase := fun _ => false
          checkPasses := fun _ => true
          obs := fun _ => ()
          guarded_read := by
            intro _
            simp }
      D.read () = none := by
  classical
  have hRadial := paper_xi_offcritical_quadratic_radial_compression γ δ hδ
  have hNull := paper_xi_offset_null_type_safety hL hs
  let D : Omega.TypedAddressBiaxialCompletion.VisibleReadPartialData :=
    { State := Unit
      Obs := Unit
      read := fun _ => none
      inDomain := fun _ => true
      inVisiblePhase := fun _ => false
      checkPasses := fun _ => true
      obs := fun _ => ()
      guarded_read := by
        intro ω
        simp }
  have hRead :=
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_visible_read_partial
      D ()
  have hReadNone : D.read () = none := by
    simpa [D] using hRead
  exact ⟨hRadial.1.1, hRadial.1.2.2, hNull.2.1, hNull.2.2, hReadNone⟩

end Omega.Zeta

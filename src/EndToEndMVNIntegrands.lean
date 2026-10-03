import EndToEndL2Restriction
import MVNProcess

open MeasureTheory Set
open scoped NNReal ENNReal
namespace Asakura.EndToEnd
open Asakura

/-- The restriction of the full-line L2 kernel represents precisely the
future kernel appearing in the printed Ito integral. -/
theorem restricted_mvn_future (H : ℝ) (hH : 0 < H) (t : ℝ≥0) :
    (L2Restriction volume (Ioi 0) (mvnFutureLp H hH t) : ℝ → ℝ) =ᵐ[volume.restrict (Ioi 0)]
      mvnFutureFunction H t := by
  exact (L2Restriction_coe volume (Ioi 0) _).trans
    ((mvn_future_function_memLp H t hH t.coe_nonneg).coeFn_toLp.filter_mono
      (ae_mono Measure.restrict_le_self))

/-- The infinite-horizon kernel is also the printed function as an L2 class. -/
theorem restricted_mvn_past (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ≥0) :
    (L2Restriction volume (Ioi 0) (mvnPastLp H hH0 hH1 t) : ℝ → ℝ) =ᵐ[volume.restrict (Ioi 0)]
      mvnPastFunction H t := by
  exact (L2Restriction_coe volume (Ioi 0) _).trans
    ((mvn_past_function_memLp H t hH0 hH1 t.coe_nonneg).coeFn_toLp.filter_mono
      (ae_mono Measure.restrict_le_self))

theorem restricted_mvn_future_formula (H : ℝ) (hH : 0 < H) (t : ℝ≥0) :
    ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      L2Restriction volume (Ioi 0) (mvnFutureLp H hH t) s =
        (Ioc (0:ℝ) (t:ℝ)).indicator (fun s => ((t:ℝ)-s)^(H-1/2)) s := by
  filter_upwards [restricted_mvn_future H hH t] with s hs
  exact hs

theorem restricted_mvn_past_formula (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ≥0) :
    ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      L2Restriction volume (Ioi 0) (mvnPastLp H hH0 hH1 t) s =
        ((t:ℝ)+s)^(H-1/2)-s^(H-1/2) := by
  filter_upwards [restricted_mvn_past H hH0 hH1 t, ae_restrict_mem measurableSet_Ioi] with s hs hpos
  simpa [mvnPastFunction,mvnPastKernel,hpos] using hs

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.restricted_mvn_future_formula
#print axioms Asakura.EndToEnd.restricted_mvn_past_formula

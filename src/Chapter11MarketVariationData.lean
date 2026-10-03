import Chapter11MarketBracketTransfer
import Chapter11VariationControlClock

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000

/-- The signed interval data used in measure invariance follow from the
 original price decomposition and the new-measure local martingale price. -/
theorem market_variation_increment_transfer {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (S A M N : ClosedTime T → Ω → ℝ) (s0 : Ω → ℝ)
    (hP : SemimartingaleDecomposition P F S A M)
    (hQ : SemimartingaleDecomposition Q F S (fun _ => s0) N)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (ν : Ω → SignedMeasure ℝ)
    (hν : ∀ᵐ w ∂P,∀ a b,a≤b → ν w (Ioc a b)=
      A (realTimeClamp (intervalClamp 0 R hR b)) w-A (realTimeClamp (intervalClamp 0 R hR a)) w) :
    ∀ᵐ w ∂P,∀ a b,a∈Icc 0 R → b∈Icc 0 R → a≤b →
      ν w (Ioc a b)=(N (realTimeClamp b) w-N (realTimeClamp a) w)-
        (M (realTimeClamp b) w-M (realTimeClamp a) w) := by
  filter_upwards [hν] with w hw
  intro a b ha hb hab
  have hat := real_time_below a ha.1 ((EReal.coe_le_coe ha.2).trans_lt hRT)
  have hbt := real_time_below b hb.1 ((EReal.coe_le_coe hb.2).trans_lt hRT)
  rw [hw a b hab,intervalClamp_eq 0 R hR ha,intervalClamp_eq 0 R hR hb]
  have ha' := (hP.decomposition _ hat w).symm.trans (hQ.decomposition _ hat w)
  have hb' := (hP.decomposition _ hbt w).symm.trans (hQ.decomposition _ hbt w)
  linarith

end Asakura.Chapter11

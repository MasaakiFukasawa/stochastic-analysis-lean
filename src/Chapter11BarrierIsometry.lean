import Chapter11BarrierMaturity
import Chapter11FiniteIsometry

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's exact terminal energy identity for the constructed
barrier delta follows from its terminal representation and Ito isometry. -/
theorem barrier_terminal_energy_identity {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T y0 : ℝ) (hb : 0<b) (hK : 0<K) (hKb : K<b)
    (hσ : 0<σ) (hT : 0<T) (hy0 : y0<0) :
    (∫ z,barrierGradient P B b K r σ T y0 z^2 ∂P.prod (volume.restrict (Ioo 0 T)))=
      ∫ w,(barrierDiscountedPayoff P B b K r σ T y0 w-barrierBrownianPrice b K r σ T y0 ![0,0])^2 ∂P := by
  obtain ⟨N,hN,hNI,_,he⟩ := barrier_delta_integral_at_maturity P B b K r σ T y0 hb hK hKb hσ hT hy0
  rw [finite_ito_isometry P B _ (barrier_gradient_measurable P B b K r σ T y0) T hT.le
    (barrier_gradient_progressive P B b K r σ T y0 T hT.le)
    (barrier_delta_terminal_energy P B b K r σ T y0 hb hK hKb hσ hT hy0).1 N hN hNI]
  apply integral_congr_ae
  filter_upwards [he] with w hw
  change (N (realTimeClamp T) w)^2=_
  congr 1
  change barrierBrownianPrice b K r σ T y0 ![0,0]+N (realTimeClamp T) w=barrierDiscountedPayoff P B b K r σ T y0 w at hw
  linarith

end Asakura.Chapter11

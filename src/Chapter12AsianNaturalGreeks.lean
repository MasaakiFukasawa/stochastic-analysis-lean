import Chapter12AsianGreeksFromWienerData
import Chapter12NaturalBrownianPathInformation
import Chapter12FiniteBrownianTrim
import Chapter12BrownianDirectionPairing
import Mathlib.MeasureTheory.Measure.SeparableMeasure

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem asian_call_delta_natural_brownian {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hc : ∀ w,Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0<T)
    (x σ r K : ℝ) (hx : 0<x) (hσ : 0<σ) :
    let BS := naturalBrownianSystem P B hB hm hc
    let X := brownianCompactPath B hc T
    letI : MeasurableSpace Ω := BS.F (realTimeClamp T)
    let I := fun j w => asianMoment T T.property x σ r j (X w)
    HasDerivAt (fun a => Real.exp (-r*T) * ∫ w,max (asianPathAverage a r T T.property σ (X w)-K) 0 ∂P.trim (BS.le (realTimeClamp T)))
      (Real.exp (-r*T) * ∫ w,max (I 0 w/T-K) 0*((1/x)*(I 0 w*B T w/(σ*I 1 w)-1+I 0 w*I 2 w/(I 1 w)^2)) ∂P.trim (BS.le (realTimeClamp T))) x := by
  let BS := naturalBrownianSystem P B hB hm hc
  let X := brownianCompactPath B hc T
  letI := finite_horizon_L2_nontrivial (T:ℝ) (show (0:ℝ)<T from hT)
  letI : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩
  letI : MeasurableSpace (FiniteWienerHilbert 0 T) := borel _
  letI : BorelSpace (FiniteWienerHilbert 0 T) := ⟨rfl⟩
  have hmain := asian_call_delta_from_wiener_data (H := FiniteWienerHilbert 0 T)
    P B hB hm hc T hT (BS.F (realTimeClamp T)) (BS.le _) X
    (brownian_compact_path_terminal_measurable P B hB hm hc T) (fun _ _ => rfl) x σ r K hx hσ
  have hgen := natural_brownian_path_Lp_information P B hB hm hc T T.property
  have hcoord := natural_brownian_coordinate P B hB hm hc T
  obtain ⟨W,hW,hXW⟩ := finite_brownian_trim_wiener P BS T T.property
  letI := probability_trim P _ (BS.le (realTimeClamp T))
  letI : MeasurableSpace Ω := BS.F (realTimeClamp T)
  obtain ⟨hh,hbound,hpair⟩ := brownian_coordinate_direction_properties 0 T T.property 0
  apply hmain W univ dense_univ (fun h _ => hW h) (fun t => brownianTimeDirection (0,t)) hh hbound
  · intro t
    have he : @brownianTimeCoordinate Ω m P inferInstance 0 BS T (0,t)=fun w => X w t := by
      funext w
      exact hcoord (0,t) w
    rw [←he]
    exact hXW (0,t)
  · exact hpair
  · exact hgen

theorem asian_call_vega_natural_brownian {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hc : ∀ w,Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0<T)
    (x σ r K : ℝ) (hx : 0<x) (hσ : 0<σ) :
    let BS := naturalBrownianSystem P B hB hm hc
    let X := brownianCompactPath B hc T
    letI : MeasurableSpace Ω := BS.F (realTimeClamp T)
    let I := fun j w => asianMoment T T.property x σ r j (X w)
    let J := fun j w => asianVegaMoment T T.property x σ r j (X w)
    HasDerivAt (fun a => Real.exp (-r*T) * ∫ w,max (asianPathAverage x r T T.property a (X w)-K) 0 ∂P.trim (BS.le (realTimeClamp T)))
      (Real.exp (-r*T) * ∫ w,max (I 0 w/T-K) 0*(J 0 w*B T w/(σ*I 1 w)-J 1 w/I 1 w-1/σ+J 0 w*I 2 w/(I 1 w)^2) ∂P.trim (BS.le (realTimeClamp T))) σ := by
  let BS := naturalBrownianSystem P B hB hm hc
  let X := brownianCompactPath B hc T
  letI := finite_horizon_L2_nontrivial (T:ℝ) (show (0:ℝ)<T from hT)
  letI : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩
  letI : MeasurableSpace (FiniteWienerHilbert 0 T) := borel _
  letI : BorelSpace (FiniteWienerHilbert 0 T) := ⟨rfl⟩
  have hmain := asian_call_vega_from_wiener_data (H := FiniteWienerHilbert 0 T)
    P B hB hm hc T hT (BS.F (realTimeClamp T)) (BS.le _) X
    (brownian_compact_path_terminal_measurable P B hB hm hc T) (fun _ _ => rfl) x σ r K hx hσ
  have hgen := natural_brownian_path_Lp_information P B hB hm hc T T.property
  have hcoord := natural_brownian_coordinate P B hB hm hc T
  obtain ⟨W,hW,hXW⟩ := finite_brownian_trim_wiener P BS T T.property
  letI := probability_trim P _ (BS.le (realTimeClamp T))
  letI : MeasurableSpace Ω := BS.F (realTimeClamp T)
  obtain ⟨hh,hbound,hpair⟩ := brownian_coordinate_direction_properties 0 T T.property 0
  apply hmain W univ dense_univ (fun h _ => hW h) (fun t => brownianTimeDirection (0,t)) hh hbound
  · intro t
    have he : @brownianTimeCoordinate Ω m P inferInstance 0 BS T (0,t)=fun w => X w t := by
      funext w
      exact hcoord (0,t) w
    rw [←he]
    exact hXW (0,t)
  · exact hpair
  · exact hgen

end Asakura.Chapter12

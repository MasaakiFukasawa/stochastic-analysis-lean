import Chapter4BrownianItoCovariances
import Chapter2StochasticFubiniPrinted

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- Restarting an actual Brownian Ito integral. A new integral is
constructed; its equality to the shifted old integral follows from their
three covariances, rather than assuming a time-shift rule. -/
theorem brownian_ito_shifted_future
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W N C H : HalfClosedTime → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hN : LocalMProcessWitness P F N)
    (hC : LocalCovarianceWitness P F W W C)
    (hclock : ∀ w (r : ℝ),0≤r → C (realTimeClamp r) w=r)
    (hHa : ∀ t,t<⊤ → Measurable[F t] (H t))
    (hHc : ∀ w t,t<⊤ → ContinuousAt (fun a => H a w) t)
    (hNI : ItoCovarianceFormula P F W (fun z => H (realTimeClamp z.2) z.1) N)
    (s : ℝ) (hs : 0≤s) :
    let φ := deterministicTimeShift s hs
    ItoCovarianceFormula P (fun t => F (φ t))
      (fun t w => W (φ t) w-W (φ ⊥) w)
      (fun z => H (φ (realTimeClamp z.2)) z.1)
      (fun t w => N (φ t) w-N (φ ⊥) w) := by
  dsimp only
  let φ := deterministicTimeShift s hs
  let G := fun t => F (φ t)
  let B := fun t w => W (φ t) w-W (φ ⊥) w
  let D := fun t w => C (φ t) w-C (φ ⊥) w
  let J := fun t w => H (φ t) w
  let V := fun t w => N (φ t) w-N (φ ⊥) w
  have hGt : Monotone G := hF.comp (deterministic_shift_mono s hs)
  have hGl t : G t≤m := hle (φ t)
  have hGn t E (hm : MeasurableSet[m] E) (hz : P E=0) : MeasurableSet[G t] E := hnull (φ t) E hm hz
  have hB : LocalMProcessWitness P G B := local_martingale_shifted_future P F hF hle W hW s hs
  have hV : LocalMProcessWitness P G V := local_martingale_shifted_future P F hF hle N hN s hs
  have hD : LocalCovarianceWitness P G B B D := covariance_shifted_future P F hF hle hnull W W C hW hW hC s hs
  have hDa w (r : ℝ) (hr : 0≤r) : D (realTimeClamp r) w=r := by
    dsimp only [D,φ]
    rw [deterministic_shift_real s hs r hr,deterministic_shift_bot s hs,
      hclock w (s+r) (add_nonneg hs hr),hclock w s hs]
    ring
  have hJa t (ht : t<⊤) : Measurable[G t] (J t) := hHa _ (deterministic_shift_below_top s hs t ht)
  have hJc w t (ht : t<⊤) : ContinuousAt (fun a => J a w) t :=
    (hHc w _ (deterministic_shift_below_top s hs t ht)).comp (deterministic_shift_continuous s hs).continuousAt
  have hreg := open_process_real_regularity G J hJa hJc
  obtain ⟨K,hK,hKI⟩ := continuous_adapted_ito_exists P (EReal.coe_lt_top 0) G hGt hGl hGn B hB
    (fun z => J (realTimeClamp z.2) z.1) hreg.1 hreg.2
  obtain ⟨A,E,hA,hE,ha,he⟩ := brownian_ito_cross_and_self_density P F hF hle hnull W N C H hW hN hC hclock hHa hHc hNI
  let As := fun t w => A (φ t) w-A (φ ⊥) w
  let Es := fun t w => E (φ t) w-E (φ ⊥) w
  have hAs : LocalCovarianceWitness P G V B As := covariance_shifted_future P F hF hle hnull N W A hN hW hA s hs
  have hEs : LocalCovarianceWitness P G V V Es := covariance_shifted_future P F hF hle hnull N N E hN hN hE s hs
  have hHreal w := half_line_integral_continuous _ (hHc w)
  have has := shifted_primitive_density P A (fun w a => H (realTimeClamp a) w) hHreal ha s hs
  have hes := shifted_primitive_density P E (fun w a => (H (realTimeClamp a) w)^2) (fun w => (hHreal w).pow 2) he s hs
  obtain ⟨_,Q,_,hQ,_,hq⟩ := brownian_ito_cross_and_self_density P G hGt hGl hGn B K D J hB hK hD hDa hJa hJc hKI
  obtain ⟨R,hR,hr⟩ := half_line_ito_covariance_density P G hGt hGl hGn B K V As J hB hK hV (hAs.symm P G)
    hJa hJc hKI (fun w a => H (realTimeClamp (s+a)) w)
    (fun w => (hHreal w).comp (continuous_const.add continuous_id)) has
  have heq : ∀ᵐ w ∂P,∀ t,t<⊤ → V t w=K t w := by
    apply local_equal_of_three_covariances P G hGt hGl V K Es Q R hV hK hEs hQ (hR.symm P G)
    filter_upwards [hes,hq,hr] with w hew hqw hrw
    intro t ht
    obtain ⟨r,hr0,_,rfl⟩ := finite_closed_time_real t ht
    dsimp only [Es,φ]
    rw [hew r hr0,hqw r hr0,hrw r hr0]
    have hi₁ : (∫ a in 0..r,(H (realTimeClamp (s+a)) w)^2)=∫ a in 0..r,(J (realTimeClamp a) w)^2 := by
      apply intervalIntegral.integral_congr
      intro a ha
      rw [uIcc_of_le hr0] at ha
      dsimp only [J,φ]
      rw [deterministic_shift_real s hs a ha.1]
    have hi₂ : (∫ a in 0..r,J (realTimeClamp a) w*H (realTimeClamp (s+a)) w)=∫ a in 0..r,(J (realTimeClamp a) w)^2 := by
      apply intervalIntegral.integral_congr
      intro a ha
      rw [uIcc_of_le hr0] at ha
      dsimp only [J,φ]
      rw [deterministic_shift_real s hs a ha.1,pow_two]
    rw [hi₁,hi₂]
    ring
  exact ItoCovarianceFormula.congr_integral P G hGt hGl B K V _ hK hV
    (heq.mono (fun w hw t ht => (hw t ht).symm)) hKI

end Asakura.Chapter4

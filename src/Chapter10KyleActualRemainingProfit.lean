import Chapter10KyleIntervalProfit
import Chapter10InitialConditionalIntegral
import FullAuditKyleProfitExercise
open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Check the remaining-profit exercise using the actual integral identity and M2 property. -/
theorem kyle_actual_remaining_profit {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[F t] Q)
    (B C E A : HalfClosedTime → Ω → ℝ) (V : Ω → ℝ) (p0 l σ : ℝ) (hl : 0<l)
    (α : Ω × ℝ → ℝ) (hαm : ∀ w,Measurable (fun s => α (w,s)))
    (hαi : ∀ t,0≤t → ∀ w,IntervalIntegrable (fun s => α (w,s)) volume 0 t)
    (hB : LocalMProcessWitness P F B) (hC : LocalCovarianceWitness P F B B C)
    (hclock : ∀ t,0≤t → ∀ w,C (realTimeClamp t) w=t)
    (hE : SemimartingaleDecomposition P F E A (fun t w => (-l*σ)*B t w))
    (hA : ∀ t,0≤t → ∀ w,A (realTimeClamp t) w=V w-p0-l*(∫ s in 0..t,α (w,s)))
    (hV : Measurable[F ⊥] V) (hV2 : MemLp V 2 P)
    (T : ℝ) (hT : 0≤T) (K : Ω → ℝ) (hK : MemLp K 2 P)
    (hb : ∀ᵐ w ∂P,∀ r∈Icc 0 T,‖E (realTimeClamp r) w‖≤‖K w‖)
    (hz : E (realTimeClamp T)=ᵐ[P] 0)
    (s : ℝ) (hs : 0≤s) (hsT : s≤T) :
    P[(fun w => ∫ u in s..T,E (realTimeClamp u) w*α (w,u))|
      MeasurableSpace.comap (fun w => (V w,V w-E (realTimeClamp s) w)) inferInstance]=ᵐ[P]
      (fun w => (E (realTimeClamp s) w)^2/(2*l)+l*σ^2*(T-s)/2) := by
  letI : MeasurableSpace Ω := m
  obtain ⟨Z,hZ,hZI,hprofit⟩ := kyle_ito_interval_profit_identity P F hF hle hnull B C E A V p0 l σ hl
    α hαm hαi hB hC hclock hE hA
  have hEa (t : HalfClosedTime) (ht : t<⊤) : Measurable[F t] (E t) := by
    rw [show E t=(fun w => A t w+(-l*σ)*B t w) from funext (hE.decomposition t ht)]
    exact (hE.variation.adapted t ht).add ((hB.adapted P F t ht).const_mul _)
  have hM := continuous_brownian_integral_martingale P F hF hle hnull B C E Z hB hC
    (fun w r hr _ => hclock r hr w) hEa hE.continuous hZ hZI T hT K hK hb
  have hVs : Measurable[F (realTimeClamp s)] V := hV.mono (hF bot_le) le_rfl
  have hEs : MemLp (E (realTimeClamp s)) 2 P := by
    apply hK.of_le ((hEa _ (half_real_time_finite _)).mono (hle _) le_rfl).aestronglyMeasurable
    exact hb.mono (fun w hw => hw s ⟨hs,hsT⟩)
  have hPs := hVs.sub (hEa _ (half_real_time_finite _))
  have hPs2 : MemLp (fun w => V w-E (realTimeClamp s) w) 2 P := hV2.sub hEs
  have hZsi : Integrable (Z (realTimeClamp s)) P := by
    simpa only [min_eq_right (real_time_clamp_mono hsT)] using
      (hM.moment (realTimeClamp s)).integrable (by norm_num)
  have hZTi : Integrable (Z (realTimeClamp T)) P := by
    simpa only [min_self] using (hM.moment (realTimeClamp T)).integrable (by norm_num)
  have hZce : P[Z (realTimeClamp T)|F (realTimeClamp s)]=ᵐ[P] Z (realTimeClamp s) := by
    simpa only [min_self,min_eq_right (real_time_clamp_mono hsT)] using
      hM.martingale (realTimeClamp s) (realTimeClamp T) (real_time_clamp_mono hsT)
  have hterminal : (fun w => V w-E (realTimeClamp T) w)=ᵐ[P] V := by
    filter_upwards [hz] with w hw
    simp only [hw,Pi.zero_apply,sub_zero]
  have hh := kyle_remaining_profit_exercise P (F (realTimeClamp s)) (hle _) V
    (fun w => V w-E (realTimeClamp s) w) (fun w => V w-E (realTimeClamp T) w)
    (Z (realTimeClamp s)) (Z (realTimeClamp T))
    (fun w => ∫ u in s..T,E (realTimeClamp u) w*α (w,u)) l σ s T hVs hPs hV2 hPs2 hZsi hZTi hZce hterminal
    (by simpa only [sub_sub_cancel] using! hprofit s T hs hsT)
  simpa only [sub_sub_cancel] using hh

end Asakura.Chapter10

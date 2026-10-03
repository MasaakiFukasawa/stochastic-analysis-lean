import Chapter10KyleActualProfitExact
open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Zero terminal error attains the bound for the actual admissible strategy. -/
theorem kyle_actual_profit_attainment {Ω : Type*} [m : MeasurableSpace Ω]
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
    (hz : E (realTimeClamp T)=ᵐ[P] 0) :
    P[(fun w => ∫ s in 0..T,E (realTimeClamp s) w*α (w,s))|
      MeasurableSpace.comap V inferInstance] =ᵐ[P]
      (fun w => (V w-p0)^2/(2*l)+l*σ^2*T/2) := by
  letI : MeasurableSpace Ω := m
  have hp := kyle_actual_profit_exact P F hF hle hnull B C E A V p0 l σ hl α hαm hαi
    hB hC hclock hE hA hV hV2 T hT K hK hb
  have he : (fun w => (E (realTimeClamp T) w)^2/(2*l))=ᵐ[P] (0 : Ω → ℝ) := by
    filter_upwards [hz] with w hw
    simp only [hw,Pi.zero_apply,zero_pow (by norm_num : (2:ℕ)≠0),zero_div]
  have hc := condExp_congr_ae (m := MeasurableSpace.comap V inferInstance) he
  filter_upwards [hp,hc] with w hw hc
  simpa only [hc,condExp_zero,Pi.zero_apply,sub_zero] using hw

end Asakura.Chapter10

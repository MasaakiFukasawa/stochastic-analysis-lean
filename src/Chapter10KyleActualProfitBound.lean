import Chapter10KyleItoIdentity
import Chapter10InitialConditionalIntegral
import Chapter10KyleProfitBound

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Actual Ito identity, finite expected squared price supremum, and C5 give
the upper bound conditional on the initially known asset value. Neither the
profit identity nor the zero conditional stochastic-integral mean is assumed. -/
theorem kyle_actual_profit_bound {Ω : Type*} [m : MeasurableSpace Ω]
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
    (hb : ∀ᵐ w ∂P,∀ r∈Icc 0 T,‖E (realTimeClamp r) w‖≤‖K w‖) :
    P[(fun w => ∫ s in 0..T,E (realTimeClamp s) w*α (w,s))|
      MeasurableSpace.comap V inferInstance] ≤ᵐ[P]
      (fun w => (V w-p0)^2/(2*l)+l*σ^2*T/2) := by
  letI : MeasurableSpace Ω := m
  obtain ⟨Z,hZ,hZI,hprofit⟩ := kyle_ito_profit_identity P F hF hle hnull B C E A V p0 l σ hl
    α hαm hαi hB hC hclock hE hA
  have hEa (t : HalfClosedTime) (ht : t<⊤) : Measurable[F t] (E t) := by
    rw [show E t=(fun w => A t w+(-l*σ)*B t w) from funext (hE.decomposition t ht)]
    exact (hE.variation.adapted t ht).add ((hB.adapted P F t ht).const_mul _)
  have hM := continuous_brownian_integral_martingale P F hF hle hnull B C E Z hB hC
    (fun w r hr _ => hclock r hr w) hEa hE.continuous hZ hZI T hT K hK hb
  let G := MeasurableSpace.comap V inferInstance
  have hGF : G≤F ⊥ := hV.comap_le
  obtain ⟨hZi,hZ0⟩ := stopped_martingale_initial_conditional_zero (m := m) P F hle Z T hM G hGF
  have hET : MemLp (E (realTimeClamp T)) 2 P := by
    apply hK.of_le ((hEa _ (half_real_time_finite _)).mono (hle _) le_rfl).aestronglyMeasurable
    exact hb.mono (fun w hw => hw T ⟨hT,le_rfl⟩)
  have hp : MemLp (fun w => V w-E (realTimeClamp T) w) 2 P := hV2.sub hET
  apply kyle_conditional_profit_bound (m := m) P G (hGF.trans (hle ⊥)) V
    (fun w => V w-E (realTimeClamp T) w) (Z (realTimeClamp T))
    (fun w => ∫ s in 0..T,E (realTimeClamp s) w*α (w,s)) p0 l σ T hl
    (show Measurable[G] V from Measurable.of_comap_le le_rfl).stronglyMeasurable hV2 hp hZi hZ0
  filter_upwards [hprofit T hT] with w hw
  simpa only [sub_sub_cancel] using hw

end Asakura.Chapter10

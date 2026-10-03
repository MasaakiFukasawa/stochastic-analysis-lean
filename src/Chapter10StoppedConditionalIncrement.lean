import Chapter10InitialConditionalIntegral

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false

/-- A stopped integrable martingale has zero conditional future increment
also in any smaller present information. -/
theorem stopped_martingale_conditional_increment_zero {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hle : ∀ u,F u≤m)
    (Z : HalfClosedTime → Ω → ℝ) (T s t : ℝ) (hst : s≤t) (htT : t≤T)
    (hM : ContinuousMpWitness P F 1 (fun u w => Z (min (realTimeClamp T) u) w))
    (G : MeasurableSpace Ω) (hG : G≤F (realTimeClamp s)) :
    Integrable (Z (realTimeClamp t)) P ∧ Integrable (Z (realTimeClamp s)) P ∧
      P[(fun w => Z (realTimeClamp t) w-Z (realTimeClamp s) w)|G]=ᵐ[P] 0 := by
  letI : MeasurableSpace Ω := m
  have hts : min (realTimeClamp T) (realTimeClamp t)=realTimeClamp (T := (⊤:EReal)) t :=
    min_eq_right (real_time_clamp_mono htT)
  have hss : min (realTimeClamp T) (realTimeClamp s)=realTimeClamp (T := (⊤:EReal)) s :=
    min_eq_right (real_time_clamp_mono (hst.trans htT))
  have hit : Integrable (Z (realTimeClamp t)) P := by
    simpa only [hts] using (hM.moment (realTimeClamp t)).integrable le_rfl
  have his : Integrable (Z (realTimeClamp s)) P := by
    simpa only [hss] using (hM.moment (realTimeClamp s)).integrable le_rfl
  have hsm : Measurable[F (realTimeClamp s)] (Z (realTimeClamp s)) := by
    simpa only [hss] using hM.adapted (realTimeClamp s)
  have hc : P[(fun w => Z (realTimeClamp t) w-Z (realTimeClamp s) w)|F (realTimeClamp s)]=ᵐ[P] 0 := by
    have hh := hM.martingale (realTimeClamp s) (realTimeClamp t) (real_time_clamp_mono hst)
    simp only [hts,hss] at hh
    filter_upwards [condExp_sub hit his (F (realTimeClamp s)),hh] with w hw hh
    change P[(fun w => Z (realTimeClamp t) w-Z (realTimeClamp s) w)|F (realTimeClamp s)] w=0
    simpa only [Pi.sub_apply,condExp_of_stronglyMeasurable (hle _) hsm.stronglyMeasurable his,hh,sub_self] using! hw
  refine ⟨hit,his,?_⟩
  exact (condExp_condExp_of_le hG (hle _)).symm.trans
    ((condExp_congr_ae (m := G) hc).trans (by simp))

end Asakura.Chapter10

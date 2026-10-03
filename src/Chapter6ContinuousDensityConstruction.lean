import Chapter6BrownianContinuousCoefficient
import Chapter6BoundedGirsanovData
import Chapter6ConditionalPushforwardDensity

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- Construct the changed measure from the continuous bounded coefficient,
and obtain the positive endpoint density with the manuscript's lower bound.
The reference measure here is the actual Brownian endpoint law. -/
theorem continuous_density_construction {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (b : ℝ × (Fin d → ℝ) → Fin d → ℝ) (hb : Continuous b)
    (R : ℝ) (hR : 0<R) (K : ℝ) (hK : 0≤K) (hbb : ∀ z,‖WithLp.toLp 2 (b z)‖≤K) :
    let H := stoppedBrownianCoefficient P B b R hR.le
    let V := fun w i => B.W i (realTimeClamp R) w
    ∃ (N : Fin d → HalfClosedTime → Ω → ℝ) (C : HalfClosedTime → Ω → ℝ)
      (Q : Measure Ω),IsProbabilityMeasure Q ∧
      (∀ j,LocalMProcessWitness P B.F (N j)) ∧
      (∀ j,ItoCovarianceFormula P B.F (B.W j) (fun z => H j (realTimeClamp z.2) z.1) (N j)) ∧
      (∀ r,0≤r → C (realTimeClamp r)=ᵐ[P] fun w => ∫ s in 0..r,∑ j,(H j (realTimeClamp s) w)^2) ∧
      (let D := fun w => Real.exp ((∑ j,N j (realTimeClamp R) w)-C (realTimeClamp R) w/2)
       Q=P.withDensity (fun w => ENNReal.ofReal (D w)) ∧ (∫ w,D w ∂P)=1 ∧
       ∃ q : (Fin d → ℝ) → ℝ,Measurable q ∧
         P[D|MeasurableSpace.comap V inferInstance]=q ∘ V ∧
         Q.map V=(P.map V).withDensity (fun y => ENNReal.ofReal (q y)) ∧
         (∀ᵐ y ∂P.map V,Real.exp (-K*(‖WithLp.toLp 2 y‖+2*Real.sqrt ((d:ℝ)*R))-K^2*R/2)≤q y)) := by
  let H := stoppedBrownianCoefficient P B b R hR.le
  let V := fun w i => B.W i (realTimeClamp R) w
  obtain ⟨hHa,hHc,hHb,hrep⟩ := stopped_brownian_coefficient_regular P B b hb R hR.le K hbb
  let G := fun j (z : Ω × ℝ) => H j (realTimeClamp z.2) z.1
  have hGr j w : Continuous (fun r => H j (realTimeClamp r) w) := (hHc j w).comp real_time_clamp_continuous
  have hGm j : Measurable (G j) := by
    have hm r : Measurable (H j (realTimeClamp r)) := (hHa j _).mono (B.le _) le_rfl
    simpa only [G,Function.comp_def,Function.uncurry_def,Prod.swap] using
      (measurable_uncurry_of_continuous_of_measurable (hGr j) hm).comp measurable_swap
  have hGp j r (hr : 0<r) := continuous_adapted_real_progressive B.F B.mono (G j) r hr.le
    (fun s _ => hHa j _) (fun w => (hGr j w).continuousOn)
  have hGb j z : |G j z|≤K := (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => H i (realTimeClamp z.2) z.1)) j).trans (hHb _ _)
  obtain ⟨N,C,hN,hNI,hC,hCe,Q,hQp,hQD,hmean,hD2,_,hAE,BQ,hBQ,hBW⟩ :=
    bounded_girsanov_density_data P B G hGm hGp K hK hGb R hR.le
  let D := fun w => Real.exp ((∑ j,N j (realTimeClamp R) w)-C (realTimeClamp R) w/2)
  have hDi : Integrable D P := hD2.integrable (by norm_num)
  have hZ : LocalMProcessWitness P B.F (fun t w => ∑ j,N j t w) :=
    local_martingale_finset_sum P (show (0:EReal)<⊤ by simp) B.F B.mono B.le univ N (fun j _ => hN j)
  have hCm : Measurable (C (realTimeClamp R)) :=
    ((hC.adapted P B.F hZ hZ _ (changed_time_finite R hR.le))).mono (B.le _) le_rfl
  have hl := bounded_density_conditional_lower_bound P B H N hHa hHc hN hNI R hR
    (fun r x => b (r,x)) (fun r => hb.measurable.comp measurable_prodMk_left) K hK (fun r x => hbb _)
    hrep (C (realTimeClamp R)) hCm (hCe R hR.le) hDi
  have hVm : Measurable V := measurable_pi_iff.mpr (fun i =>
    ((B.martingale i).adapted P B.F _ (changed_time_finite R hR.le)).mono (B.le _) le_rfl)
  obtain ⟨q,hqm,hqe,_,hqmap⟩ := conditional_pushforward_density P Q V hVm D hDi
    (ae_of_all _ (fun w => Real.exp_pos _)) hQD
  refine ⟨N,C,Q,hQp,hN,hNI,hCe,hQD,hmean,q,hqm,hqe,hqmap,?_⟩
  have hLm : Measurable (fun y : Fin d → ℝ => Real.exp (-K*(‖WithLp.toLp 2 y‖+2*Real.sqrt ((d:ℝ)*R))-K^2*R/2)) := by fun_prop
  apply (ae_map_iff hVm.aemeasurable (measurableSet_le hLm hqm)).2
  change ∀ᵐ w ∂P,Real.exp (-K*(‖WithLp.toLp 2 (V w)‖+2*Real.sqrt ((d:ℝ)*R))-K^2*R/2)≤P[D|MeasurableSpace.comap V inferInstance] w at hl
  rw [hqe] at hl
  exact hl

end Asakura.Chapter6

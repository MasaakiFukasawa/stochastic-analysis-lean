import Chapter4BrownianVariationIto
import Chapter3C2Composition
import Chapter3ItoVariationCovariance
import Chapter3OpenPathMeasurable

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The covariance chain rule for a C2 function of (W,Y), where Y has
continuous variation. No C3 regularity of the original flow is needed. -/
theorem martingale_variation_composition_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W Y A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hY : AdaptedLocalVariationWitness F Y)
    (hYc : ∀ w t,t<⊤ → ContinuousAt (fun s => Y s w) t)
    (hA : LocalCovarianceWitness P F W W A)
    (ψ : (Fin 2 → ℝ) → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n)) :
    ∃ B L C J : ClosedTime T → Ω → ℝ,
      SemimartingaleDecomposition P F (fun t w => ψ ![W t w,Y t w]) B L ∧
      LocalCovarianceWitness P F L W C ∧
      VariationIntegralFormula P c hc A
        (fun z => fderiv ℝ ψ ![W (realTimeClamp z.2) z.1,Y (realTimeClamp z.2) z.1] (Pi.single 0 1)) J ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → C t w=J t w) := by
  classical
  let XX : Fin 2 → ClosedTime T → Ω → ℝ := ![W,Y]
  let AA : Fin 2 → ClosedTime T → Ω → ℝ := ![(fun _ _ => 0),Y]
  let MM : Fin 2 → ClosedTime T → Ω → ℝ := ![W,(fun _ _ => 0)]
  let CC := fun (i j : Fin 2) => if i=0 ∧ j=0 then A else (fun _ _ => 0)
  have hx i : SemimartingaleDecomposition P F (XX i) (AA i) (MM i) := by
    fin_cases i
    · exact ⟨(by change AdaptedLocalVariationWitness F (fun _ _ => 0); simpa only [zero_mul] using hY.smul 0),
        hW,hW.path P F,fun _ _ _ => by simp [XX,AA,MM]⟩
    · exact ⟨hY,zero_local_process P hT F,hYc,fun _ _ _ => by simp [XX,AA,MM]⟩
  have hcv i j : LocalCovarianceWitness P F (MM i) (MM j) (CC i j) := by
    fin_cases i <;> fin_cases j
    · exact hA
    · exact (zero_covariance_left P hT F hF hle W).symm P F
    · exact zero_covariance_left P hT F hF hle W
    · exact zero_covariance_left P hT F hF hle _
  obtain ⟨B,L,N,hL,hN,hNI,heL⟩ := c2_composition_martingale_part P hT F hF hle hnull
    XX AA MM CC hx hcv ψ hψ c hc hcm hcT hcc
  have hvec t w : (fun i => XX i t w)=![W t w,Y t w] := by ext i; fin_cases i <;> rfl
  have hn1 := integral_against_zero_martingale P hT F hF hle hnull (N 1) _ (hN 1) (hNI 1)
  have heN : ∀ᵐ w ∂P,∀ t,t<⊤ → N 0 t w=L t w := by
    filter_upwards [heL,hn1] with w hw hnw
    intro t ht
    simpa only [Fin.sum_univ_two,hnw t ht,add_zero] using (hw t ht).symm
  let H := fun t w => fderiv ℝ ψ ![W t w,Y t w] (Pi.single 0 1)
  have hp : Continuous (fun z => fderiv ℝ ψ z (Pi.single 0 1)) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hHa t (ht : t<⊤) : Measurable[F t] (H t) := by
    apply hp.measurable.comp
    letI : MeasurableSpace Ω := F t
    apply Measurable.of_eval
    intro i
    fin_cases i
    · exact hW.adapted P F t ht
    · exact hY.adapted t ht
  have hHc w t (ht : t<⊤) : ContinuousAt (fun s => H s w) t := by
    apply hp.continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact hW.path P F w t ht
    · exact hYc w t ht
  have hAc w t (ht : t<⊤) : ContinuousAt (fun s => A s w) t := by
    have hh := ((hW.path P F w t ht).mul (hW.path P F w t ht)).sub (hA.defect.path P F w t ht)
    convert hh using 1
    funext s
    simp only [Pi.sub_apply,Pi.mul_apply,sub_sub_cancel]
  obtain ⟨J,hJv,hJc,hJ⟩ := continuous_adapted_variation_exists P F hF hnull c hc hcm hcT hcc
    A (covariance_adapted_variation P F hF hle hW hW hA) hAc
    (fun z => H (realTimeClamp z.2) z.1)
    (open_process_real_regularity F H hHa hHc).1 (open_process_real_regularity F H hHa hHc).2
  have hNI0 : ItoCovarianceFormula P F W (fun z => H (realTimeClamp z.2) z.1) (N 0) := by
    simpa only [hvec,MM,Matrix.cons_val_zero] using hNI 0
  obtain ⟨C,hC,heC⟩ := ito_covariance_identified_with_variation_integral P hT F W (N 0) W A J
    (hN 0) hW hA _ (fun w => open_path_real_measurable _ (hHc w)) hNI0 c hc hcT hcc hJc hJ
  refine ⟨B,L,C,J,?_,?_,hJ,heC⟩
  · simpa only [hvec] using hL
  · exact hC.congr_ae_processes P F hF hle (hN 0) hW hL.martingale hW heN
      (ae_of_all _ fun _ _ _ => rfl)

end Asakura.Chapter4

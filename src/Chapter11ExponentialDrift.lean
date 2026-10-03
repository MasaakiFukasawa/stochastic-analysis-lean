import Chapter11ExponentialIto
import Chapter6FiniteTimeDensity
import Chapter5BracketCommonTime
import Chapter3OpenPathMeasurable
import Chapter4FinitePathLift

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- Exponentiating a semimartingale whose drift and bracket have time
densities gives the actual stochastic equation. The densities may be merely
measurable: continuity is required only of the semimartingale paths. -/
theorem exponential_time_drift_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X A N C : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A N)
    (hC : LocalCovarianceWitness P F N N C)
    (b q : Ω × ℝ → ℝ) (hbm : ∀ w,Measurable (fun r => b (w,r)))
    (hqm : ∀ w,Measurable (fun r => q (w,r)))
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hbi : ∀ᵐ w ∂P,IntervalIntegrable (fun r => b (w,r)) volume 0 R)
    (hqi : ∀ᵐ w ∂P,IntervalIntegrable (fun r => q (w,r)) volume 0 R)
    (hAe : ∀ᵐ w ∂P,∀ r∈Icc 0 R,A (realTimeClamp r) w=A ⊥ w+∫ s in 0..r,b (w,s))
    (hCe : ∀ᵐ w ∂P,∀ r∈Icc 0 R,C (realTimeClamp r) w=∫ s in 0..r,q (w,s)) :
    ∃ L : ClosedTime T → Ω → ℝ,LocalMProcessWitness P F L ∧
      ItoCovarianceFormula P F N (fun z => Real.exp (X (realTimeClamp z.2) z.1)) L ∧
      ∀ t∈Icc 0 R,(fun w => Real.exp (X (realTimeClamp t) w))=ᵐ[P]
        fun w => Real.exp (X ⊥ w)+(∫ s in 0..t,Real.exp (X (realTimeClamp s) w)*(b (w,s)+q (w,s)/2))+L (realTimeClamp t) w := by
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨I,J,L,_,_,hL,hI,hJ,hLI,he⟩ := exponential_semimartingale_constructed P hT F hF hle hnull
    X A N C hX hC c hc hcm.monotone hcT hcc
  have hEa t (ht : t<⊤) : Measurable[F t] (fun w => Real.exp (X t w)) := by
    have hh : X t=(fun w => A t w+N t w) := funext (hX.decomposition t ht)
    rw [hh]
    exact ((hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)).exp
  have hEc w t ht : ContinuousAt (fun s => Real.exp (X s w)) t := Real.continuous_exp.continuousAt.comp (hX.continuous w t ht)
  have hEm w := open_path_real_measurable (fun t => Real.exp (X t w)) (hEc w)
  have hEcc := (open_process_real_regularity F _ hEa hEc).2
  refine ⟨L,hL,hLI,?_⟩
  intro t ht
  have htT := (EReal.coe_le_coe ht.2).trans_lt hRT
  have hbti : ∀ᵐ w ∂P,IntervalIntegrable (fun r => b (w,r)) volume 0 t :=
    hbi.mono (fun w hw => hw.mono_set (by simpa only [uIcc_of_le ht.1,uIcc_of_le hR] using Icc_subset_Icc_right ht.2))
  have hqti : ∀ᵐ w ∂P,IntervalIntegrable (fun r => q (w,r)) volume 0 t :=
    hqi.mono (fun w hw => hw.mono_set (by simpa only [uIcc_of_le ht.1,uIcc_of_le hR] using Icc_subset_Icc_right ht.2))
  have hi := finite_time_density_variation_integral P A I (A ⊥) b _ c (fun n => (hc n).le) hcT hcc
    t ht.1 htT (hAe.mono (fun w hw r hr => hw r (Icc_subset_Icc_right ht.2 hr))) hbm hbti hEm
    (hEcc t ht.1 htT) hI
  have hj := finite_time_density_variation_integral P C J (fun _ => 0) q _ c (fun n => (hc n).le) hcT hcc
    t ht.1 htT (hCe.mono (fun w hw r hr => by simpa only [zero_add] using hw r (Icc_subset_Icc_right ht.2 hr))) hqm hqti hEm
    (hEcc t ht.1 htT) hJ
  filter_upwards [he,hi,hj,hbti,hqti] with w he hi hj hbi hqi
  have hh := he _ (real_time_below t ht.1 htT)
  rw [hi,hj] at hh
  have his : IntervalIntegrable (fun r => Real.exp (X (realTimeClamp r) w)*b (w,r)) volume 0 t := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
    exact continuous_multiplier_integrable t ht.1 _
      ((ae_restrict_mem measurableSet_Ioc).mono fun r hr => ⟨hr.1.le,hr.2⟩) _ _
      (hEcc t ht.1 htT w) (hEm w) hbi.1
  have hjs : IntervalIntegrable (fun r => Real.exp (X (realTimeClamp r) w)*q (w,r)) volume 0 t := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
    exact continuous_multiplier_integrable t ht.1 _
      ((ae_restrict_mem measurableSet_Ioc).mono fun r hr => ⟨hr.1.le,hr.2⟩) _ _
      (hEcc t ht.1 htT w) (hEm w) hqi.1
  have hsum : (∫ s in 0..t,Real.exp (X (realTimeClamp s) w)*(b (w,s)+q (w,s)/2))=
      (∫ s in 0..t,Real.exp (X (realTimeClamp s) w)*b (w,s))+(∫ s in 0..t,Real.exp (X (realTimeClamp s) w)*q (w,s))/2 := by
    simp_rw [mul_add,←mul_div_assoc]
    rw [intervalIntegral.integral_add his (hjs.div_const 2),intervalIntegral.integral_div]
  rw [hsum]
  linarith

end Asakura.Chapter11

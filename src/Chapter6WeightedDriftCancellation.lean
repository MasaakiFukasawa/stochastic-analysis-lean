import Chapter3OpenPathMeasurable
import Chapter6SemimartingaleWeight
import Chapter6FiniteTimeDensity
import Chapter4FinitePathLift
import Chapter7ClockHalfTime

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Actual integration by parts cancels the alpha*Y drift on the finite
BSDE horizon. No weighted local-martingale identity is assumed. -/
theorem weighted_drift_cancellation {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (Y V M A : HalfClosedTime → Ω → ℝ) (hY : SemimartingaleDecomposition P F Y V M)
    (hA : AdaptedLocalVariationWitness F A) (hAc : ∀ w t,t<⊤ → ContinuousAt (fun s => A s w) t)
    (α φ : ℝ → Ω → ℝ) (hαc : ∀ w,Continuous (fun r => α r w)) (hφc : ∀ w,Continuous (fun r => φ r w))
    (R : ℝ) (hR : 0≤R)
    (hVeq : ∀ᵐ w ∂P,∀ r∈Icc 0 R,V (realTimeClamp r) w=V ⊥ w+∫ s in 0..r,-(φ s w+α s w*Y (realTimeClamp s) w))
    (hAeq : ∀ w r,r∈Icc 0 R → A (realTimeClamp r) w=A ⊥ w+∫ s in 0..r,α s w*A (realTimeClamp s) w)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := ⊤) (c n)) :
    ∃ N,LocalMProcessWitness P F N ∧
      ∀ r∈Icc 0 R,(fun w => Y (realTimeClamp r) w*A (realTimeClamp r) w+∫ s in 0..r,A (realTimeClamp s) w*φ s w)=ᵐ[P]
        fun w => Y ⊥ w*A ⊥ w+N (realTimeClamp r) w := by
  have hT : (0:EReal)<⊤ := by simp
  have hYa t (ht : t<⊤) : Measurable[F t] (Y t) := by
    have he : Y t=(fun w => V t w+M t w) := funext (hY.decomposition t ht)
    rw [he]; exact (hY.variation.adapted t ht).add (hY.martingale.adapted P F t ht)
  have hYm w : Measurable (fun r => Y (realTimeClamp r) w) :=
    open_path_real_measurable (fun t => Y t w) (hY.continuous w)
  have hAm w : Measurable (fun r => A (realTimeClamp r) w) :=
    open_path_real_measurable (fun t => A t w) (hAc w)
  have hYc w : ContinuousOn (fun r => Y (realTimeClamp r) w) (Icc 0 R) :=
    (open_process_real_regularity F Y hYa hY.continuous).2 R hR (EReal.coe_lt_top R) w
  have hArc w : ContinuousOn (fun r => A (realTimeClamp r) w) (Icc 0 R) :=
    (open_process_real_regularity F A hA.adapted hAc).2 R hR (EReal.coe_lt_top R) w
  obtain ⟨I,J,N,hN,hI,hJ,hprod⟩ := semimartingale_weight_constructed P hT F hF hle hnull Y V M A hY hA hAc
    c hc hcm (fun n => EReal.coe_lt_top _) hcc
  refine ⟨N,hN,?_⟩
  intro r hr
  have hsub : Icc 0 r⊆Icc 0 R := Icc_subset_Icc_right hr.2
  have hgc w : ContinuousOn (fun s => -(φ s w+α s w*Y (realTimeClamp s) w)) (Icc 0 r) :=
    ((hφc w).continuousOn.add ((hαc w).continuousOn.mul ((hYc w).mono hsub))).neg
  have hfc w : ContinuousOn (fun s => α s w*A (realTimeClamp s) w) (Icc 0 r) :=
    (hαc w).continuousOn.mul ((hArc w).mono hsub)
  have hi := finite_time_density_variation_integral P V I (V ⊥)
    (fun z => -(φ z.2 z.1+α z.2 z.1*Y (realTimeClamp z.2) z.1)) (fun z => A (realTimeClamp z.2) z.1)
    c hc (fun n => EReal.coe_lt_top _) hcc r hr.1 (EReal.coe_lt_top r)
    (hVeq.mono (fun w hw s hs => hw s (hsub hs)))
    (fun w => ((hφc w).measurable.add ((hαc w).measurable.mul (hYm w))).neg)
    (ae_of_all _ (fun w => (hgc w).intervalIntegrable_of_Icc hr.1))
    hAm (fun w => (hArc w).mono hsub) hI
  have hj := finite_time_density_variation_integral P A J (A ⊥)
    (fun z => α z.2 z.1*A (realTimeClamp z.2) z.1) (fun z => Y (realTimeClamp z.2) z.1)
    c hc (fun n => EReal.coe_lt_top _) hcc r hr.1 (EReal.coe_lt_top r)
    (ae_of_all _ (fun w s hs => hAeq w s (hsub hs)))
    (fun w => (hαc w).measurable.mul (hAm w))
    (ae_of_all _ (fun w => (hfc w).intervalIntegrable_of_Icc hr.1))
    hYm (fun w => (hYc w).mono hsub) hJ
  filter_upwards [hi,hj,hprod] with w hiw hjw hpw
  have hai : IntervalIntegrable (fun s => A (realTimeClamp s) w * -(φ s w+α s w*Y (realTimeClamp s) w)) volume 0 r :=
    (((hArc w).mono hsub).mul (hgc w)).intervalIntegrable_of_Icc hr.1
  have hbi : IntervalIntegrable (fun s => Y (realTimeClamp s) w*(α s w*A (realTimeClamp s) w)) volume 0 r :=
    (((hYc w).mono hsub).mul (hfc w)).intervalIntegrable_of_Icc hr.1
  have he : I (realTimeClamp r) w+J (realTimeClamp r) w= -(∫ s in 0..r,A (realTimeClamp s) w*φ s w) := by
    rw [hiw,hjw,← intervalIntegral.integral_add hai hbi,← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  have hh := hpw (realTimeClamp r) (real_time_below r hr.1 (EReal.coe_lt_top r))
  linarith

end Asakura.Chapter6

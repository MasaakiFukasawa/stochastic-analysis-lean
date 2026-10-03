import Chapter4C12Drift
import Chapter4VectorItoCovariance
import Chapter4StoppedCovarianceDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- The actual vector SDE gives the generator drift and local martingale
representation of a C1,2 function on a closed time strip. -/
theorem sde_drift_representation_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W : Fin noise → ClosedTime T → Ω → ℝ)
    (B : Fin noise → Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hB : ∀ j k,LocalCovarianceWitness P F (W j) (W k) (B j k))
    (hclock : ∀ j k w (r : ℝ),0≤r → (r:EReal)<T → B j k (realTimeClamp r) w=if j=k then r else 0)
    (X : ClosedTime T → Ω → Fin dim → ℝ) (ξ : Ω → Fin dim → ℝ)
    (hξ : Measurable[F ⊥] ξ)
    (G : Fin dim → ClosedTime T → Ω → ℝ)
    (H N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hGa : ∀ i t,t<⊤ → Measurable[F t] (G i t))
    (hGc : ∀ i w t,t<⊤ → ContinuousAt (fun s => G i s w) t)
    (hN : ∀ i j,LocalMProcessWitness P F (N i j))
    (hHa : ∀ i j t,t<⊤ → Measurable[F t] (H i j t))
    (hHc : ∀ i j w t,t<⊤ → ContinuousAt (fun s => H i j s w) t)
    (hNI : ∀ i j,ItoCovarianceFormula P F (W j) (fun z => H i j (realTimeClamp z.2) z.1) (N i j))
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (he : ∀ᵐ w ∂P,∀ r∈Icc 0 R,∀ i,X (realTimeClamp r) w i=
      ξ w i+(∫ s in 0..r,G i (realTimeClamp s) w)+∑ j,N i j (realTimeClamp r) w)
    (f : ℝ → (Fin dim → ℝ) → ℝ) (ft : ℝ × (Fin dim → ℝ) → ℝ)
    (hf : ∀ a,ContDiff ℝ 2 (f a))
    (hft : ∀ a x,HasDerivAt (fun s => f s x) (ft (a,x)) a)
    (hfc : Continuous (fun z : ℝ × (Fin dim → ℝ) => f z.1 z.2)) (hftc : Continuous ft)
    (hdxc : Continuous (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (f z.1) z.2))
    (hhc : Continuous (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (fderiv ℝ (f z.1)) z.2))
    (D : Ω × ℝ → ℝ)
    (hpde : ∀ᵐ w ∂P,∀ r∈Icc 0 R,ft (r,X (realTimeClamp r) w)+
      (∑ i,fderiv ℝ (f r) (X (realTimeClamp r) w) (Pi.single i 1)*G i (realTimeClamp r) w)+
      (∑ i,∑ l,fderiv ℝ (fderiv ℝ (f r)) (X (realTimeClamp r) w) (Pi.single i 1) (Pi.single l 1)*
        (∑ j,H i j (realTimeClamp r) w*H l j (realTimeClamp r) w))/2=D (w,r)) :
    ∃ Z : ClosedTime T → Ω → ℝ,LocalMProcessWitness P F Z ∧
      ∀ r∈Icc 0 R,(fun w => f r (X (realTimeClamp r) w))=ᵐ[P]
        fun w => f 0 (X ⊥ w)+Z (realTimeClamp r) w+∫ s in 0..r,D (w,s) := by
  classical
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  let M := fun i t w => ∑ j,N i j t w
  have hM i : LocalMProcessWitness P F (M i) :=
    local_martingale_finset_sum P hT F hF hle Finset.univ (N i) (fun j _ => hN i j)
  have hsemi i := finite_sde_semimartingale P hT F hF hle (fun t w => X t w i) (M i) (G i)
    (fun w => ξ w i) (measurable_pi_apply i |>.comp hξ) (hM i) (hGa i) (hGc i) R hR hRT
    (he.mono fun w hw r hr => hw r hr i)
  choose Y A hY hYc hYX hAB using hsemi
  obtain ⟨C,hC,hCG⟩ := vector_ito_covariance_density P hT F hF hle hnull W B hW hB hclock
    H N hN hHa hHc hNI c (fun n => (hc n).le) hcm.monotone hcT hcc
  let Q := fun i l (z : Ω × ℝ) => ∑ j,H i j (realTimeClamp z.2) z.1*H l j (realTimeClamp z.2) z.1
  let GG := fun i (z : Ω × ℝ) => (Iic R).indicator (fun r => G i (realTimeClamp r) z.1) z.2
  let QQ := fun i l (z : Ω × ℝ) => (Iic R).indicator (fun r => Q i l (z.1,r)) z.2
  have hGreal i n w : ContinuousOn (fun r => G i (realTimeClamp r) w) (Icc 0 (c n)) := by
    intro r hr
    exact ((hGc i w _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))).comp
      real_time_clamp_continuous.continuousAt).continuousWithinAt
  have hHreal i j n w : ContinuousOn (fun r => H i j (realTimeClamp r) w) (Icc 0 (c n)) := by
    intro r hr
    exact ((hHc i j w _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))).comp
      real_time_clamp_continuous.continuousAt).continuousWithinAt
  have hQreal i l n w : ContinuousOn (fun r => Q i l (w,r)) (Icc 0 (c n)) :=
    continuousOn_finset_sum Finset.univ (fun j _ => (hHreal i j n w).mul (hHreal l j n w))
  have hGGm i w : Measurable (fun r => GG i (w,r)) :=
    (open_path_real_measurable _ (hGc i w)).indicator measurableSet_Iic
  have hQQm i l w : Measurable (fun r => QQ i l (w,r)) :=
    (Finset.measurable_sum Finset.univ (fun j _ =>
      (open_path_real_measurable _ (hHc i j w)).mul (open_path_real_measurable _ (hHc l j w)))).indicator measurableSet_Iic
  have hGGi i n : ∀ᵐ w ∂P,IntervalIntegrable (fun r => GG i (w,r)) volume 0 (c n) := by
    apply ae_of_all
    intro w
    have hh := (hGreal i n w).intervalIntegrable_of_Icc (μ := volume) (hc n).le
    exact ⟨hh.1.indicator measurableSet_Iic,hh.2.indicator measurableSet_Iic⟩
  have hQQi i l n : ∀ᵐ w ∂P,IntervalIntegrable (fun r => QQ i l (w,r)) volume 0 (c n) := by
    apply ae_of_all
    intro w
    have hh := (hQreal i l n w).intervalIntegrable_of_Icc (μ := volume) (hc n).le
    exact ⟨hh.1.indicator measurableSet_Iic,hh.2.indicator measurableSet_Iic⟩
  have hstop : ∀ t,MeasurableSet[F t] {w : Ω | realTimeClamp (T := T) R≤t} := by
    intro t
    by_cases h : realTimeClamp (T := T) R≤t <;> simp [h]
  have hCs i l := (hC i l).stopped P F hF hle (fun _ => realTimeClamp R) hstop
  have hCsG i l n := stopped_covariance_density P (C i l) (Q i l) R hR (c n) (hc n).le (hCG i l n)
  have hYY : ∀ᵐ w ∂P,∀ r∈Icc 0 R,(fun i => Y i (realTimeClamp r) w)=X (realTimeClamp r) w := by
    filter_upwards [ae_all_iff.mpr hYX] with w hw
    intro r hr
    ext i
    simpa only [min_eq_right (real_time_clamp_mono hr.2)] using hw i (realTimeClamp r)
  have hp : ∀ᵐ w ∂P,∀ r∈Icc 0 R,ft (r,fun i => Y i (realTimeClamp r) w)+
      (∑ i,fderiv ℝ (f r) (fun k => Y k (realTimeClamp r) w) (Pi.single i 1)*GG i (w,r))+
      (∑ i,∑ l,fderiv ℝ (fderiv ℝ (f r)) (fun k => Y k (realTimeClamp r) w) (Pi.single i 1) (Pi.single l 1)*QQ i l (w,r))/2=D (w,r) := by
    filter_upwards [hpde,hYY] with w hw hyw
    intro r hr
    simp only [hyw r hr,GG,QQ,indicator_of_mem (show r∈Iic R from hr.2)]
    exact hw r hr
  obtain ⟨Z,hZ,hZe⟩ := c12_drift_local_representation P hT F hF hle hnull Y A
    (fun i t w => M i (min (realTimeClamp R) t) w) (fun i l t w => C i l (min (realTimeClamp R) t) w)
    hY hCs f ft hf hft hftc hdxc hhc R hR hRT c (fun n => (hc n).le) hcm.monotone hcT hcc
    GG QQ hGGm hGGi (fun i n => ae_of_all _ fun w r hr => hAB i w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n)))
    hQQm hQQi hCsG D hp
  have hz : realTimeClamp (T:=T) 0=⊥ := by
    apply Subtype.ext
    exact real_time_clamp_eq 0 le_rfl (le_of_lt hT)
  refine ⟨Z,hZ,?_⟩
  intro r hr
  filter_upwards [hZe r hr,hYY] with w hw hyw
  have hy0 := hyw 0 ⟨le_rfl,hR⟩
  simp only [hz] at hy0
  simpa only [hyw r hr,hy0] using hw

end Asakura.Chapter4

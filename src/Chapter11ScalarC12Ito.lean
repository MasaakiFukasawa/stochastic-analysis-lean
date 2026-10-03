import Chapter11ScalarC12Lift

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Scalar C1,2 Ito, reusing the proved time-dependent Ito formula. -/
theorem scalar_c12_density_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A M C : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A M)
    (hC : LocalCovarianceWitness P F M M C)
    (g : ℝ → ℝ → ℝ) (gt : ℝ × ℝ → ℝ)
    (hg : ∀ t,ContDiff ℝ 2 (g t)) (hgt : ∀ t x,HasDerivAt (fun s => g s x) (gt (t,x)) t)
    (hgc : Continuous (fun z : ℝ × ℝ => g z.1 z.2)) (hgtc : Continuous gt)
    (hdc : Continuous (fun z : ℝ × ℝ => deriv (g z.1) z.2))
    (hddc : Continuous (fun z : ℝ × ℝ => deriv (deriv (g z.1)) z.2))
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (b q : Ω × ℝ → ℝ) (hbm : ∀ w,Measurable (fun r => b (w,r)))
    (hqm : ∀ w,Measurable (fun r => q (w,r)))
    (hbi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => b (w,r)) volume 0 (c n))
    (hqi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => q (w,r)) volume 0 (c n))
    (hAe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),A (realTimeClamp r) w=A ⊥ w+∫ s in 0..r,b (w,s))
    (hCe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),C (realTimeClamp r) w=∫ s in 0..r,q (w,s)) :
    ∃ N : ClosedTime T → Ω → ℝ,LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F M
        (fun z => deriv (g (finitePrefixTime (T:=T) R hR (realTimeClamp z.2)).val) (X (realTimeClamp z.2) z.1)) N ∧
      ∀ r∈Icc 0 R,(fun w => g r (X (realTimeClamp r) w))=ᵐ[P]
        fun w => g 0 (X ⊥ w)+N (realTimeClamp r) w+
          (∫ s in 0..r,gt (s,X (realTimeClamp s) w))+
          (∫ s in 0..r,deriv (g s) (X (realTimeClamp s) w)*b (w,s))+
          (∫ s in 0..r,deriv (deriv (g s)) (X (realTimeClamp s) w)*q (w,s))/2 := by
  obtain ⟨hf,hft,_,hftc,hdxc,hhc⟩ := scalar_c12_lift_regular g gt hg hgt hgc hgtc hdc hddc
  obtain ⟨N,hN,hNI,_,he⟩ := c12_density_ito_constructed P hT F hF hle hnull
    (fun (_ : Fin 1) => X) (fun _ => A) (fun _ => M) (fun _ _ => C)
    (fun _ => hX) (fun _ _ => hC) (scalarC12Lift g) (fun z => gt (z.1,z.2 0))
    hf hft hftc hdxc hhc R hR hRT c hc hcm hcT hcc (fun _ => b) (fun _ _ => q)
    (fun _ => hbm) (fun _ => hbi) (fun _ => hAe) (fun _ _ => hqm) (fun _ _ => hqi) (fun _ _ => hCe)
  refine ⟨N 0,hN 0,?_,?_⟩
  · simpa only [scalar_c12_lift_first g hg,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply,Pi.single_eq_same,smul_eq_mul,mul_one] using hNI 0
  · intro r hr
    simpa only [Fin.sum_univ_one,scalarC12Lift,scalar_c12_lift_first g hg,
      scalar_c12_lift_second g hg,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply,ContinuousLinearMap.smulRight_apply,
      Pi.single_eq_same,smul_eq_mul,mul_one] using he r hr

end Asakura.Chapter11

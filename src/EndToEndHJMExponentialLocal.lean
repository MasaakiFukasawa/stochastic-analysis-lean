import EndToEndHJMRandomInitial
import EndToEndFiniteParameterExtension
open MeasureTheory Set Filter
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- The original bond price has the stochastic exponential representation;
only local bounds on the relevant finite maturity interval are needed. -/
theorem hjm_exponential_local_bounds {Ω:Type} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (U : ℝ) (hU : 0≤U) (f0:ℝ → Ω → ℝ) (hf0:∀w,IntegrableOn (fun x => f0 x w) (Ioc 0 U) volume)
    (hinit:Measurable[B.F ⊥] (fun w => ∫x in Ioc 0 U,f0 x w))
    (a:ℝ × (Ω × ℝ) → ℝ) (σ:Fin d → ℝ × (Ω × ℝ) → ℝ)
    (ham:Measurable a) (hσm:∀i,Measurable (σ i))
    (hap:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:ℝ × (Ω × Icc (0:ℝ) b) => a (z.1,(z.2.1,z.2.2.val))))
    (hσp:∀i b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:ℝ × (Ω × Icc (0:ℝ) b) => σ i (z.1,(z.2.1,z.2.2.val))))
    (hab:∀w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀r∈Icc 0 b, |a (x,(w,r))|≤K)
    (hσb:∀i w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀r∈Icc 0 b, |σ i (x,(w,r))|≤K)
    (N : Fin d → ℝ → HalfClosedTime → Ω → ℝ)
    (hNm : ∀i,Measurable (fun z:ℝ × (Ω × HalfClosedTime) => N i z.1 z.2.2 z.2.1))
    (hN : ∀i x,LocalMProcessWitness P B.F (N i x))
    (hNI : ∀i,∀ᵐx∂volume.restrict (Ioc 0 U),
      ItoCovarianceFormula P B.F (B.W i) (fun z => -σ i (x,z)) (N i x)) :
    let Price := fun (t : HalfClosedTime) w => Real.exp (-(∫x in Ioc 0 U,f0 x w+
      (∫s in 0..(t:EReal).toReal,a (x,(w,s)))-∑i,N i x t w))
    LocalMProcessWitness P B.F (fun t w => Price t w-Price ⊥ w) →
      ∃ M : Fin d → HalfClosedTime → Ω → ℝ,
        (∀ i,LocalMProcessWitness P B.F (M i)) ∧
        (∀ i,ItoCovarianceFormula P B.F (B.W i)
          (fun z => -(∫x in Ioc 0 U,σ i (x,z))) (M i)) ∧
        ∀ r,0≤r → Price (realTimeClamp r)=ᵐ[P]
          (fun w => Real.exp (-(∫x in Ioc 0 U,f0 x w))*Real.exp
            (-(∫s in 0..r,∑i,(∫x in Ioc 0 U,σ i (x,(w,s)))^2)/2+
              ∑i,M i (realTimeClamp r) w)) := by
  classical
  intro Price hPrice
  let a' := fun z : ℝ × (Ω × ℝ) => @ite ℝ (z.1∈Icc 0 U) (Classical.propDecidable _) (a z) 0
  let σ' := fun i (z : ℝ × (Ω × ℝ)) => @ite ℝ (z.1∈Icc 0 U) (Classical.propDecidable _) (σ i z) 0
  obtain ⟨ham',hap',hab',ha⟩ := finite_parameter_extension B.F (Icc 0 U) measurableSet_Icc a ham hap hab
  have hσ i := finite_parameter_extension B.F (Icc 0 U) measurableSet_Icc (σ i) (hσm i) (hσp i) (hσb i)
  have hni i : ∀ᵐx∂volume.restrict (Ioc 0 U),
      ItoCovarianceFormula P B.F (B.W i) (fun z => -σ' i (x,z)) (N i x) := by
    filter_upwards [hNI i,ae_restrict_mem measurableSet_Ioc] with x hx hxi
    simpa only [σ',if_pos (show x∈Icc 0 U from ⟨hxi.1.le,hxi.2⟩)] using hx
  let Price' := fun (t:HalfClosedTime) w => Real.exp (-(∫x in Ioc 0 U,f0 x w+
    (∫s in 0..(t:EReal).toReal,a' (x,(w,s)))-∑i,N i x t w))
  have he t w : Price' t w=Price t w := by
    apply congrArg (fun x : ℝ => Real.exp (-x))
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    simp only [a',if_pos (show x∈Icc 0 U from ⟨hx.1.le,hx.2⟩)]
  have hp : LocalMProcessWitness P B.F (fun t w => Price' t w-Price' ⊥ w) := by
    convert hPrice using 1
    funext t w
    rw [he t w,he ⊥ w]
  obtain ⟨M,hM,hMI,_,hE⟩ := hjm_exponential_random_initial P B (volume.restrict (Ioc 0 U)) f0 hf0 hinit
    a' σ' (by simpa only [a'] using ham') (fun i => by simpa only [σ'] using (hσ i).1)
    (by simpa only [a'] using hap') (fun i => by simpa only [σ'] using (hσ i).2.1)
    (by simpa only [a'] using hab') (fun i => by simpa only [σ'] using (hσ i).2.2.1)
    N hN hni hNm hp
  have hi i z : (∫x in Ioc 0 U,σ' i (x,z))=(∫x in Ioc 0 U,σ i (x,z)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    simp only [σ',if_pos (show x∈Icc 0 U from ⟨hx.1.le,hx.2⟩)]
  refine ⟨M,hM,?_,?_⟩
  · intro i
    simpa only [hi] using hMI i
  · intro r hr
    have hh := hE r hr
    change Price' (realTimeClamp r)=ᵐ[P] _ at hh
    filter_upwards [hh] with w hw
    simpa only [he,hi] using hw

#print axioms hjm_exponential_local_bounds
end Asakura.EndToEnd

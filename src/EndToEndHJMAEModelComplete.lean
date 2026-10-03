import EndToEndHJMAEGlobal
import EndToEndHJMExponentialLocal

open MeasureTheory Set Filter
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The HJM drift and bond-price exponential, for the original forward rates,
with random initial curve and almost-everywhere local coefficient bounds. -/
theorem hjm_global_ae_model {Ω:Type} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (f0:ℝ → Ω → ℝ) (hf0:∀U:ℝ,0≤U → ∀w,IntegrableOn (fun x => f0 x w) (Ioc 0 U) volume)
    (hinit:∀u:ℝ,0≤u → Measurable[B.F ⊥] (fun w => ∫x in Ioc 0 u,f0 x w))
    (a:ℝ × (Ω × ℝ) → ℝ) (σ:Fin d → ℝ × (Ω × ℝ) → ℝ)
    (ham:Measurable a) (hσm:∀i,Measurable (σ i))
    (hap:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:ℝ × (Ω × Icc (0:ℝ) b) => a (z.1,(z.2.1,z.2.2.val))))
    (hσp:∀i b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:ℝ × (Ω × Icc (0:ℝ) b) => σ i (z.1,(z.2.1,z.2.2.val))))
    (hab:∀ᵐw∂P,∀U,0≤U → ∀b,0≤b → ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀r∈Icc 0 b, |a (x,(w,r))|≤K)
    (hσb:∀i,∀ᵐw∂P,∀U,0≤U → ∀b,0≤b → ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀r∈Icc 0 b, |σ i (x,(w,r))|≤K)
    (N : Fin d → ℝ → HalfClosedTime → Ω → ℝ)
    (hNm : ∀i,Measurable (fun z:ℝ × (Ω × HalfClosedTime) => N i z.1 z.2.2 z.2.1))
    (hN : ∀i x,LocalMProcessWitness P B.F (N i x))
    (hNI : ∀i,∀ᵐx∂volume,0<x →
      ItoCovarianceFormula P B.F (B.W i) (fun z => -σ i (x,z)) (N i x)) :
      (let Price := fun u (t : HalfClosedTime) w => Real.exp (-(∫x in Ioc 0 u,f0 x w+
        (∫s in 0..(t:EReal).toReal,a (x,(w,s)))-∑i,N i x t w))
       (∀ u,0≤u → LocalMProcessWitness P B.F (fun t w => Price u t w-Price u ⊥ w)) →
       (∀ᵐ w ∂P,∀ᵐ r ∂volume,0<r → ∀ᵐ u ∂volume,0<u →
         a (u,(w,r))=∑i,σ i (u,(w,r))*(∫s in 0..u,σ i (s,(w,r)))) ∧
       ∀ U,0≤U → ∃ M : Fin d → HalfClosedTime → Ω → ℝ,
         (∀ i,LocalMProcessWitness P B.F (M i)) ∧
         (∀ i,ItoCovarianceFormula P B.F (B.W i)
           (fun z => -(∫x in Ioc 0 U,σ i (x,z))) (M i)) ∧
         ∀ r,0≤r → Price U (realTimeClamp r)=ᵐ[P]
           (fun w => Real.exp (-(∫x in Ioc 0 U,f0 x w))*Real.exp
             (-(∫s in 0..r,∑i,(∫x in Ioc 0 U,σ i (x,(w,s)))^2)/2+
               ∑i,M i (realTimeClamp r) w))) := by
  classical
  intro Price hPrice
  let Good := fun w => (∀U,0≤U → ∀b,0≤b → ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀r∈Icc 0 b,|a (x,(w,r))|≤K) ∧
    (∀i,∀U,0≤U → ∀b,0≤b → ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀r∈Icc 0 b,|σ i (x,(w,r))|≤K)
  have hg : ∀ᵐw∂P,Good w := by
    filter_upwards [hab,ae_all_iff.mpr hσb] with w hw hs
    exact ⟨hw,hs⟩
  let E := toMeasurable P {w | ¬Good w}
  have hEm : MeasurableSet E := measurableSet_toMeasurable P _
  have hE0 : P E=0 := (measure_toMeasurable (μ:=P) _).trans (ae_iff.mp hg)
  have he : ∀ᵐw∂P,w∉E := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hE0
  have hgood w (hw:w∉E) : Good w := by
    by_contra hn
    exact hw (subset_toMeasurable P _ hn)
  let a' := fun z:ℝ × (Ω × ℝ) => @ite ℝ (z.2.1∈E) (Classical.propDecidable _) 0 (a z)
  let σ' := fun i (z:ℝ × (Ω × ℝ)) => @ite ℝ (z.2.1∈E) (Classical.propDecidable _) 0 (σ i z)
  let N' := fun i x t w => @ite ℝ (w∈E) (Classical.propDecidable _) 0 (N i x t w)
  obtain ⟨ham',hap'⟩ := coefficient_null_mask P B E hEm hE0 a ham hap
  have hs i := coefficient_null_mask P B E hEm hE0 (σ i) (hσm i) (hσp i)
  have hab' w U (hU:0≤U) b (hb:0≤b) : ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀r∈Icc 0 b,|a' (x,(w,r))|≤K := by
    by_cases hw:w∈E
    · exact ⟨0,le_rfl,fun _ _ _ _ => by simp only [a',if_pos hw,abs_zero,le_refl]⟩
    · simpa only [a',if_neg hw] using (hgood w hw).1 U hU b hb
  have hsb' i w U (hU:0≤U) b (hb:0≤b) : ∃K:ℝ,0≤K ∧ ∀x∈Icc 0 U,∀r∈Icc 0 b,|σ' i (x,(w,r))|≤K := by
    by_cases hw:w∈E
    · exact ⟨0,le_rfl,fun _ _ _ _ => by simp only [σ',if_pos hw,abs_zero,le_refl]⟩
    · simpa only [σ',if_neg hw] using (hgood w hw).2 i U hU b hb
  have hN' i x : LocalMProcessWitness P B.F (N' i x) := local_martingale_null_mask P B E hEm hE0 (N i x) (hN i x)
  have hNm' i : Measurable (fun z:ℝ × (Ω × HalfClosedTime) => N' i z.1 z.2.2 z.2.1) :=
    measurable_const.ite (hEm.preimage (measurable_fst.comp measurable_snd)) (hNm i)
  have hNI' i : ∀ᵐx∂volume,0<x → ItoCovarianceFormula P B.F (B.W i) (fun z => -σ' i (x,z)) (N' i x) := by
    filter_upwards [hNI i] with x hx hxp
    have hi := ito_null_mask P B E hEm hE0 i (fun z => -σ i (x,z)) (N i x) (hN i x) (hx hxp)
    convert hi using 1
    funext z
    dsimp only [σ']
    split_ifs <;> simp
  let Price' := fun u (t:HalfClosedTime) w => Real.exp (-(∫x in Ioc 0 u,f0 x w+
    (∫s in 0..(t:EReal).toReal,a' (x,(w,s)))-∑i,N' i x t w))
  have hp u (hu:0≤u) : LocalMProcessWitness P B.F (fun t w => Price' u t w-Price' u ⊥ w) := by
    convert local_martingale_null_mask P B E hEm hE0 _ (hPrice u hu) using 1
    funext t w
    by_cases hw:w∈E
    · simp only [Price',a',N',if_pos hw,intervalIntegral.integral_zero,Finset.sum_const_zero,add_zero,sub_zero,sub_self]
    · simp only [Price',Price,a',N',if_neg hw]
  have hd := hjm_global_random_drift P B f0 hf0 hinit a' σ' ham' (fun i => (hs i).1)
    hap' (fun i => (hs i).2) hab' hsb' N' hNm' hN' hNI' hp
  refine ⟨?_,?_⟩
  · filter_upwards [hd,he] with w hw hwe
    simpa only [a',σ',if_neg hwe] using hw
  · intro U hU
    obtain ⟨M,hM,hMI,hExp⟩ := hjm_exponential_local_bounds P B U hU f0 (hf0 U hU) (hinit U hU)
      a' σ' ham' (fun i => (hs i).1) hap' (fun i => (hs i).2)
      (fun w => hab' w U hU) (fun i w => hsb' i w U hU)
      N' hNm' hN' (fun i => (ae_restrict_iff' measurableSet_Ioc).mpr ((hNI' i).mono (fun x hx hxi => hx hxi.1))) (hp U hU)
    refine ⟨M,hM,?_,?_⟩
    · intro i
      apply Asakura.Chapter7.ito_integrand_common_ae P B.F (B.W i) (M i)
        (fun z => -(∫x in Ioc 0 U,σ' i (x,z))) _ (hMI i)
      filter_upwards [he] with w hw
      intro r
      simp only [σ',if_neg hw]
    · intro r hr
      filter_upwards [hExp r hr,he] with w hw hwe
      simpa only [Price',Price,a',σ',N',if_neg hwe] using hw

#print axioms hjm_global_ae_model
end Asakura.EndToEnd

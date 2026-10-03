import Chapter13CheyetteConstruction
import Chapter13CheyetteSemimartingale

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- Raw locally bounded progressive matrix coefficients construct the
Cheyette semimartingale state and its bracket, as well as the state formula.
No semimartingale decomposition or covariance identity is an input. -/
theorem cheyette_model_constructed {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {n d:ℕ} (B:BrownianSystem P d)
    (S:Fin n → Fin d → Ω × ℝ → ℝ) (hm:∀i j,Measurable (S i j))
    (hp:∀i j b,0<b → @Measurable _ _
      (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) b => S i j (z.1,z.2.val)))
    (hb:∀i j w b,0≤b → ∃K:ℝ,0≤K ∧ ∀r∈Icc 0 b,|S i j (w,r)|≤K)
    (g:Fin n → ℝ → ℝ) (hgm:∀k,Measurable (g k))
    (hg:∀k t,0≤t → IntervalIntegrable (g k) volume 0 t) (R:ℝ) (hR:0<R) :
    let A := fun i k w r => ∑j,S i j (w,r)*S k j (w,r)
    let Y := fun i k w t => ∫r in 0..t,A i k w r
    ∃(N:Fin n → Fin d → HalfClosedTime → Ω → ℝ) (X D:Fin n → HalfClosedTime → Ω → ℝ),
      (∀i j,ItoCovarianceFormula P B.F (B.W j) (S i j) (N i j)) ∧
      (∀i,SemimartingaleDecomposition P B.F (X i) (D i) (fun t w => ∑j,N i j t w)) ∧
      (∀i k,∃C,LocalCovarianceWitness P B.F (fun t w => ∑j,N i j t w) (fun t w => ∑j,N k j t w) C ∧
        ∀t,0≤t → C (realTimeClamp t)=ᵐ[P] (fun w => Y i k w t)) ∧
      (∀i t w,X i t w=(∑k,∫r in 0..(finitePrefixTime R hR.le t).val,Y i k w r*g k r)+∑j,N i j t w) ∧
      ∀w t,t∈Icc 0 R → ∀v K:Fin n → ℝ,
        (∑i,v i*((∑k,∫u in 0..t,A i k w u*(K k-∫s in 0..u,g k s))+∑j,N i j (realTimeClamp t) w))=
          (∑i,∑k,v i*Y i k w t*(K k-∫s in 0..t,g k s))+∑i,v i*X i (realTimeClamp t) w := by
  intro A Y
  obtain ⟨N,hN,hNI,hNC,hformula⟩:=cheyette_state_constructed P B S hm hp hb g hg
  have hNs i:LocalMProcessWitness P B.F (fun t w => ∑j,N i j t w) :=
    local_process_finset_sum P B.F B.mono B.le Finset.univ (N i) (fun j _ => hN i j)
      (zero_local_process P (by simp) B.F)
  have hi i j:=bounded_coefficient_square (S i j) (hm i j) (hb i j)
  have hA i k w:IntervalIntegrable (A i k w) volume 0 R := by
    have hh j:=square_integrable_product _ _ 0 R
      ((hm i j).comp (measurable_const.prodMk measurable_id))
      ((hm k j).comp (measurable_const.prodMk measurable_id)) (hi i j w R hR.le) (hi k j w R hR.le)
    simpa only [A,Finset.sum_fn,Finset.sum_apply,Function.comp_apply,id_eq] using IntervalIntegrable.sum Finset.univ (fun j _ => hh j)
  have hAp i k:@Measurable _ _ (progressiveSpace (fun t:Icc (0:ℝ) R => B.F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) R => A i k z.1 z.2.val) :=
    Finset.measurable_sum _ (fun j _ => (hp i j R hR).mul (hp k j R hR))
  obtain ⟨X,D,hX,hXe⟩:=cheyette_state_semimartingale P B.F B.mono B.le R hR.le
    (fun i k z => A i k z.1 z.2) hAp hA g hgm (fun k => hg k R hR.le) _ hNs
  refine ⟨N,X,D,hNI,hX,hNC,hXe,?_⟩
  intro w t ht v K
  have he:=hformula w t ht.1 v K
  have htime:(finitePrefixTime (T:=(⊤:EReal)) R hR.le (realTimeClamp t)).val=t := by
    rw [finite_prefix_time_of_real R t hR.le ht le_top]
  simpa only [hXe,htime] using he
end Asakura.Chapter13
#print axioms Asakura.Chapter13.cheyette_model_constructed

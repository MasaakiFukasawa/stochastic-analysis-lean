import Chapter13BoundedCoefficient
import Chapter13CheyetteState

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Construction of the Cheyette noise, covariance primitive and state
formula from the original matrix coefficient. All time integrability inputs
are derived from local bounds on that coefficient. -/
theorem cheyette_state_constructed {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {n d:ℕ} (B:BrownianSystem P d)
    (S:Fin n → Fin d → Ω × ℝ → ℝ) (hm:∀i j,Measurable (S i j))
    (hp:∀i j b,0<b → @Measurable _ _
      (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) b => S i j (z.1,z.2.val)))
    (hb:∀i j w b,0≤b → ∃K:ℝ,0≤K ∧ ∀r∈Icc 0 b,|S i j (w,r)|≤K)
    (g:Fin n → ℝ → ℝ) (hg:∀j t,0≤t → IntervalIntegrable (g j) volume 0 t) :
    let A := fun i k w r => ∑j,S i j (w,r)*S k j (w,r)
    let Y := fun i k w t => ∫r in 0..t,A i k w r
    ∃N:Fin n → Fin d → HalfClosedTime → Ω → ℝ,
      (∀i j,LocalMProcessWitness P B.F (N i j)) ∧
      (∀i j,ItoCovarianceFormula P B.F (B.W j) (S i j) (N i j)) ∧
      (∀i k,∃C,LocalCovarianceWitness P B.F (fun t w => ∑j,N i j t w) (fun t w => ∑j,N k j t w) C ∧
        ∀t,0≤t → C (realTimeClamp t)=ᵐ[P] (fun w => Y i k w t)) ∧
      ∀w t,0≤t → ∀v K:Fin n → ℝ,
        let X := fun i => (∑k,∫u in 0..t,Y i k w u*g k u)+∑j,N i j (realTimeClamp t) w
        (∑i,v i*((∑k,∫u in 0..t,A i k w u*(K k-∫s in 0..u,g k s))+∑j,N i j (realTimeClamp t) w))=
          (∑i,∑k,v i*Y i k w t*(K k-∫s in 0..t,g k s))+∑i,v i*X i := by
  intro A Y
  have hi i j:=bounded_coefficient_square (S i j) (hm i j) (hb i j)
  obtain ⟨N,hN,hNI,hNC⟩:=matrix_noise_constructed P B S hm hp hi
  refine ⟨N,hN,hNI,hNC,?_⟩
  intro w t ht v K X
  have hA i k:IntervalIntegrable (A i k w) volume 0 t := by
    have hh j := square_integrable_product _ _ 0 t
      ((hm i j).comp (measurable_const.prodMk measurable_id))
      ((hm k j).comp (measurable_const.prodMk measurable_id)) (hi i j w t ht) (hi k j w t ht)
    simpa only [A,Finset.sum_fn,Finset.sum_apply,Function.comp_apply,id_eq] using IntervalIntegrable.sum Finset.univ (fun j _ => hh j)
  exact cheyette_state_kernel (fun i k => A i k w) g v K
    (fun i => ∑j,N i j (realTimeClamp t) w) 0 t hA (fun k => hg k t ht)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.cheyette_state_constructed

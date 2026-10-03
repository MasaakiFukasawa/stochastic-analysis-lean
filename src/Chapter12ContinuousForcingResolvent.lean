import Chapter12FundamentalInversePair
import Chapter10LinearPathUniqueness

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem continuous_forcing_resolvent_solves {E:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A J Q:ℝ → E →L[ℝ] E) (hcA:Continuous A) (hcJ:Continuous J) (hcQ:Continuous Q)
    (T:ℝ) (hT:0≤T) (hdJ:∀t∈Icc 0 T,HasDerivAt J (A t*J t) t)
    (hJQ:∀t∈Icc 0 T,J t*Q t=1) (R:ℝ → E) (hcR:Continuous R) :
    let X := fun t => R t+J t (∫s in 0..t,Q s (A s (R s)))
    ∀t∈Icc 0 T,X t=R t+∫s in 0..t,A s (X s) := by
  intro X t ht
  let f := fun s => Q s (A s (R s))
  let I := fun t => ∫s in 0..t,f s
  let Y := fun t => J t (I t)
  have hfc:Continuous f := hcQ.clm_apply (hcA.clm_apply hcR)
  have hIc:Continuous I := (intervalIntegral.differentiable_integral_of_continuous hfc).continuous
  have hYc:Continuous Y := hcJ.clm_apply hIc
  have hd s (hs:s∈uIcc (0:ℝ) t):HasDerivAt Y (A s (X s)) s := by
    have hs':s∈Icc 0 T := by rw [uIcc_of_le ht.1] at hs;exact ⟨hs.1,hs.2.trans ht.2⟩
    have hi:HasDerivAt I (f s) s := intervalIntegral.integral_hasDerivAt_right
      (hfc.intervalIntegrable 0 s) hfc.aestronglyMeasurable.stronglyMeasurableAtFilter hfc.continuousAt
    have hh := (hdJ s hs').clm_apply hi
    have he:J s (Q s (A s (R s)))=A s (R s) := by
      change (J s*Q s) (A s (R s))=_
      rw [hJQ s hs']
      rfl
    convert hh using 1
    change A s (R s+J s (I s))=A s (J s (I s))+J s (Q s (A s (R s)))
    rw [map_add,he,add_comm]
  have hc:Continuous (fun s => A s (X s)) := hcA.clm_apply (hcR.add hYc)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 t)
  have hY0:Y 0=0 := by simp [Y,I]
  rw [hY0,sub_zero] at he
  change R t+Y t=R t+_
  rw [he]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.continuous_forcing_resolvent_solves

import Chapter12FundamentalInversePair

open MeasureTheory Set
open scoped Topology NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem fundamental_transition_inverse_bound {E:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (A J Q:ℝ → E →L[ℝ] E) (hcJ:Continuous J) (K:ℝ≥0) (hb:∀r,‖A r‖≤(K:ℝ))
    (T:ℝ) (hdJ:∀t∈Icc 0 T,HasDerivAt J (A t*J t) t)
    (hJQ:∀t∈Icc 0 T,J t*Q t=1) (s:ℝ) (hs:s∈Icc 0 T) :
    ∃e:E ≃L[ℝ] E,e.toContinuousLinearMap=J T*Q s ∧
      ‖e.symm.toContinuousLinearMap‖≤Real.exp ((K:ℝ)*(T-s)) := by
  let L := fun r => (J (s+r)).comp (Q s)
  have hcL:Continuous L := (hcJ.comp (continuous_const.add continuous_id)).clm_comp continuous_const
  have hL0:L 0=1 := by simpa [L,ContinuousLinearMap.mul_def] using hJQ s hs
  have hd r (hr:r∈Ioc 0 (T-s)):HasDerivAt L (A (s+r)*L r) r := by
    have ht:s+r∈Icc 0 T := ⟨by linarith [hs.1,hr.1],by linarith [hr.2]⟩
    have hh := ((hdJ (s+r) ht).scomp r ((hasDerivAt_id r).const_add s)).clm_comp
      (hasDerivAt_const r (Q s))
    simpa only [L,Function.comp_def,one_smul,ContinuousLinearMap.comp_zero,add_zero,ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_assoc] using hh
  obtain ⟨e,he,hb⟩ := variational_flow_equiv_with_inverse_bound L (fun r => A (s+r))
    (T-s) (K:ℝ) (sub_nonneg.mpr hs.2) hcL hL0 hd (fun r _ => hb (s+r))
  refine ⟨e,?_,hb⟩
  simpa [L,ContinuousLinearMap.mul_def] using he

theorem fundamental_transition_integral {E:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A J Q:ℝ → E →L[ℝ] E) (hcA:Continuous A) (hcQ:Continuous Q)
    (T:ℝ) (hdQ:∀t∈Icc 0 T,HasDerivAt Q (-(Q t*A t)) t)
    (hT:J T*Q T=1) (s:ℝ) (hs:s∈Icc 0 T) :
    J T*Q s=1+∫r in s..T,J T*(Q r*A r) := by
  let f := fun r => (J T).comp (Q r)
  let g := fun r => (J T).comp ((Q r).comp (A r))
  have hg:Continuous g := continuous_const.clm_comp (hcQ.clm_comp hcA)
  have hd r (hr:r∈uIcc s T):HasDerivAt f (-(g r)) r := by
    have hr':r∈Icc 0 T := by rw [uIcc_of_le hs.2] at hr;exact ⟨hs.1.trans hr.1,hr.2⟩
    have hh := (hasDerivAt_const r (J T)).clm_comp (hdQ r hr')
    simpa only [f,g,ContinuousLinearMap.zero_comp,zero_add,ContinuousLinearMap.comp_neg,ContinuousLinearMap.mul_def] using hh
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hg.neg.intervalIntegrable s T)
  rw [intervalIntegral.integral_neg] at he
  change -(∫r in s..T,g r)=J T*Q T-J T*Q s at he
  rw [hT] at he
  change J T*Q s=1+∫r in s..T,g r
  apply (sub_eq_zero.mp ?_)
  rw [sub_add_eq_sub_sub,←neg_sub 1 (J T*Q s),←he,neg_neg,sub_self]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.fundamental_transition_inverse_bound
#print axioms Asakura.Chapter12.fundamental_transition_integral

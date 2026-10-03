import Chapter12ConstructedVariationalInverse

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem fundamental_inverse_pair {E:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (A:ℝ → E →L[ℝ] E) (hcA:Continuous A) (K:ℝ≥0) (hb:∀t,‖A t‖≤(K:ℝ))
    (T:ℝ) (hT:0≤T) :
    ∃J Q:ℝ → E →L[ℝ] E,Continuous J ∧ Continuous Q ∧ J 0=1 ∧ Q 0=1 ∧
      (∀t∈Icc 0 T,HasDerivAt J (A t*J t) t) ∧
      (∀t∈Icc 0 T,HasDerivAt Q (-(Q t*A t)) t) ∧
      (∀t∈Icc 0 T,Q t*J t=1 ∧ J t*Q t=1) := by
  obtain ⟨J₀,hJ₀c,hJ₀⟩ := Asakura.Chapter8.variational_operator_exists (T+1) (by linarith) A hcA K hb
  have hFc:Continuous (fun p:ℝ×(E →L[ℝ] E) => -(p.2*A p.1)) :=
    (continuous_snd.mul (hcA.comp continuous_fst)).neg
  have hLip t:LipschitzWith K (fun Q:E →L[ℝ] E => -(Q*A t)) := by
    apply LipschitzWith.of_dist_le_mul
    intro Q R
    rw [dist_neg_neg,dist_eq_norm,dist_eq_norm,←sub_mul]
    exact (norm_mul_le _ _).trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb t) (norm_nonneg (Q-R)))
  obtain ⟨Q₀,hQ₀c,hQ₀⟩ := Asakura.Chapter8.forced_integral_equation_exists (T+1) (by linarith) K
    (fun t (Q:E →L[ℝ] E) => -(Q*A t)) hFc hLip (fun _ => 1) continuous_const
  let J := fun t => (1:E →L[ℝ] E)+∫s in 0..t,A s*J₀ s
  let Q := fun t => (1:E →L[ℝ] E)+∫s in 0..t,-(Q₀ s*A s)
  have hcJ:Continuous J := continuous_const.add (intervalIntegral.differentiable_integral_of_continuous (hcA.mul hJ₀c)).continuous
  have hcQ:Continuous Q := continuous_const.add (intervalIntegral.differentiable_integral_of_continuous (hQ₀c.mul hcA).neg).continuous
  have heJ t (ht:t∈Icc 0 T):J t=J₀ t := by
    ext v
    change v+(∫s in 0..t,A s*J₀ s) v=J₀ t v
    rw [ContinuousLinearMap.intervalIntegral_apply (φ:=fun s => A s*J₀ s) ((hcA.mul hJ₀c).intervalIntegrable _ _)]
    exact (hJ₀ t ⟨ht.1,by linarith [ht.2]⟩ v).symm
  have heQ t (ht:t∈Icc 0 T):Q t=Q₀ t := (hQ₀ t ⟨ht.1,by linarith [ht.2]⟩).symm
  have hJ0:J 0=1 := by simp [J]
  have hQ0:Q 0=1 := by simp [Q]
  have hdJ t (ht:t∈Icc 0 T):HasDerivAt J (A t*J t) t := by
    rw [heJ t ht]
    exact (intervalIntegral.integral_hasDerivAt_right ((hcA.mul hJ₀c).intervalIntegrable 0 t)
      (hcA.mul hJ₀c).aestronglyMeasurable.stronglyMeasurableAtFilter (hcA.mul hJ₀c).continuousAt).const_add 1
  have hdQ t (ht:t∈Icc 0 T):HasDerivAt Q (-(Q t*A t)) t := by
    rw [heQ t ht]
    exact (intervalIntegral.integral_hasDerivAt_right ((hQ₀c.mul hcA).neg.intervalIntegrable 0 t)
      (hQ₀c.mul hcA).neg.aestronglyMeasurable.stronglyMeasurableAtFilter (hQ₀c.mul hcA).neg.continuousAt).const_add 1
  refine ⟨J,Q,hcJ,hcQ,hJ0,hQ0,hdJ,hdQ,?_⟩
  intro t ht
  have hd s (hs:s∈uIcc (0:ℝ) t):HasDerivAt (fun r => Q r*J r) 0 s := by
    have hs':s∈Icc 0 T := by rw [uIcc_of_le ht.1] at hs;exact ⟨hs.1,hs.2.trans ht.2⟩
    have hh := (hdQ s hs').clm_comp (hdJ s hs')
    have hz : (-(Q s*A s)).comp (J s)+(Q s).comp (A s*J s)=0 := by
      ext v
      simp
    rw [hz] at hh
    exact hh
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (intervalIntegrable_const (a:=0) (b:=t) (c:=(0:E →L[ℝ] E)))
  have hQJ:Q t*J t=1 := by
    apply sub_eq_zero.mp
    simpa only [intervalIntegral.integral_zero,hQ0,hJ0,mul_one] using he.symm
  refine ⟨hQJ,?_⟩
  have hinj:Function.Injective (J t) := by
    intro v w h
    have hh := congrArg (fun z => Q t z) h
    simpa only [←ContinuousLinearMap.mul_apply,hQJ,ContinuousLinearMap.one_apply] using hh
  have hsur:Function.Surjective (J t) := (LinearMap.injective_iff_surjective).mp hinj
  ext v
  obtain ⟨u,rfl⟩ := hsur v
  change J t (Q t (J t u))=J t u
  have hh := congrArg (fun L:E →L[ℝ] E => L u) hQJ
  change Q t (J t u)=u at hh
  rw [hh]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.fundamental_inverse_pair

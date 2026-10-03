import Chapter11InvestmentIdentification
import Chapter11StrategyMoments

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- Merton's verification applies to every solution of the investment SDE,
 rather than only to a separately constructed exponential process. -/
theorem investment_solution_uniform_moments {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (π : Ω × ℝ → ℝ) (hm : Measurable π)
    (R : ℝ) (hR : 0<R)
    (hp : ∀ d,0<d → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => π (z.1,z.2.val)))
    (K x r μ σ : ℝ) (hK : 0≤K) (hb : ∀ z,|π z|≤K)
    (hx : 0<x)
    (X M : HalfClosedTime → Ω → ℝ)
    (hXa : ∀ t,t<⊤ → Measurable[B.F t] (X t))
    (hXc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (hM : LocalMProcessWitness P B.F M)
    (hMI : ItoCovarianceFormula P B.F (B.W 0) (fun z => X (realTimeClamp z.2) z.1*(σ*π z)) M)
    (he : ∀ᵐ w ∂P,∀ t∈Icc 0 R,X (realTimeClamp t) w=x+
      (∫ s in 0..t,X (realTimeClamp s) w*(r+π (w,s)*(μ-r)))+M (realTimeClamp t) w) :
    ∀ q : ℝ,∃ C : ℝ,∀ t∈Icc 0 R,
      Integrable (fun w => (X (realTimeClamp t) w)^q) P ∧
      (∫ w,(X (realTimeClamp t) w)^q ∂P)≤C := by
  obtain ⟨N,D,hN,hNI,hD,hDe,hmom⟩ := bounded_strategy_all_moments P B π hm hp K x r μ σ R hK hb hx
  have hform := investment_solution_identified P B π hm R hR (hp R hR) K x r μ σ hK hb X M N hXa hXc hM hMI hN hNI he
  intro q
  refine ⟨x^q*Real.exp (|q| *((|r|+K*|μ-r|)*R)+|q^2-q| *((|σ| *K)^2*R)/2),?_⟩
  intro t ht
  have heq : X (realTimeClamp t)=ᵐ[P] fun w => x*Real.exp
      ((∫ s in 0..t,r+π (w,s)*(μ-r))+N (realTimeClamp t) w-D (realTimeClamp t) w/2) := by
    filter_upwards [hform t ht,hDe t ht.1] with w hw hd
    rw [hw,hd]
    congr 2
    have hi : IntervalIntegrable (fun s => r+π (w,s)*(μ-r)) volume 0 t := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
      apply Integrable.of_bound ((measurable_const.add ((hm.comp measurable_prodMk_left).mul_const (μ-r))).aestronglyMeasurable) (|r|+K*|μ-r|)
      apply ae_of_all
      intro s
      rw [Real.norm_eq_abs]
      exact le_trans (abs_add_le _ _) (by rw [abs_mul];exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (hb (w,s)) (abs_nonneg _)))
    have hj : IntervalIntegrable (fun s => (σ*π (w,s))^2) volume 0 t := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
      apply Integrable.of_bound (((hm.comp measurable_prodMk_left).const_mul σ).pow_const 2).aestronglyMeasurable ((|σ| *K)^2)
      apply ae_of_all
      intro s
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq.mpr (by rw [abs_mul,abs_of_nonneg (mul_nonneg (abs_nonneg σ) hK)];exact mul_le_mul_of_nonneg_left (hb (w,s)) (abs_nonneg σ))
    have hf : (fun s => r+π (w,s)*(μ-r)-σ^2*(π (w,s))^2/2)=
        (fun s => (r+π (w,s)*(μ-r))-(σ*π (w,s))^2/2) := by funext s;ring
    rw [hf,intervalIntegral.integral_sub hi (hj.div_const 2),intervalIntegral.integral_div]
    ring
  have hpow := heq.fun_comp (fun z => z^q)
  have h := hmom q t ht
  exact ⟨h.1.congr hpow.symm,(integral_congr_ae hpow).le.trans h.2⟩

end Asakura.Chapter11

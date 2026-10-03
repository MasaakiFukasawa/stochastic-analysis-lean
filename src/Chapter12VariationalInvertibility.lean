import Chapter12BackwardVariationalBound
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem variational_flow_lower_norm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J A : ℝ → E →L[ℝ] E) (T K : ℝ) (hT : 0≤T) (hc : Continuous J)
    (h0 : J 0=1) (hd : ∀ t∈Ioc (0:ℝ) T,HasDerivAt J (A t*J t) t)
    (hb : ∀ t∈Ioc (0:ℝ) T,‖A t‖≤K) (v : E) :
    ‖v‖≤‖J T v‖*Real.exp (K*T) := by
  have hdf : ∀ t∈Ioc (0:ℝ) T,HasDerivAt (fun s => J s v) (A t (J t v)) t := by
    intro t ht
    simpa only [map_zero,add_zero,ContinuousLinearMap.mul_apply] using
      (hd t ht).clm_apply (hasDerivAt_const t v)
  have hdb : ∀ t∈Ioc (0:ℝ) T,‖A t (J t v)‖≤K*‖J t v‖ := by
    intro t ht
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg _))
  have hh := backward_variational_norm_bound (fun s => J s v) (fun s => A s (J s v))
    T K hT (hc.clm_apply continuous_const) hdf hdb
  simpa only [h0,ContinuousLinearMap.one_apply] using hh

/-- In finite dimension, the backward norm estimate itself proves
invertibility and bounds the inverse. -/
theorem variational_flow_equiv_with_inverse_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (J A : ℝ → E →L[ℝ] E) (T K : ℝ) (hT : 0≤T) (hc : Continuous J)
    (h0 : J 0=1) (hd : ∀ t∈Ioc (0:ℝ) T,HasDerivAt J (A t*J t) t)
    (hb : ∀ t∈Ioc (0:ℝ) T,‖A t‖≤K) :
    ∃ e : E ≃L[ℝ] E,e.toContinuousLinearMap=J T ∧
      ‖e.symm.toContinuousLinearMap‖≤Real.exp (K*T) := by
  have hker : (J T).ker=⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    apply (injective_iff_map_eq_zero (J T).toLinearMap).mpr
    intro v hv
    change J T v=0 at hv
    have hh := variational_flow_lower_norm J A T K hT hc h0 hd hb v
    rw [hv,norm_zero,zero_mul] at hh
    exact norm_le_zero_iff.mp hh
  have hsur : (J T).range=⊤ := LinearMap.range_eq_top.mpr
    ((LinearMap.injective_iff_surjective).mp (LinearMap.ker_eq_bot.mp hker))
  let e := ContinuousLinearEquiv.ofBijective (J T) hker hsur
  refine ⟨e,ContinuousLinearEquiv.coe_ofBijective _ _ _,?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro v
  have hh := variational_flow_lower_norm J A T K hT hc h0 hd hb (e.symm v)
  have he : J T (e.symm v)=v := e.apply_symm_apply v
  rw [he] at hh
  change ‖e.symm v‖≤Real.exp (K*T)*‖v‖
  simpa only [mul_comm] using hh

end Asakura.Chapter12

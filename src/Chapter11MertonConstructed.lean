import Chapter11PowerExpectation
import Chapter11InvestmentWealth

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- Merton verification for the actual exponential wealth of any bounded
progressive strategy. The Ito equation and zero-mean noise are constructed,
not hypotheses. The constant optimal ratio attains the upper bound. -/
theorem merton_actual_wealth_verified {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (π : Ω × ℝ → ℝ) (hπm : Measurable π)
    (hπp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => π (z.1,z.2.val)))
    (K x r μ σ γ T : ℝ) (hK : 0≤K) (hb : ∀ z,|π z|≤K)
    (hx : 0<x) (hσ : σ≠0) (hγ : 0<γ) (hγ1 : γ≠1) (hT : 0<T)
    (N V : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => σ*π z) N)
    (hV : ∀ w t,t∈Icc 0 T → V (realTimeClamp t) w=
      x*Real.exp ((∫ s in 0..t,r+π (w,s)*(μ-r)-σ^2*(π (w,s))^2/2)+N (realTimeClamp t) w)) :
    Integrable (fun w => (V (realTimeClamp T) w)^(1-γ)/(1-γ)) P ∧
    (∫ w,(V (realTimeClamp T) w)^(1-γ)/(1-γ) ∂P)≤mertonValue r μ σ γ T 0 x ∧
    ((∀ z,π z=(μ-r)/(γ*σ^2)) →
      (∫ w,(V (realTimeClamp T) w)^(1-γ)/(1-γ) ∂P)=mertonValue r μ σ γ T 0 x) := by
  let b := fun z : Ω × ℝ => r+π z*(μ-r)-σ^2*(π z)^2/2
  have hbm : Measurable b := (measurable_const.add (hπm.mul_const (μ-r))).sub (((hπm.pow_const 2).const_mul (σ^2)).div_const 2)
  have hbp d (hd : 0<d) : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => b (z.1,z.2.val)) :=
    (measurable_const.add ((hπp d hd).mul_const (μ-r))).sub ((((hπp d hd).pow_const 2).const_mul (σ^2)).div_const 2)
  have hbb z : |b z|≤|r|+K*|μ-r|+σ^2*K^2/2 := by
    have hs : (π z)^2≤K^2 := sq_le_sq.mpr (by simpa only [abs_of_nonneg hK] using hb z)
    have hq : |σ^2*(π z)^2/2|≤σ^2*K^2/2 := by
      rw [abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (sq_nonneg _)) (by norm_num)
    have hp : |π z*(μ-r)|≤K*|μ-r| := by rw [abs_mul];exact mul_le_mul_of_nonneg_right (hb z) (abs_nonneg _)
    calc
      |b z| ≤ |r+π z*(μ-r)|+|σ^2*(π z)^2/2| := abs_sub _ _
      _ ≤ (|r|+|π z*(μ-r)|)+σ^2*K^2/2 := add_le_add (abs_add_le _ _) hq
      _ ≤ |r|+K*|μ-r|+σ^2*K^2/2 := by linarith
  have hVe w t (ht : t∈Icc 0 T) : V (realTimeClamp t) w=Real.exp (Real.log x+(∫ s in 0..t,b (w,s))+N (realTimeClamp t) w) := by
    simp only [hV w t ht,Real.exp_add,Real.exp_log hx,b,mul_assoc]
  obtain ⟨U,M,hM,hUV,hIto,hUm,hUpos,hUi,hUTi,hMi,hM0⟩ := exponential_power_transform_constructed
    P B b (fun z => σ*π z) hbm (hπm.const_mul σ) hbp (fun d hd => (hπp d hd).const_mul σ)
    (|σ| *K) (|r|+K*|μ-r|+σ^2*K^2/2) (Real.log x) T (mertonRate r μ σ γ) (1-γ)
    (mul_nonneg (abs_nonneg _) hK) (by positivity)
    (fun z => by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hb z) (abs_nonneg _)) hbb hT N V hN hNI hVe
  have hv := power_transform_expected_bound P (fun z => U (realTimeClamp z.2) z.1) π (M (realTimeClamp T))
    r μ σ γ T (Real.exp (mertonRate r μ σ γ*T+(1-γ)*Real.log x)) K hσ hγ hγ1 hT.le hUm hπm
    (fun z => hUpos _ _) hb hUi hMi hM0 (hIto T ⟨hT.le,le_rfl⟩)
  have he : (fun w => (V (realTimeClamp T) w)^(1-γ)/(1-γ))=ᵐ[P]
      fun w => U (realTimeClamp T) w/(1-γ) := by
    filter_upwards [hUV] with w hw
    simpa using congrArg (fun y => y/(1-γ)) (hw T ⟨hT.le,le_rfl⟩).symm
  have hc : Real.exp (mertonRate r μ σ γ*T+(1-γ)*Real.log x)/(1-γ)=mertonValue r μ σ γ T 0 x := by
    simp only [mertonValue,sub_zero,Real.exp_add,Real.rpow_def_of_pos hx]
    rw [mul_comm (1-γ) (Real.log x)]
  refine ⟨hv.1.congr he.symm,?_,?_⟩
  · rw [integral_congr_ae he]
    exact hc ▸ hv.2.2
  · intro hopt
    rw [integral_congr_ae he,hv.2.1]
    simp only [hopt,sub_self,zero_pow (by decide : 2≠0),mul_zero,integral_zero,sub_zero]
    exact hc

/-- The maximizing constant is admissible and its wealth is constructed. -/
theorem merton_optimal_wealth_exists {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (x r μ σ γ T : ℝ) (hx : 0<x) (hσ : σ≠0) (hγ : 0<γ) (hγ1 : γ≠1) (hT : 0<T) :
    ∃ V N M : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P B.F N ∧ LocalMProcessWitness P B.F M ∧
      ItoCovarianceFormula P B.F (B.W 0)
        (fun z => V (realTimeClamp z.2) z.1*(σ*((μ-r)/(γ*σ^2)))) M ∧
      (∀ w t,0<V t w) ∧
      (∀ t∈Icc 0 T,V (realTimeClamp t)=ᵐ[P]
        fun w => x+(∫ s in 0..t,V (realTimeClamp s) w*(r+((μ-r)/(γ*σ^2))*(μ-r)))+M (realTimeClamp t) w) ∧
      Integrable (fun w => (V (realTimeClamp T) w)^(1-γ)/(1-γ)) P ∧
      (∫ w,(V (realTimeClamp T) w)^(1-γ)/(1-γ) ∂P)=mertonValue r μ σ γ T 0 x := by
  let a := (μ-r)/(γ*σ^2)
  obtain ⟨V,N,M,hN,hM,hNI,hMI,hpos,hVe,hSDE⟩ := investment_wealth_constructed P B (fun _ => a)
    measurable_const (fun _ _ => measurable_const) |a| x r μ σ T (abs_nonneg _) (fun _ => le_rfl) hx hT
  have hv := merton_actual_wealth_verified P B (fun _ => a) measurable_const (fun _ _ => measurable_const)
    |a| x r μ σ γ T (abs_nonneg _) (fun _ => le_rfl) hx hσ hγ hγ1 hT N V hN hNI hVe
  exact ⟨V,N,M,hN,hM,hMI,hpos,hSDE,hv.1,hv.2.2 (fun _ => rfl)⟩

end Asakura.Chapter11

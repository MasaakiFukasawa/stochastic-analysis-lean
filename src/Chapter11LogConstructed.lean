import Chapter11InvestmentWealth
import Chapter11LogUtility
import Chapter11ConstrainedLog

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- A given actual integral of a bounded strategy has zero mean. -/
theorem bounded_given_integral_mean {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (G : Ω × ℝ → ℝ) (hm : Measurable G)
    (hp : ∀ d,0<d → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => G (z.1,z.2.val)))
    (K : ℝ) (hK : 0≤K) (hb : ∀ z,|G z|≤K)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) G N) (T : ℝ) (hT : 0≤T) :
    Integrable (N (realTimeClamp T)) P ∧ (∫ w,N (realTimeClamp T) w ∂P)=0 := by
  obtain ⟨M,C,hM,hMI,_,_,_,_,hmean⟩ := bounded_strategy_integral P B G hm hp K hK hb
  have he := hNI.unique P (by simp) B.F B.mono B.le B.null (B.W 0) N M G (B.martingale 0) hN hM hMI
  have hEq : N (realTimeClamp T)=ᵐ[P] M (realTimeClamp T) := he.mono fun w hw => hw _ (real_time_below T hT (EReal.coe_lt_top T))
  exact ⟨(hmean T hT).1.congr hEq.symm,(integral_congr_ae hEq).trans (hmean T hT).2⟩

/-- Connect the expected-log computation to the very same wealth whose
SDE and positivity were constructed, including its actual stochastic noise. -/
theorem constructed_log_wealth_optimal {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (π : Ω × ℝ → ℝ) (hm : Measurable π)
    (hp : ∀ d,0<d → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => π (z.1,z.2.val)))
    (K x r μ σ T : ℝ) (hK : 0≤K) (hb : ∀ z,|π z|≤K) (hx : 0<x) (hσ : σ≠0) (hT : 0<T) :
    ∃ V N M : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P B.F N ∧ LocalMProcessWitness P B.F M ∧
      ItoCovarianceFormula P B.F (B.W 0) (fun z => V (realTimeClamp z.2) z.1*(σ*π z)) M ∧
      (∀ w t,0<V t w) ∧
      (∀ t∈Icc 0 T,V (realTimeClamp t)=ᵐ[P]
        fun w => x+(∫ s in 0..t,V (realTimeClamp s) w*(r+π (w,s)*(μ-r)))+M (realTimeClamp t) w) ∧
      Integrable (fun w => Real.log (V (realTimeClamp T) w)) P ∧
      (∫ w,Real.log (V (realTimeClamp T) w) ∂P)=Real.log x+(r+(μ-r)^2/(2*σ^2))*T-
        σ^2/2*(∫ w,(∫ t in Icc 0 T,(π (w,t)-(μ-r)/σ^2)^2) ∂P) ∧
      (∫ w,Real.log (V (realTimeClamp T) w) ∂P)≤Real.log x+(r+(μ-r)^2/(2*σ^2))*T ∧
      ((∀ z,π z=(μ-r)/σ^2) → (∫ w,Real.log (V (realTimeClamp T) w) ∂P)=Real.log x+(r+(μ-r)^2/(2*σ^2))*T) := by
  obtain ⟨V,N,M,hN,hM,hNI,hMI,hpos,hVe,hSDE⟩ := investment_wealth_constructed P B π hm hp K x r μ σ T hK hb hx hT
  have hmean := bounded_given_integral_mean P B (fun z => σ*π z) (hm.const_mul σ) (fun d hd => (hp d hd).const_mul σ)
    (|σ| *K) (mul_nonneg (abs_nonneg _) hK) (fun z => by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hb z) (abs_nonneg σ)) N hN hNI T hT.le
  have he : (fun w => V (realTimeClamp T) w)=terminalLogWealth (fun w t => π (w,t)) (N (realTimeClamp T)) x r μ σ T := by
    funext w
    rw [hVe w T ⟨hT.le,le_rfl⟩,intervalIntegral.integral_of_le hT.le]
    simp only [terminalLogWealth,integral_Icc_eq_integral_Ioc]
  have hi := logarithmic_wealth_identity P (fun w t => π (w,t)) (N (realTimeClamp T)) x r μ σ T K hx hσ hT.le hm
    (fun w t => by simpa only [Real.norm_eq_abs] using hb (w,t)) hmean.1 hmean.2
  have ho := logarithmic_wealth_optimal P (fun w t => π (w,t)) (N (realTimeClamp T)) x r μ σ T K hx hσ hT.le hm
    (fun w t => by simpa only [Real.norm_eq_abs] using hb (w,t)) hmean.1 hmean.2
  refine ⟨V,N,M,hN,hM,hMI,hpos,hSDE,?_,?_,?_,?_⟩
  all_goals simp only [funext_iff] at he
  · simpa only [he] using hi.1
  · simpa only [he] using hi.2
  · simpa only [he] using ho.1
  · intro hopt
    simpa only [he] using ho.2 (fun w t => hopt (w,t))

/-- The constrained exercise for actual constructed wealth. The clipped
constant attains the bound, and the mean-zero input is proved from Ito. -/
theorem constructed_constrained_log_optimal {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (π : Ω × ℝ → ℝ) (hm : Measurable π)
    (hp : ∀ d,0<d → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => π (z.1,z.2.val)))
    (hb : ∀ z,π z∈Icc 0 1)
    (x r μ σ T : ℝ) (hx : 0<x) (hσ : σ≠0) (hT : 0<T) :
    ∃ V N M : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P B.F N ∧ LocalMProcessWitness P B.F M ∧
      ItoCovarianceFormula P B.F (B.W 0) (fun z => V (realTimeClamp z.2) z.1*(σ*π z)) M ∧
      (∀ w t,0<V t w) ∧
      (∀ t∈Icc 0 T,V (realTimeClamp t)=ᵐ[P]
        fun w => x+(∫ s in 0..t,V (realTimeClamp s) w*(r+π (w,s)*(μ-r)))+M (realTimeClamp t) w) ∧
      let p := min 1 (max 0 ((μ-r)/σ^2))
      let L := Real.log x+(r+p*(μ-r)-σ^2*p^2/2)*T
      (∫ w,Real.log (V (realTimeClamp T) w) ∂P)≤L ∧
      ((∀ z,π z=p) → (∫ w,Real.log (V (realTimeClamp T) w) ∂P)=L) := by
  have hbound z : |π z|≤1 := by rw [abs_of_nonneg (hb z).1];exact (hb z).2
  obtain ⟨V,N,M,hN,hM,hNI,hMI,hpos,hVe,hSDE⟩ := investment_wealth_constructed P B π hm hp 1 x r μ σ T (by norm_num) hbound hx hT
  have hmean := bounded_given_integral_mean P B (fun z => σ*π z) (hm.const_mul σ) (fun d hd => (hp d hd).const_mul σ)
    (|σ| *1) (by positivity) (fun z => by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hbound z) (abs_nonneg σ)) N hN hNI T hT.le
  have he w : V (realTimeClamp T) w=terminalLogWealth (fun w t => π (w,t)) (N (realTimeClamp T)) x r μ σ T w := by
    rw [hVe w T ⟨hT.le,le_rfl⟩,intervalIntegral.integral_of_le hT.le]
    simp only [terminalLogWealth,integral_Icc_eq_integral_Ioc]
  have hc := constrained_log_utility P (fun w t => π (w,t)) (N (realTimeClamp T)) x r μ σ T hx hσ hT.le hm
    (fun w t => hb (w,t)) hmean.1 hmean.2
  refine ⟨V,N,M,hN,hM,hMI,hpos,hSDE,?_,?_⟩
  · simpa only [he] using hc.1
  · intro hopt
    simpa only [he] using hc.2 (fun w t => hopt (w,t))

end Asakura.Chapter11

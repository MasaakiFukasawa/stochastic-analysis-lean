import Chapter6LinearLikelihoodDensity

open MeasureTheory Set Filter Finset Matrix
open scoped Topology NNReal ENNReal BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

theorem linear_likelihood_changed_brownian {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (H N : Fin n → Fin d → HalfClosedTime → Ω → ℝ)
    (hHa : ∀ k j t,Measurable[B.F t] (H k j t)) (hHc : ∀ k j w,Continuous (fun t => H k j t w))
    (hN : ∀ k j,LocalMProcessWitness P B.F (N k j))
    (hNI : ∀ k j,ItoCovarianceFormula P B.F (B.W j) (fun z => H k j (realTimeClamp z.2) z.1) (N k j))
    (K : ℝ) (hK : 0≤K) (hHb : ∀ k j t w,|H k j t w|≤K)
    (R : ℝ) (hR : 0≤R) (θ : Fin n → ℝ) :
    let score := fun w k => ∑ j,N k j (realTimeClamp R) w
    let info := fun w k l => ∫ r in 0..R,∑ j,H k j (realTimeClamp r) w*H l j (realTimeClamp r) w
    ∃ (Q : Measure Ω) (hQp : IsProbabilityMeasure Q) (density : Ω → ℝ≥0),
      Measurable density ∧ MemLp (fun w => (density w:ℝ)) 2 P ∧
      Q=P.withDensity (fun w => (density w:ℝ≥0∞)) ∧
      Q=P.withDensity (fun w => ENNReal.ofReal (Real.exp (quadraticLogLikelihood (info w) (score w) θ))) ∧
      ∃ BQ : BrownianSystem Q d,BQ.F=B.F ∧
        ∀ j r,r∈Icc 0 R → B.W j (realTimeClamp r)=ᵐ[Q]
          fun w => BQ.W j (realTimeClamp r) w+∫ s in 0..r,∑ k,θ k*H k j (realTimeClamp s) w := by
  let A := fun j t w => ∑ k,θ k*H k j t w
  let M := fun j t w => ∑ k,θ k*N k j t w
  let G := fun j (z : Ω × ℝ) => A j (realTimeClamp z.2) z.1
  have hAa j t : Measurable[B.F t] (A j t) := Finset.measurable_sum _ (fun k _ => (hHa k j t).const_mul _)
  have hAc j w : Continuous (fun t => A j t w) := continuous_finsetSum _ (fun k _ => (hHc k j w).const_mul _)
  have hGr j w : Continuous (fun r => G j (w,r)) := (hAc j w).comp real_time_clamp_continuous
  have hGm j : Measurable (G j) := by
    have hm r : Measurable (A j (realTimeClamp r)) := (hAa j _).mono (B.le _) le_rfl
    simpa only [G,Function.comp_def,Function.uncurry_def,Prod.swap] using
      (measurable_uncurry_of_continuous_of_measurable (hGr j) hm).comp measurable_swap
  have hGp j r (hr : 0<r) := continuous_adapted_real_progressive B.F B.mono (G j) r hr.le (fun s _ => hAa j _) (fun w => (hGr j w).continuousOn)
  have hMb j := finite_weighted_ito P (show (0:EReal)<⊤ by simp) B.F B.mono B.le B.null
    (B.W j) (B.martingale j) (fun k z => H k j (realTimeClamp z.2) z.1) (fun k => N k j) (fun k => hN k j) (fun k => hNI k j) θ
  let K' := ∑ k,|θ k| * K
  have hK' : 0≤K' := sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) hK)
  have hGb j z : |G j z|≤K' := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact sum_le_sum (fun k _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hHb k j _ _) (abs_nonneg _))
  obtain ⟨I,C,hI,hII,hC,hCe,Q,hQp,hQD,hmean,hD2,_,_,BQ,hBQ,hBW⟩ := bounded_girsanov_density_data P B G hGm hGp K' hK' hGb R hR
  let D := fun w => Real.exp ((∑ j,I j (realTimeClamp R) w)-C (realTimeClamp R) w/2)
  have hZ := local_martingale_finset_sum P (show (0:EReal)<⊤ by simp) B.F B.mono B.le univ I (fun j _ => hI j)
  have hCm : Measurable (C (realTimeClamp R)) := ((hC.adapted P B.F hZ hZ _ (changed_time_finite R hR))).mono (B.le _) le_rfl
  have hDm : Measurable D := ((Finset.measurable_sum _ (fun j _ => ((hI j).adapted P B.F _ (changed_time_finite R hR)).mono (B.le _) le_rfl)).sub (hCm.div_const 2)).exp
  let density := fun w => Real.toNNReal (D w)
  have hd : Measurable density := hDm.real_toNNReal
  have hde w : (density w:ℝ)=D w := Real.coe_toNNReal _ (Real.exp_pos _).le
  have he j := ItoCovarianceFormula.unique P (show (0:EReal)<⊤ by simp) B.F B.mono B.le B.null
    (B.W j) (I j) (M j) (G j) (B.martingale j) (hI j) (hMb j).1 (hII j) (hMb j).2
  have hDq : D=ᵐ[P] fun w => Real.exp (quadraticLogLikelihood
      (fun k l => ∫ r in 0..R,∑ j,H k j (realTimeClamp r) w*H l j (realTimeClamp r) w)
      (fun k => ∑ j,N k j (realTimeClamp R) w) θ) := by
    filter_upwards [ae_all_iff.2 he,hCe R hR] with w hw hc
    change Real.exp ((∑ j,I j (realTimeClamp R) w)-C (realTimeClamp R) w/2)=_
    rw [hc]
    have hn : (∑ j,I j (realTimeClamp R) w)=∑ k,θ k*(∑ j,N k j (realTimeClamp R) w) := by
      simp_rw [fun j => hw j _ (changed_time_finite R hR)]
      dsimp only [M]
      rw [sum_comm]
      simp only [mul_sum]
    rw [hn]
    have hg := likelihood_energy_gram (fun k j r => H k j (realTimeClamp r) w) R hR
      (fun k j => ((hHc k j w).comp real_time_clamp_continuous).continuousOn) θ
    change Real.exp ((∑ k,θ k*(∑ j,N k j (realTimeClamp R) w))-(∫ r in 0..R,∑ j,(∑ k,θ k*H k j (realTimeClamp r) w)^2)/2)=_
    rw [hg]
    rfl
  refine ⟨Q,hQp,density,hd,?_,?_,?_,BQ,hBQ,?_⟩
  · simpa only [hde] using hD2
  · exact hQD
  · exact hQD.trans (withDensity_congr_ae (hDq.mono (fun w hw => congrArg ENNReal.ofReal hw)))
  · intro j r hr
    filter_upwards [hBW j r hr.1] with w hw
    rw [min_eq_right hr.2] at hw
    change BQ.W j (realTimeClamp r) w=B.W j (realTimeClamp r) w-(∫ s in 0..r,∑ k,θ k*H k j (realTimeClamp s) w) at hw
    linarith

end Asakura.Chapter6

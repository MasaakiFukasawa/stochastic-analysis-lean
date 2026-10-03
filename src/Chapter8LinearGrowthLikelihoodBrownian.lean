import Chapter8LinearGrowthGivenBrownian
import Chapter6FiniteWeightedIto
import Chapter6LikelihoodEnergy

open MeasureTheory Set Filter Finset Matrix
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7 Asakura.Chapter6
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- The actual finite collection of score Ito integrals determines a
probability density for every parameter in the whole Euclidean parameter space. -/
theorem linear_growth_likelihood_brownian {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (H N : Fin n → Fin d → HalfClosedTime → Ω → ℝ)
    (hHa : ∀ k j (t : ℝ),Measurable[B.F (realTimeClamp t)] (H k j (realTimeClamp t)))
    (hHc : ∀ k j w,Continuous (fun t : ℝ => H k j (realTimeClamp t) w))
    (hN : ∀ k j,LocalMProcessWitness P B.F (N k j))
    (hNI : ∀ k j,ItoCovarianceFormula P B.F (B.W j) (fun z => H k j (realTimeClamp z.2) z.1) (N k j))
    (K : ℝ) (hK : 0≤K) (R : ℝ) (hR : 0≤R)
    (hHb : ∀ k w r,r∈Icc 0 R → ‖WithLp.toLp 2 (fun j => H k j (realTimeClamp r) w)‖≤
      K*(1+‖WithLp.toLp 2 (fun j => B.W j (realTimeClamp r) w)‖))
    (θ : Fin n → ℝ) :
    let score := fun w k => ∑ j,N k j (realTimeClamp R) w
    let info := fun w k l => ∫ r in 0..R,∑ j,H k j (realTimeClamp r) w*H l j (realTimeClamp r) w
    let D := fun w => Real.exp (quadraticLogLikelihood (info w) (score w) θ)
    ∃ hQp : IsProbabilityMeasure (P.withDensity (fun w => ENNReal.ofReal (D w))),
      ∃ BQ : BrownianSystem (P.withDensity (fun w => ENNReal.ofReal (D w))) d,
        BQ.F=B.F ∧ ∀ j r,0≤r → BQ.W j (realTimeClamp r)=ᵐ[P.withDensity (fun w => ENNReal.ofReal (D w))]
          fun w => B.W j (realTimeClamp r) w-∫ s in 0..min R r,∑ k,θ k*H k j (realTimeClamp s) w := by
  let A := fun j t w => ∑ k,θ k*H k j t w
  let M := fun j t w => ∑ k,θ k*N k j t w
  let G := fun j (z : Ω × ℝ) => A j (realTimeClamp z.2) z.1
  have hAi j (t : ℝ) : Measurable[B.F (realTimeClamp t)] (A j (realTimeClamp t)) := Finset.measurable_sum _ (fun k _ => (hHa k j t).const_mul _)
  have hAc j w : Continuous (fun t : ℝ => A j (realTimeClamp t) w) := continuous_finsetSum _ (fun k _ => (hHc k j w).const_mul _)
  have hGr j w : Continuous (fun r => G j (w,r)) := hAc j w
  have hGm j : Measurable (G j) := by
    have hm r : Measurable (A j (realTimeClamp r)) := (hAi j _).mono (B.le _) le_rfl
    simpa only [G,Function.comp_def,Function.uncurry_def,Prod.swap] using
      (measurable_uncurry_of_continuous_of_measurable (hGr j) hm).comp measurable_swap
  have hGp j r (hr : 0<r) := continuous_adapted_real_progressive B.F B.mono (G j) r hr.le
    (fun s _ => hAi j _) (fun w => (hGr j w).continuousOn)
  have hMb j := finite_weighted_ito P (show (0:EReal)<⊤ by simp) B.F B.mono B.le B.null
    (B.W j) (B.martingale j) (fun k z => H k j (realTimeClamp z.2) z.1) (fun k => N k j)
    (fun k => hN k j) (fun k => hNI k j) θ
  let C := ∑ k,|θ k| * K
  have hC : 0≤C := Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) hK)
  have hGb w r (hr : r∈Icc 0 R) : ‖WithLp.toLp 2 (fun j => G j (w,r))‖≤
      C*(1+‖WithLp.toLp 2 (fun j => B.W j (realTimeClamp r) w)‖) := by
    have he : WithLp.toLp 2 (fun j => G j (w,r))=
        ∑ k,θ k • WithLp.toLp 2 (fun j => H k j (realTimeClamp r) w) := by
      ext j
      simp only [G,A,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,WithLp.ofLp_toLp,smul_eq_mul]
    rw [he]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ k,(|θ k| *K)*(1+‖WithLp.toLp 2 (fun j => B.W j (realTimeClamp r) w)‖) := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_smul,Real.norm_eq_abs,mul_assoc]
        exact mul_le_mul_of_nonneg_left (hHb k w r hr) (abs_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  have hd := linear_growth_given_integral_brownian P B G hGm hGp hGr R hR C hC hGb M
    (fun j => (hMb j).1) (fun j => (hMb j).2)
  have he w : Real.exp ((∑ j,M j (realTimeClamp R) w)-(∫ r in 0..R,∑ j,(G j (w,r))^2)/2)=
      Real.exp (quadraticLogLikelihood
        (fun k l => ∫ r in 0..R,∑ j,H k j (realTimeClamp r) w*H l j (realTimeClamp r) w)
        (fun k => ∑ j,N k j (realTimeClamp R) w) θ) := by
    have hc := likelihood_energy_gram (fun k j r => H k j (realTimeClamp r) w) R hR
      (fun k j => (hHc k j w).continuousOn) θ
    change Real.exp ((∑ j,∑ k,θ k*N k j (realTimeClamp R) w)-(∫ r in 0..R,∑ j,(∑ k,θ k*H k j (realTimeClamp r) w)^2)/2)=_
    rw [hc,Finset.sum_comm]
    simp only [quadraticLogLikelihood,dotProduct,mul_sum]
  have heq : (fun w => ENNReal.ofReal (Real.exp ((∑ j,M j (realTimeClamp R) w)-(∫ r in 0..R,∑ j,(G j (w,r))^2)/2))) =
      (fun w => ENNReal.ofReal (Real.exp (quadraticLogLikelihood
        (fun k l => ∫ r in 0..R,∑ j,H k j (realTimeClamp r) w*H l j (realTimeClamp r) w)
        (fun k => ∑ j,N k j (realTimeClamp R) w) θ))) := by funext w; rw [he]
  dsimp only at hd
  rw [heq] at hd
  simpa only [G, A, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul] using hd

end Asakura.Chapter8

import Chapter8ConstructedLangevinScoreCLT
import Chapter8SelfNormalisation
import Chapter8InformationPositive

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal BigOperators RealInnerProductSpace Topology Matrix.Norms.Elementwise MatrixOrder
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- The MLE CLT, consistency and observable self-normalisation, after the
likelihood equation. The information and score limits are derived from
the actual model; the estimator convention on singular information is arbitrary. -/
theorem constructed_langevin_estimator_clt {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n p : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E) (g : (Fin d → ℝ) → (Fin d → ℝ)) (Kg : ℝ≥0) (hg : LipschitzWith Kg g)
    (σ : Fin d → Fin n → ℝ) (L : ℝ) (hL : 0≤L)
    (hLip : ∀ x y,(∑ i,(-(g x i)- -(g y i))^2)+
      (∑ i : Fin d,∑ j : Fin n,(σ i j-σ i j)^2)≤L*∑ i,(x i-y i)^2)
    (κ : ℝ) (hκ : 0<κ)
    (hmono : ∀ x y,κ*‖e x-e y‖^2≤⟪e x-e y,e (g x)-e (g y)⟫)
    (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π] (hπ : MemLp (fun x => x) 2 π)
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W (fun i y => -(g y i)) (fun i j _ => σ i j) (fun _ => x) (Z x))
    (hinv : ∀ t : ℝ,0≤t → ∀ f : (Fin d → ℝ) → ℝ,ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      (∫ x,(∫ w,f (Z x (realTimeClamp t) w) ∂P) ∂π)=∫ x,f x ∂π)
    (x : Fin d → ℝ) (H : Fin p → Fin n → E → ℝ) (K : Fin p → Fin n → ℝ≥0)
    (hH : ∀ k j,LipschitzWith (K k j) (H k j)) (hHc : ∀ k j,ContDiff ℝ 1 (H k j))
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosDef)
    (hSe : ∀ k l,S k l=∫ z,∑ j,H k j z*H l j z ∂π.map e)
    (T : ℕ → ℝ) (hT : ∀ k,0<T k) (hTlim : Tendsto T atTop atTop) :
    let J : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ := fun q w k l => (∫ r in 0..T q,∑ j,H k j (e (Z x (realTimeClamp r) w))*H l j (e (Z x (realTimeClamp r) w)))/(T q)
    ∃ N : Fin p → Fin n → HalfClosedTime → Ω → ℝ,
      (∀ k j,LocalMProcessWitness P B.F (N k j)) ∧
      (∀ k j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => H k j (e (Z x (realTimeClamp z.2) z.1))) (N k j)) ∧
      ∀ V : ℕ → Ω → EuclideanSpace ℝ (Fin p),
        (∀ q,AEMeasurable (V q) P) →
        (∀ q w,(J q w).det≠0 → V q w=Matrix.toEuclideanCLM (𝕜 := ℝ) (J q w)⁻¹
          (WithLp.toLp 2 (fun k => (∑ j,N k j (realTimeClamp (T q)) w)/Real.sqrt (T q)))) →
        TendstoInDistribution V atTop id (fun _ => P) (multivariateGaussian 0 S⁻¹) ∧
        TendstoInMeasure P (fun q w => (Real.sqrt (T q))⁻¹ • V q w) atTop (fun _ => 0) ∧
        TendstoInDistribution (fun q w => Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (J q w)) (V q w))
          atTop id (fun _ => P) (multivariateGaussian 0 1) := by
  dsimp only
  let J : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ := fun q w k l =>
    (∫ r in 0..T q,∑ j,H k j (e (Z x (realTimeClamp r) w))*H l j (e (Z x (realTimeClamp r) w)))/(T q)
  obtain ⟨havg,N,hN,hNI,hscore⟩ := constructed_langevin_score_clt P B e g Kg hg σ L hL hLip κ hκ hmono
    π hπ Z hZ hinv x H K hH hHc S hS hSe T hT hTlim
  have hc w : Continuous (fun t : ℝ => e (Z x (realTimeClamp t) w)) := by
    apply e.continuous.comp
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hZ x).path w _ (half_real_time_finite t)).comp real_time_clamp_continuous.continuousAt
  have hm : Measurable (fun z : Ω × ℝ => e (Z x (realTimeClamp z.2) z.1)) := by
    exact (measurable_uncurry_of_continuous_of_measurable hc
      (fun t => e.continuous.measurable.comp (((hZ x).adapted _ (half_real_time_finite t)).mono (B.le _) le_rfl))).comp measurable_swap
  have hJm q : Measurable (J q) := by
    apply measurable_pi_lambda
    intro k
    apply measurable_pi_lambda
    intro l
    have hh := time_average_measurable
      (fun w r => ∑ j,H k j (e (Z x (realTimeClamp r) w))*H l j (e (Z x (realTimeClamp r) w)))
      (Finset.measurable_sum _ (fun j _ => ((hHc k j).continuous.measurable.comp hm).mul ((hHc l j).continuous.measurable.comp hm)))
      (T q) (hT q).le
    simpa only [timeAverage,J,div_eq_inv_mul] using hh
  have hJpos q w : (J q w).PosSemidef := by
    have hh := information_gram_posSemidef (fun k j r => H k j (e (Z x (realTimeClamp r) w)))
      (T q) (hT q).le (fun k j => ((hHc k j).continuous.comp (hc w)).continuousOn)
    convert hh.smul (inv_nonneg.mpr (hT q).le) using 1
    ext k l
    simp [J,div_eq_inv_mul]
  have hJlim k l : TendstoInMeasure P (fun q w => J q w k l) atTop (fun _ => S k l) := (havg k l).comp hTlim
  refine ⟨N,hN,hNI,?_⟩
  intro V hVm hVe
  have hv := likelihood_clt_assembly P
    (fun q w => WithLp.toLp 2 (fun k => (∑ j,N k j (realTimeClamp (T q)) w)/Real.sqrt (T q)))
    V J S hS hscore hJm hVm hJlim hVe
  refine ⟨hv,?_,self_normalised_likelihood_clt P V J S hS hv hJm hJpos hJlim⟩
  exact consistency_from_scaled_clt P (multivariateGaussian 0 S⁻¹) V id hv
    (fun q => (Real.sqrt (T q))⁻¹) (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hTlim))

end Asakura.Chapter8

import Chapter8ConstructedLangevinEstimatorCLT
import Chapter8WrittenMLELimit
import Chapter8InvariantCoordinateTests
import Chapter8SelfNormalisation
import Chapter8InformationPositive

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal BigOperators RealInnerProductSpace Topology Matrix.Norms.Elementwise MatrixOrder
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- The MLE CLT, consistency and observable self-normalisation, after the
likelihood equation. The information and score limits are derived from
the actual model; the estimator convention on singular information is arbitrary. -/
theorem langevin_mle_manuscript {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n p : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E) (g : (Fin d → ℝ) → (Fin d → ℝ)) (Kg : ℝ≥0) (hg : LipschitzWith Kg g)
    (σ : Fin d → Fin n → ℝ) (κ : ℝ) (hκ : 0<κ)
    (hmono : ∀ x y,κ*‖e x-e y‖^2≤⟪e x-e y,e (g x)-e (g y)⟫)
    (x : Fin d → ℝ) (H : Fin p → Fin n → E → ℝ) (K : Fin p → Fin n → ℝ≥0)
    (hH : ∀ k j,LipschitzWith (K k j) (H k j)) (hHc : ∀ k j,ContDiff ℝ 1 (H k j))
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosDef)
    (θ : Fin p → ℝ) (T : ℕ → ℝ) (hT : ∀ k,0<T k) (hTlim : Tendsto T atTop atTop) :
    ∃ (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
      (π : Measure E),
      (∀ x,VectorSDESolution P B.F B.W (fun i y => -(g y i)) (fun i j _ => σ i j) (fun _ => x) (Z x)) ∧
      IsProbabilityMeasure π ∧ MemLp (fun z : E => z) 2 π ∧
      ((∀ k l,S k l=∫ z,∑ j,H k j z*H l j z ∂π) →
    ∃ N : Fin p → Fin n → HalfClosedTime → Ω → ℝ,
      (∀ k j,LocalMProcessWitness P B.F (N k j)) ∧
      (∀ k j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => H k j (e (Z x (realTimeClamp z.2) z.1))) (N k j)) ∧
      let I : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ := fun q w k l =>
        ∫ r in 0..T q,∑ j,H k j (e (Z x (realTimeClamp r) w))*H l j (e (Z x (realTimeClamp r) w))
      let score := fun q w => I q w *ᵥ θ+(fun k => ∑ j,N k j (realTimeClamp (T q)) w)
      let est := fun q w => if (I q w).det≠0 then (I q w)⁻¹ *ᵥ score q w else 0
      let V := fun q w => WithLp.toLp 2 (fun k => Real.sqrt (T q)*(est q w k-θ k))
      (∀ k l,TendstoInMeasure P (fun q w => I q w k l/T q) atTop (fun _ => S k l)) ∧
      TendstoInDistribution V atTop id (fun _ => P) (multivariateGaussian 0 S⁻¹) ∧
      TendstoInMeasure P (fun q w => WithLp.toLp 2 (fun k => est q w k-θ k)) atTop (fun _ => 0) ∧
      TendstoInDistribution (fun q w => Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt ((T q)⁻¹ • I q w)) (V q w))
        atTop id (fun _ => P) (multivariateGaussian 0 1)) := by
  obtain ⟨Z,F,π,hZ,hFm,hFr,hπ,hπ2,hinv,_⟩ := langevin_invariant_manuscript P B e g Kg hg σ κ hκ hmono
  letI : IsProbabilityMeasure π := hπ
  refine ⟨Z,π,hZ,hπ,hπ2,?_⟩
  intro hSe
  let ν := π.map e.symm
  haveI : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff e.symm.continuous.measurable.aemeasurable).mpr inferInstance
  have hν : MemLp (fun z => z) 2 ν := by
    apply e.symm.toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff.mpr
    exact e.symm.toContinuousLinearMap.comp_memLp' hπ2
  have hνmap : ν.map e=π := by
    rw [Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
    simp only [Function.comp_def,e.apply_symm_apply,Measure.map_id']
  let L : ℝ := (d:ℝ)*(Kg:ℝ)^2
  have hL : 0≤L := by dsimp [L]; positivity
  have hLip : ∀ x y,(∑ i,(-(g x i)- -(g y i))^2)+
      (∑ i : Fin d,∑ j : Fin n,(σ i j-σ i j)^2)≤L*∑ i,(x i-y i)^2 := by
    intro x y
    simpa only [sub_self,zero_pow (by decide : 2≠0),Finset.sum_const_zero,add_zero,Pi.neg_apply,L]
      using lipschitz_square_coordinates (fun x => -g x) Kg hg.neg x y
  have hinvt t (ht : 0≤t) f (hf : ContDiff ℝ (⊤:ℕ∞) f) (hs : HasCompactSupport f) :=
    invariant_coordinate_tests P e π (F t) (hFm t ht) (fun x => Z x (realTimeClamp t)) (hFr t ht) (hinv t ht) f hf.continuous hs
  obtain ⟨havg,N,hN,hNI,hNl⟩ := constructed_langevin_score_clt P B e g Kg hg σ L hL hLip κ hκ hmono
    ν hν Z hZ hinvt x H K hH hHc S hS (by simpa only [hνmap] using hSe) T hT hTlim
  refine ⟨N,hN,hNI,?_⟩
  dsimp only
  let I : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ := fun q w k l =>
    ∫ r in 0..T q,∑ j,H k j (e (Z x (realTimeClamp r) w))*H l j (e (Z x (realTimeClamp r) w))
  have hc w : Continuous (fun t : ℝ => e (Z x (realTimeClamp t) w)) := by
    apply e.continuous.comp
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hZ x).path w _ (half_real_time_finite t)).comp real_time_clamp_continuous.continuousAt
  have hm : Measurable (fun z : Ω × ℝ => e (Z x (realTimeClamp z.2) z.1)) :=
    (measurable_uncurry_of_continuous_of_measurable hc
      (fun t => e.continuous.measurable.comp (((hZ x).adapted _ (half_real_time_finite t)).mono (B.le _) le_rfl))).comp measurable_swap
  have hIm q : Measurable (I q) := by
    apply measurable_pi_lambda
    intro k
    apply measurable_pi_lambda
    intro l
    have hh : Measurable (fun z : Ω × ℝ => ∑ j,H k j (e (Z x (realTimeClamp z.2) z.1))*H l j (e (Z x (realTimeClamp z.2) z.1))) :=
      Finset.measurable_sum _ (fun j _ => ((hHc k j).continuous.measurable.comp hm).mul ((hHc l j).continuous.measurable.comp hm))
    dsimp only [I]
    simp_rw [intervalIntegral.integral_of_le (hT q).le]
    exact (show StronglyMeasurable (Function.uncurry (fun w r => ∑ j,H k j (e (Z x (realTimeClamp r) w))*H l j (e (Z x (realTimeClamp r) w)))) from hh.stronglyMeasurable).integral_prod_right.measurable
  have hIp q w : (I q w).PosSemidef := information_gram_posSemidef
    (fun k j r => H k j (e (Z x (realTimeClamp r) w))) (T q) (hT q).le
    (fun k j => ((hHc k j).continuous.comp (hc w)).continuousOn)
  let noise := fun q w k => ∑ j,N k j (realTimeClamp (T q)) w
  let score := fun q w => I q w *ᵥ θ+noise q w
  have hsm q : Measurable (score q) := by
    apply measurable_pi_lambda
    intro k
    apply Measurable.add
    · simpa only [Matrix.mulVec,dotProduct,Function.comp_def] using Finset.measurable_sum Finset.univ (fun l _ =>
        (((measurable_pi_apply l).comp ((measurable_pi_apply k).comp (hIm q))).mul_const (θ l)))
    · exact Finset.measurable_sum _ (fun j _ => ((hN k j).adapted P B.F _ (half_real_time_finite _)).mono (B.le _) le_rfl)
  have hIl k l : TendstoInMeasure P (fun q w => I q w k l/T q) atTop (fun _ => S k l) := (havg k l).comp hTlim
  exact ⟨hIl,written_mle_limit P I hIm hIp score noise hsm θ
    (fun _ => ae_of_all _ (fun _ => rfl)) T hT hTlim S hS hIl hNl⟩
end Asakura.Chapter8

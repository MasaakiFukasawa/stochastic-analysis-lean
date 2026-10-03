import Chapter8ConstructedLangevinEstimatorCLT
import Chapter8InvariantCoordinateTests
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
theorem langevin_inference_constructed {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n p : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E) (g : (Fin d → ℝ) → (Fin d → ℝ)) (Kg : ℝ≥0) (hg : LipschitzWith Kg g)
    (σ : Fin d → Fin n → ℝ) (κ : ℝ) (hκ : 0<κ)
    (hmono : ∀ x y,κ*‖e x-e y‖^2≤⟪e x-e y,e (g x)-e (g y)⟫)
    (x : Fin d → ℝ) (H : Fin p → Fin n → E → ℝ) (K : Fin p → Fin n → ℝ≥0)
    (hH : ∀ k j,LipschitzWith (K k j) (H k j)) (hHc : ∀ k j,ContDiff ℝ 1 (H k j))
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosDef)
    (T : ℕ → ℝ) (hT : ∀ k,0<T k) (hTlim : Tendsto T atTop atTop) :
    ∃ (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
      (π : Measure E),
      (∀ x,VectorSDESolution P B.F B.W (fun i y => -(g y i)) (fun i j _ => σ i j) (fun _ => x) (Z x)) ∧
      IsProbabilityMeasure π ∧ MemLp (fun z : E => z) 2 π ∧
      ((∀ k l,S k l=∫ z,∑ j,H k j z*H l j z ∂π) →
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
  have hh := constructed_langevin_estimator_clt P B e g Kg hg σ L hL hLip κ hκ hmono
    ν hν Z hZ hinvt x H K hH hHc S hS (by simpa only [hνmap] using hSe) T hT hTlim
  exact hh

end Asakura.Chapter8

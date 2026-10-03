import Chapter8ConstructedUnboundedTimeAverage
import Chapter8ConstructedScoreCLT
import Chapter8ContinuousObservationLimit

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal BigOperators RealInnerProductSpace Topology
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The information limit and Gaussian score limit are derived from the
actual Langevin model and the previous time-average theorem. -/
theorem constructed_langevin_score_clt {Ω E : Type*} [MeasurableSpace Ω]
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
    (∀ k l,TendstoInMeasure P
      (fun t w => (∫ r in 0..t,∑ j,H k j (e (Z x (realTimeClamp r) w))*H l j (e (Z x (realTimeClamp r) w)))/t)
      atTop (fun _ => S k l)) ∧
    ∃ N : Fin p → Fin n → HalfClosedTime → Ω → ℝ,
      (∀ k j,LocalMProcessWitness P B.F (N k j)) ∧
      (∀ k j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => H k j (e (Z x (realTimeClamp z.2) z.1))) (N k j)) ∧
      TendstoInDistribution
        (fun k w => WithLp.toLp 2 (fun j => (∑ i,N j i (realTimeClamp (T k)) w)/Real.sqrt (T k)))
        atTop id (fun _ => P) (multivariateGaussian 0 S) := by
  haveI : IsProbabilityMeasure (π.map e) :=
    (Measure.isProbabilityMeasure_map_iff e.continuous.measurable.aemeasurable).mpr inferInstance
  have hπe : MemLp (fun z : E => z) 2 (π.map e) := by
    apply e.toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff.mpr
    exact e.toContinuousLinearMap.comp_memLp' hπ
  have havg k l : TendstoInMeasure P
      (fun t w => (∫ r in 0..t,∑ j,H k j (e (Z x (realTimeClamp r) w))*H l j (e (Z x (realTimeClamp r) w)))/t)
      atTop (fun _ => S k l) := by
    obtain ⟨hc,hi⟩ := information_entry_regular (π.map e) hπe (H k) (H l) (K k) (K l) (hH k) (hH l) (hHc k) (hHc l)
    obtain ⟨C,hC,hgC⟩ := information_entry_weighted_bound (H k) (H l) (K k) (K l) (hH k) (hH l)
    apply probability_limit_from_observation_sequences
    intro R hR hRlim
    have hh := constructed_unbounded_time_average P B e g Kg hg σ L hL hLip κ hκ hmono π hπ Z hZ hinv
      x R hR hRlim (fun z => ∑ j,H k j z*H l j z) hc hi C hC hgC
    rw [←hSe k l] at hh
    apply hh.congr' _ Filter.EventuallyEq.rfl
    apply Filter.Eventually.of_forall
    intro q
    apply ae_of_all
    intro w
    dsimp only [timeAverage]
    rw [div_eq_inv_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le (hR q).le] at hr
    dsimp only
    rw [max_eq_right hr.1]
  refine ⟨havg,?_⟩
  have hZa j i (t : ℝ) : Measurable[B.F (realTimeClamp t)]
      (fun w => H j i (e (Z x (realTimeClamp t) w))) :=
    (hHc j i).continuous.measurable.comp (e.continuous.measurable.comp ((hZ x).adapted _ (half_real_time_finite t)))
  have hZc j i w : Continuous (fun t : ℝ => H j i (e (Z x (realTimeClamp t) w))) := by
    apply (hHc j i).continuous.comp (e.continuous.comp _)
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hZ x).path w _ (half_real_time_finite t)).comp real_time_clamp_continuous.continuousAt
  exact constructed_score_clt P B (fun j i t w => H j i (e (Z x t w))) hZa hZc S hS havg T hT hTlim

end Asakura.Chapter8

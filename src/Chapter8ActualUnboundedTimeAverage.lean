import Chapter8ActualStationaryTimeAverage
import Chapter8ActualSynchronousContraction
import Chapter8InformationErgodicTransfer
import Chapter8SecondMomentL1

open MeasureTheory Set Filter
open scoped NNReal BigOperators RealInnerProductSpace Topology
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The cutoff and common-noise argument for the information limit is
applied to actual SDEs, with stationarity, contraction and bounded-observable
convergence all derived rather than assumed. -/
theorem actual_unbounded_time_average {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E) (g : (Fin d → ℝ) → (Fin d → ℝ)) (hg : Continuous g)
    (σ : Fin d → Fin n → ℝ) (L : ℝ) (hL : 0≤L)
    (hLip : ∀ x y,(∑ i,(-(g x i)- -(g y i))^2)+
      (∑ i : Fin d,∑ j : Fin n,(σ i j-σ i j)^2)≤L*∑ i,(x i-y i)^2)
    (κ : ℝ) (hκ : 0<κ)
    (hmono : ∀ x y,κ*‖e x-e y‖^2≤⟪e x-e y,e (g x)-e (g y)⟫)
    (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π] (hπ : MemLp (fun x => x) 2 π)
    (ξ : Ω → Fin d → ℝ) (hξ : MemLp ξ 2 P) (hξlaw : P.map ξ=π)
    (Y : HalfClosedTime → Ω → Fin d → ℝ)
    (hY : VectorSDESolution P B.F B.W (fun i y => -(g y i)) (fun i j _ => σ i j) ξ Y)
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W (fun i y => -(g y i)) (fun i j _ => σ i j) (fun _ => x) (Z x))
    (hinv : ∀ t : ℝ,0≤t → ∀ f : (Fin d → ℝ) → ℝ,ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      (∫ x,(∫ w,f (Z x (realTimeClamp t) w) ∂P) ∂π)=∫ x,f x ∂π)
    (x : Fin d → ℝ) (T : ℕ → ℝ) (hT : ∀ k,0<T k) (hTlim : Tendsto T atTop atTop)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (hi : Integrable f (π.map e))
    (C : ℝ) (hC : 0≤C)
    (hfg : ∀ z z',|f z-f z'|≤C*‖z-z'‖*(1+‖z‖+‖z'‖)) :
    TendstoInMeasure P
      (fun k w => timeAverage (fun t => f (e (Z x (realTimeClamp (max 0 t)) w))) (T k))
      atTop (fun _ => ∫ z,f z ∂π.map e) := by
  let π' := π.map e
  haveI : IsProbabilityMeasure π' :=
    (Measure.isProbabilityMeasure_map_iff e.continuous.measurable.aemeasurable).mpr inferInstance
  have hπ' : MemLp (fun y : E => y) 2 π' := by
    apply e.toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff.mpr
    exact e.toContinuousLinearMap.comp_memLp' hπ
  let X' := fun w t => e (Z x (realTimeClamp (max 0 t)) w)
  let Y' := fun w t => e (Y (realTimeClamp (max 0 t)) w)
  obtain ⟨hYc,hYm,hYlp,hYa⟩ := sde_real_path_data P B L hL _ _ hLip ξ hξ Y hY
  obtain ⟨hXc,hXm,hXlp,hXa⟩ := sde_real_path_data P B L hL _ _ hLip (fun _ => x) (memLp_const x) (Z x) (hZ x)
  have hmX : Measurable (Function.uncurry X') := e.continuous.measurable.comp hXm
  have hmY : Measurable (Function.uncurry Y') := e.continuous.measurable.comp hYm
  have hcX w : Continuous (X' w) := e.continuous.comp (hXc w)
  have hcY w : Continuous (Y' w) := e.continuous.comp (hYc w)
  have hlaw t : P.map (fun w => Y' w t)=π' := by
    change P.map (e ∘ Y (realTimeClamp (max 0 t)))=π.map e
    rw [←Measure.map_map e.continuous.measurable ((hYa t).mono (B.le _) le_rfl)]
    rw [sde_stationary_law P B L hL _ _ hLip π ξ hξ hξlaw Y hY Z hZ hinv (max 0 t) (le_max_left _ _)]
  have hcon t (ht : 0≤t) a b : ∀ᵐ w ∂P,
      ‖e (Z a (realTimeClamp t) w)-e (Z b (realTimeClamp t) w)‖≤Real.exp (-κ*t)*‖e a-e b‖ :=
    (actual_synchronous_contraction P B e g hg σ κ hmono (fun _ => a) (fun _ => b)
      (Z a) (Z b) (hZ a) (hZ b)).mono (fun w hw => hw t ht)
  have hXY t (ht : 0≤t) : ∀ᵐ w ∂P,‖X' w t-Y' w t‖≤Real.exp (-κ*t)*‖e x-Y' w 0‖ := by
    have hz : realTimeClamp (T := ⊤) 0=⊥ := by
      apply Subtype.ext
      rw [real_time_clamp_eq 0 le_rfl (by simp)]
      rfl
    filter_upwards [actual_synchronous_contraction P B e g hg σ κ hmono (fun _ => x) ξ
      (Z x) Y (hZ x) hY,hY.initial_value P (EReal.coe_lt_top 0) B.F B.W _ _ ξ Y] with w hw hw0
    simpa only [X',Y',max_eq_right ht,max_self,hz,hw0] using hw t ht
  apply coupled_unbounded_time_average_probability P π' hπ' X' Y' hmX hmY hcX hcY hlaw
    (e x) κ hκ hXY T hT hTlim _ f hf hi C hC hfg
  intro φ K hφ hb
  obtain ⟨D,hD,hDb⟩ := hb
  let a := ∫ z,φ z ∂π'
  let V := fun k w => timeAverage (fun t => φ (Y' w t)) (T k)-a
  have hV k : MemLp (V k) 2 P := by
    apply MemLp.of_bound
      ((time_average_measurable (fun w t => φ (Y' w t)) (hφ.continuous.measurable.comp hmY)
        (T k) (hT k).le).sub measurable_const).aestronglyMeasurable (D+|a|)
    apply ae_of_all
    intro w
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add
      (time_average_abs_le _ D (T k) (hT k) (fun t => hDb _)) le_rfl)
  apply l1_limit_from_second_moments P atTop V hV
  have hlim : Tendsto (fun k => (2*(K:ℝ)^2*(∫ z,‖e z‖^2 ∂π)/κ)/(T k)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hTlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun k => integral_nonneg (fun w => sq_nonneg _))
  intro k
  have hh := actual_stationary_time_average P B e L hL _ _ hLip π hπ ξ hξ hξlaw Y hY Z hZ hinv
    κ (T k) hκ (hT k) hcon φ K hφ
  have ha : a=∫ z,φ (e z) ∂π := integral_map e.continuous.measurable.aemeasurable hφ.continuous.measurable.aestronglyMeasurable
  simpa only [V,Y',ha,div_mul_eq_div_div] using hh

end Asakura.Chapter8

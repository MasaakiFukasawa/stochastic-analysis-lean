import Chapter8SDERealPathData
import Chapter8SDEIntegrableMarkov
import Chapter8SDEStationaryLaw
import Chapter8StationaryTimeAverage

open MeasureTheory Set
open scoped NNReal BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The stationary time-average estimate for actual SDE solutions. The
stationary laws, path regularity, moments and conditional Markov identity
are all derived here; only coefficient assumptions, invariant transition
integrals and the already-proved synchronous contraction are inputs. -/
theorem actual_stationary_time_average {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E)
    (L : ℝ) (hL : 0≤L)
    (b : Fin d → (Fin d → ℝ) → ℝ) (σ : Fin d → Fin n → (Fin d → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(b i x-b i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π]
    (hπ : MemLp (fun x : Fin d → ℝ => x) 2 π)
    (ξ : Ω → Fin d → ℝ) (hξ : MemLp ξ 2 P) (hξlaw : P.map ξ=π)
    (X : HalfClosedTime → Ω → Fin d → ℝ) (hX : VectorSDESolution P B.F B.W b σ ξ X)
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W b σ (fun _ => x) (Z x))
    (hinv : ∀ t : ℝ,0≤t → ∀ f : (Fin d → ℝ) → ℝ,
      ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      (∫ x,(∫ w,f (Z x (realTimeClamp t) w) ∂P) ∂π)=∫ x,f x ∂π)
    (κ T : ℝ) (hκ : 0<κ) (hT : 0<T)
    (hCon : ∀ t≥0,∀ x y,∀ᵐ w ∂P,
      ‖e (Z x (realTimeClamp t) w)-e (Z y (realTimeClamp t) w)‖≤
        Real.exp (-κ*t)*‖e x-e y‖)
    (f : E → ℝ) (Lf : ℝ≥0) (hf : LipschitzWith Lf f) :
    (∫ w,(timeAverage (fun t => f (e (X (realTimeClamp (max 0 t)) w))) T-
      (∫ x,f (e x) ∂π))^2 ∂P) ≤
      2*(Lf:ℝ)^2*(∫ x,‖e x‖^2 ∂π)/(κ*T) := by
  let π' := π.map e
  let Y := fun t w => e (X (realTimeClamp (max 0 t)) w)
  let F := fun t => B.F (realTimeClamp (max 0 t))
  let V := fun t y w => e (Z (e.symm y) (realTimeClamp (max 0 t)) w)
  haveI : IsProbabilityMeasure π' :=
    (Measure.isProbabilityMeasure_map_iff e.continuous.measurable.aemeasurable).mpr inferInstance
  have hπ' : MemLp (fun y : E => y) 2 π' := by
    apply (e.toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff).mpr
    exact e.toContinuousLinearMap.comp_memLp' hπ
  obtain ⟨hc,hm,hM,ha⟩ := sde_real_path_data P B L hL b σ hLip ξ hξ X hX
  have hlaw t : P.map (Y t)=π' := by
    have hs := sde_stationary_law P B L hL b σ hLip π ξ hξ hξlaw X hX Z hZ hinv
      (max 0 t) (le_max_left _ _)
    change P.map (e ∘ X (realTimeClamp (max 0 t)))=π.map e
    rw [←Measure.map_map e.continuous.measurable ((ha t).mono (B.le _) le_rfl),hs]
  have hVm t (_ht : 0≤t) y : MemLp (V t y) 2 P := by
    have hh := (sde_real_path_data P B L hL b σ hLip (fun _ => e.symm y)
      (memLp_const _) (Z (e.symm y)) (hZ _)).2.2.1 t
    exact e.toContinuousLinearMap.comp_memLp' hh
  have hVc t (ht : 0≤t) y y' : ∀ᵐ w ∂P,
      ‖V t y w-V t y' w‖≤Real.exp (-κ*t)*‖y-y'‖ := by
    simpa only [V,max_eq_right ht,e.apply_symm_apply] using hCon t ht (e.symm y) (e.symm y')
  have hCE s (hs : 0≤s) t (hst : s≤t) :
      P[(fun w => f (Y t w)) | F s]=ᵐ[P] fun w => ∫ y,f (V (t-s) (Y s w) y) ∂P := by
    have hfπ' := lipschitz_observable_memLp π' (fun y : E => y) hπ' f Lf hf
    have hiπ : Integrable (fun x => f (e x)) π :=
      (hfπ'.integrable (by norm_num)).comp_aemeasurable e.continuous.measurable.aemeasurable
    have hiX : Integrable (fun x => f (e x)) (P.map (X (realTimeClamp t))) := by
      rw [sde_stationary_law P B L hL b σ hLip π ξ hξ hξlaw X hX Z hZ hinv t (hs.trans hst)]
      exact hiπ
    have hh := sde_markov_integrable_expectation P B L hL b σ hLip ξ hξ X hX Z hZ
      (fun x => f (e x)) (hf.continuous.measurable.comp e.continuous.measurable)
      s t hs hst hiX
    simpa only [Y,F,V,max_eq_right hs,max_eq_right (hs.trans hst),
      max_eq_right (sub_nonneg.mpr hst),e.symm_apply_apply] using hh
  have hh := stationary_markov_time_average P π' hπ' Y
    (e.continuous.measurable.comp hm) (fun w => e.continuous.comp (hc w)) hlaw F
    (fun t => B.le _) (fun t => (e.continuous.measurable.comp (ha t)).aestronglyMeasurable)
    V hVm κ T hκ hT hVc f Lf hf hCE
  have hi := integral_map (μ := π) e.continuous.measurable.aemeasurable hf.continuous.aestronglyMeasurable
  have hn := integral_map (μ := π) e.continuous.measurable.aemeasurable
    (show AEStronglyMeasurable (fun y : E => ‖y‖^2) (π.map e) from (by fun_prop))
  simpa only [π',Y,hi,hn] using hh

end Asakura.Chapter8

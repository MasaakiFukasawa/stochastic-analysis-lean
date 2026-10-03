import Chapter8ActualTransitionRegularity
import Chapter8SDEBackwardEquation
import Chapter8BoundedSDEExpectation
import Chapter8GeneratorGrowthBridge
import Chapter8IntegratedGeneratorZero

open MeasureTheory Set
open scoped NNReal BigOperators
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxRecDepth 3000
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- For an actual smooth additive SDE, the integrated generator identity
implies preservation of smooth test integrals. Spatial and temporal
regularity are proved from the coefficients, not supplied as PDE hypotheses. -/
theorem smooth_diffusion_invariant_tests {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ}
    (B : BrownianSystem P n) (b : (Fin d → ℝ) → (Fin d → ℝ))
    (σ : Fin d → Fin n → ℝ)
    (D : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (D₂ : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (hD : ∀ z,HasFDerivAt b (D z) z) (hD₂ : ∀ z,HasFDerivAt D (D₂ z) z)
    (hcD₂ : Continuous D₂) (C L : ℝ≥0) (hDC : LipschitzWith C D)
    (hL : 0<L) (hDb : ∀ z,‖D z‖ ≤ (L:ℝ))
    (Lip : ℝ) (hLip : 0≤Lip)
    (hcoeff : ∀ x y,(∑ i,(b x i-b y i)^2)≤Lip*∑ i,(x i-y i)^2)
    (Cb : ℝ) (hCb : 0≤Cb) (hbg : ∀ x,‖b x‖≤Cb*(1+‖x‖))
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W (fun i y => b y i) (fun i j _ => σ i j) (fun _ => x) (Z x))
    (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π]
    (hπ : Integrable (fun x : Fin d → ℝ => ‖x‖) π)
    (hzero : ∀ g : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 g →
      ∀ A K : ℝ,0≤A → 0≤K → (∀ x,‖fderiv ℝ g x‖≤A) →
      (∀ x,‖fderiv ℝ (fderiv ℝ g) x‖≤K) →
      (∫ x,coordinateGenerator (fun i y => b y i) (fun i j _ => σ i j) g x ∂π)=0)
    (T : ℝ) (hT : 0≤T) (f : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (hs : HasCompactSupport f) :
    (∫ x, (∫ w,f (Z x (realTimeClamp T) w) ∂P) ∂π)=∫ x,f x ∂π := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hf1 : ContDiff ℝ (⊤:ℕ∞) (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  have hf22 : ContDiff ℝ (⊤:ℕ∞) (fderiv ℝ (fderiv ℝ f)) := (contDiff_infty_iff_fderiv.mp hf1).2
  obtain ⟨B₀,hB₀⟩ := hs.exists_bound_of_continuous hf.continuous
  obtain ⟨B₁,hB₁⟩ := (hs.fderiv ℝ).exists_bound_of_continuous hf1.continuous
  obtain ⟨B₂,hB₂⟩ := ((hs.fderiv ℝ).fderiv ℝ).exists_bound_of_continuous hf22.continuous
  have h1 x : ‖fderiv ℝ f x‖≤max B₁ 0 := (hB₁ x).trans (le_max_left _ _)
  have h2 x : ‖fderiv ℝ (fderiv ℝ f) x‖≤max B₂ 0 := (hB₂ x).trans (le_max_left _ _)
  obtain ⟨A,K,hA,hK,hreg⟩ := actual_transition_regularity P B b σ D D₂ hD hD₂ hcD₂ C L hDC hL hDb
    Z hZ T hT f hf2 B₀ (max B₁ 0) (max B₂ 0) (le_max_right _ _) (le_max_right _ _) hB₀ h1 h2
  have hcoeff' x y : (∑ i,(b x i-b y i)^2)+(∑ i : Fin d,∑ j : Fin n,(σ i j-σ i j)^2)≤Lip*∑ i,(x i-y i)^2 := by
    simpa only [sub_self,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero,add_zero] using hcoeff x y
  let G := fun t x => ∫ w,f (Z x (realTimeClamp t) w) ∂P
  let H := fun t => coordinateGenerator (fun i y => b y i) (fun i j _ => σ i j) (G t)
  have hbounded x := bounded_sde_expectation P B (fun i y => b y i) (fun i j _ => σ i j)
    x (Z x) (hZ x) f hf.continuous B₀ hB₀
  obtain ⟨Cg,hCg,hGgrowth⟩ := generator_linear_growth b σ Cb hCb hbg A K hA hK
  obtain ⟨Cf,hCf,hfgrowth⟩ := generator_linear_growth b σ Cb hCb hbg (max B₁ 0) (max B₂ 0)
    (le_max_right _ _) (le_max_right _ _)
  obtain ⟨Q,hQ,hfq,hgq⟩ := bounded_linear_polynomial_growth f _ B₀ Cf hCf hB₀ (hfgrowth f h1 h2)
  have hbc i : Continuous (fun y => b y i) :=
    (continuous_apply i).comp (continuous_iff_continuousAt.mpr (fun y => (hD y).continuousAt))
  have hhc t (ht : t∈Icc 0 T) : Continuous (H t) :=
    coordinate_generator_continuous _ _ hbc (fun _ _ => continuous_const) (G t) (hreg t ht).1
  have hd t (ht : t∈Ioo 0 T) x : HasDerivAt (fun r => G r x) (H t x) t := by
    obtain ⟨Q',hQ',hfq',hgq'⟩ := bounded_linear_polynomial_growth (G t) (H t) B₀ Cg hCg
      (fun y => (hbounded y).2 t) (hGgrowth (G t) (hreg t ⟨ht.1.le,ht.2.le⟩).2.1 (hreg t ⟨ht.1.le,ht.2.le⟩).2.2)
    exact sde_backward_equation P B (fun i y => b y i) (fun i j _ => σ i j) Lip hLip hcoeff' Z hZ
      f hf2 B₀ hB₀ 1 Q hQ hfq hgq t ht.1 (hreg t ⟨ht.1.le,ht.2.le⟩).1 1 Q' hQ' hfq' hgq' x
  have he := integrated_generator_zero_constant π G H T B₀ Cg hT (fun x => ‖x‖) hπ
    (fun t ht => (hreg t ht).1.continuous.aestronglyMeasurable)
    (fun t _ => ae_of_all _ fun x => (hbounded x).2 t)
    (ae_of_all _ fun x => (hbounded x).1.continuousOn)
    (fun t ht => (hhc t ⟨ht.1.le,ht.2.le⟩).aestronglyMeasurable)
    (ae_of_all _ fun x t ht => by
      simpa only [Real.norm_eq_abs] using hGgrowth (G t) (hreg t ⟨ht.1.le,ht.2.le⟩).2.1 (hreg t ⟨ht.1.le,ht.2.le⟩).2.2 x)
    (ae_of_all _ fun x t ht => hd t ht x)
    (fun t ht => hzero (G t) (hreg t ⟨ht.1.le,ht.2.le⟩).1 A K hA hK
      (hreg t ⟨ht.1.le,ht.2.le⟩).2.1 (hreg t ⟨ht.1.le,ht.2.le⟩).2.2)
  have hz : G 0=f := by
    exact lipschitz_transition_zero P B Lip hLip (fun i y => b y i) (fun i j _ => σ i j) hcoeff' Z hZ f
  rw [hz] at he
  exact he

end Asakura.Chapter8

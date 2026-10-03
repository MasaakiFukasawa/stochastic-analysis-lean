import Chapter6LinearGrowthDensityConstruction
import Chapter6PositiveDensityWritten
import Chapter6BrownianEndpointDensity
import Chapter6AffineMarginalBound
import Chapter6ConditionalDensityCoordinate
import Chapter6DensityLowerBound

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators ENNReal NNReal
namespace Asakura.Chapter12
open Asakura.Chapter6 Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- The continuous-linear-growth-drift density statement, with an actual
constructed Girsanov density, Lebesgue density and the exact lower bound.
The Gaussian factor is written as the equivalent transformed product pdf. -/
theorem linear_growth_positive_density_driver {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ)
    (μ : ℝ × (Fin d → ℝ) → Fin d → ℝ) (hμ : Continuous μ)
    (R : ℝ) (hR : 0<R) (K : ℝ) (hK : 0≤K)
    (hμK : ∀ r y,‖WithLp.toLp 2 (L.symm (μ (r,x+L y)))‖≤K*(1+‖WithLp.toLp 2 y‖)) :
    let b := fun z : ℝ × (Fin d → ℝ) => L.symm (μ (z.1,x+L z.2))
    let H := stoppedBrownianCoefficient P B b R hR.le
    let Y := fun w => x+L (fun i => B.W i (realTimeClamp R) w)
    let g := gaussianAffineDensity L x ⟨R,hR.le⟩
    ∃ (N : Fin d → HalfClosedTime → Ω → ℝ) (C : HalfClosedTime → Ω → ℝ)
      (Q : Measure Ω) (hQp : IsProbabilityMeasure Q) (BQ : BrownianSystem Q d) (p : (Fin d → ℝ) → ℝ),
      Measurable p ∧ (∀ᵐy∂(volume:Measure (Fin d → ℝ)),0≤p y) ∧ BQ.F=B.F ∧
      (∀ j r,0≤r → BQ.W j (realTimeClamp r)=ᵐ[Q]
        fun w => B.W j (realTimeClamp r) w-∫ s in 0..min R r,H j (realTimeClamp s) w) ∧
      (∀ j,LocalMProcessWitness P B.F (N j)) ∧
      (∀ j,ItoCovarianceFormula P B.F (B.W j) (fun z => H j (realTimeClamp z.2) z.1) (N j)) ∧
      (∀ r,0≤r → C (realTimeClamp r)=ᵐ[P] fun w => ∫ s in 0..r,∑ j,(H j (realTimeClamp s) w)^2) ∧
      Q=P.withDensity (fun w => ENNReal.ofReal (Real.exp ((∑ j,N j (realTimeClamp R) w)-C (realTimeClamp R) w/2))) ∧
      P.map Y=volume.withDensity (fun y => ENNReal.ofReal (g y)) ∧
      Q.map Y=volume.withDensity (fun y => ENNReal.ofReal (p y)) ∧
      ((fun w => p (Y w))=fun w => g (Y w)*P[(fun w => Real.exp ((∑ j,N j (realTimeClamp R) w)-C (realTimeClamp R) w/2))|MeasurableSpace.comap Y inferInstance] w) ∧
      (∀ᵐ y ∂(volume : Measure (Fin d → ℝ)),
        g y*Real.exp (-linearGrowthDensityConstant d K R*(1+‖WithLp.toLp 2 (L.symm (y-x))‖^2))≤p y) ∧
      (∀ p' : (Fin d → ℝ) → ℝ,Continuous p' → p'=ᵐ[volume] p → ∀ y,0<p' y) := by
  let b := fun z : ℝ × (Fin d → ℝ) => L.symm (μ (z.1,x+L z.2))
  have hb : Continuous b := L.symm.continuous.comp (hμ.comp (continuous_fst.prodMk (continuous_const.add (L.continuous.comp continuous_snd))))
  obtain ⟨N,C,Q,hQp,hN,hNI,hCe,hBW,hQD,hmean,q,hqm,hqe,hqmap,hqbound⟩ :=
    linear_growth_density_construction P B b hb R hR K hK (fun z => hμK _ _)
  letI := hQp
  obtain ⟨BQ,hBQ,hBWe⟩ := hBW
  let V := fun w i => B.W i (realTimeClamp R) w
  let g₀ := fun y : Fin d → ℝ => ∏ i,gaussianPDFReal 0 ⟨R,hR.le⟩ (y i)
  let a := fun y : Fin d → ℝ => Real.exp (-linearGrowthDensityConstant d K R*(1+‖WithLp.toLp 2 y‖^2))
  have htv : (⟨R,hR.le⟩ : ℝ≥0)≠0 := by intro he; exact hR.ne' (congrArg (fun v : ℝ≥0 => (v:ℝ)) he)
  have hg₀p y : 0<g₀ y := prod_pos (fun i _ => gaussianPDFReal_pos _ _ _ htv)
  have hg₀c : Continuous g₀ := by unfold g₀; simp only [gaussianPDFReal_def]; fun_prop
  have ham : Measurable a := by unfold a; fun_prop
  obtain ⟨hgp,hbase,htarget,hlower⟩ := affine_marginal_lower_bound (P.map V) (Q.map V) L x
    g₀ q a hg₀c.measurable hqm ham hg₀p (brownian_endpoint_density P B R hR) hqmap hqbound
  let g := gaussianAffineDensity L x ⟨R,hR.le⟩
  let p := fun y => g y*q (L.symm (y-x))
  have hVm : Measurable V := measurable_pi_iff.mpr (fun i =>
    ((B.martingale i).adapted P B.F _ (changed_time_finite R hR.le)).mono (B.le _) le_rfl)
  have hmap (ν : Measure Ω) : (ν.map V).map (affineMeasurableEquiv L x)=ν.map (fun w => x+L (V w)) := by
    rw [Measure.map_map (affineMeasurableEquiv L x).measurable hVm]
    rfl
  rw [hmap] at hbase htarget
  have hCE := conditional_density_coordinate_change P V (affineMeasurableEquiv L x) _ q g hqe
  have hinv y : (affineMeasurableEquiv L x).symm y=L.symm (y-x) := by
    change L.symm (-x+y)=L.symm (y-x)
    congr 1
    abel
  simp only [hinv] at hCE
  have hgc : Continuous g := continuous_const.mul (hg₀c.comp (L.symm.continuous.comp (continuous_id.sub continuous_const)))
  have hpm : Measurable p := hgc.measurable.mul (hqm.comp (L.symm.continuous.comp (continuous_id.sub continuous_const)).measurable)
  have hpn : ∀ᵐy∂(volume:Measure (Fin d → ℝ)),0≤p y := hlower.mono (fun y hy =>
    (mul_pos (hgp y) (Real.exp_pos _)).le.trans hy)
  refine ⟨N,C,Q,hQp,BQ,p,hpm,hpn,hBQ,hBWe,hN,hNI,hCe,hQD,hbase,htarget,hCE,hlower,?_⟩
  intro p' hp' he
  have hac : Continuous a := by unfold a; fun_prop
  apply continuous_density_strictly_positive volume p'
    (fun y => g y*a (L.symm (y-x))) hp' (hgc.mul (hac.comp (L.symm.continuous.comp (continuous_id.sub continuous_const))))
    (fun y => mul_pos (hgp y) (Real.exp_pos _))
  filter_upwards [hlower,he] with y hy he
  exact he ▸ hy

end Asakura.Chapter12

#print axioms Asakura.Chapter12.linear_growth_positive_density_driver

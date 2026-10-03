import Chapter8MeasurableAdditiveFlow
import FullAuditLangevinContraction
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's common-noise Wasserstein contraction with a solution
family actually constructed from the drift and continuous random forcing.
No jointly measurable solution map is assumed as an extra input. -/
theorem constructed_langevin_contraction {E Ω : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ → Ω → E) (hWm : ∀ t,Measurable (W t))
    (hWc : ∀ ω,Continuous (fun t => W t ω)) (hW0 : ∀ ω,W 0 ω=0)
    (g : E → E) (H : E → E →L[ℝ] E) (L : ℝ≥0) (κ T : ℝ) (hT : 0 ≤ T)
    (hD : ∀ x,HasFDerivAt g (H x) x) (hHb : ∀ x,‖H x‖ ≤ (L:ℝ))
    (hmono : ∀ x y,κ*‖x-y‖^2 ≤ ⟪x-y,g x-g y⟫_ℝ) :
    ∃ X : ℝ → E → Ω → E,
      (∀ t,Measurable (Function.uncurry (X t))) ∧
      (∀ x ω,Continuous (fun t => X t x ω)) ∧
      (∀ x ω t,t∈Icc 0 T → X t x ω=x-(∫ s in 0..t,g (X s x ω))+W t ω) ∧
      ∀ (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        MemLp (fun x : E => x) 2 μ → MemLp (fun x : E => x) 2 ν →
        ∀ t,t∈Icc 0 T →
        transportDistance (flowLaw μ P (X t)) (flowLaw ν P (X t)) ≤
          Real.exp (-κ*t)*transportDistance μ ν := by
  have hg : LipschitzWith L g := by
    apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hD x).differentiableAt)
    intro x
    rw [(hD x).fderiv]
    exact_mod_cast hHb x
  obtain ⟨Y,hYm,hYc,hY⟩ := measurable_additive_flow_exists (fun x => -g x) L hg.neg W hWm hWc T hT
  let X := fun t x ω => Y x t ω
  have hX x ω t (ht : t∈Icc 0 T) : X t x ω=x-(∫ s in 0..t,g (X s x ω))+W t ω := by
    simpa only [X,intervalIntegral.integral_neg,sub_eq_add_neg] using hY x ω t ht
  refine ⟨X,hYm,hYc,hX,?_⟩
  intro μ ν hμp hνp hμ hν t ht
  have hX0 x ω : X 0 x ω=x := by
    simpa only [intervalIntegral.integral_same,sub_zero,hW0,add_zero] using hX x ω 0 ⟨le_rfl,hT⟩
  have hLip : ∀ x y,∀ᵐ ω ∂P,‖X t x ω-X t y ω‖ ≤ Real.exp (-κ*t)*‖x-y‖ := by
    intro x y
    apply ae_of_all
    intro ω
    have hd := langevin_common_noise_difference (fun s => X s x ω) (fun s => X s y ω)
      (fun s => W s ω) g x y t (hYc x ω) (hYc y ω) hg.continuous
      (fun s hs => hX x ω s ⟨hs.1,hs.2.trans ht.2⟩)
      (fun s hs => hX y ω s ⟨hs.1,hs.2.trans ht.2⟩)
    have he := langevin_path_contraction (fun s => X s x ω) (fun s => X s y ω) g κ t ht.1
      (hYc x ω).continuousOn (hYc y ω).continuousOn hmono hd t ⟨ht.1,le_rfl⟩
    simpa only [hX0] using he
  haveI := quadratic_coupling_nonempty μ ν hμ hν
  exact shared_noise_transport_contraction μ ν P (X t) (hYm t) _ (Real.exp_pos _) hLip

end Asakura.Chapter8

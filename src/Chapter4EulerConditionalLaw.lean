import Chapter4BrownianSystem
import Chapter4EulerNoiseMap
import Chapter4IndependentNoiseParameter

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Euler's actual recursion has the conditional transition law of the
same recursion driven by any other Brownian system. The equality of the
joint noise laws is proved, not supplied as a hypothesis. -/
theorem euler_conditional_transition
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] {dim noise : ℕ}
    (B B₀ : BrownianSystem P noise)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Continuous (μ i)) (hσ : ∀ i j,Continuous (σ i j))
    (η : Ω → Fin dim → ℝ) (hη : Measurable[B.F ⊥] η)
    (h : ℝ) (hh : 0≤h) (n : ℕ)
    (f : (Fin dim → ℝ) → ℝ) (hf : Continuous f) (K : ℝ) (hb : ∀ x,‖f x‖≤K) :
    let q := fun x => ∫ w,f (eulerGrid μ σ (fun j r => B₀.W j (realTimeClamp r)) (fun _ => x) h n w) ∂P
    Measurable q ∧ (∀ x,‖q x‖≤K) ∧
    P[(fun w => f (eulerGrid μ σ (fun j r => B.W j (realTimeClamp r)) η h n w)) | B.F ⊥]=ᵐ[P]
      fun w => q (η w) := by
  classical
  letI : MeasurableSpace Ω := m
  dsimp only
  let Z := finiteNoiseGrid (fun j r => B.W j (realTimeClamp r)) h n
  let Z₀ := finiteNoiseGrid (fun j r => B₀.W j (realTimeClamp r)) h n
  obtain ⟨hZm,hZlaw,hZi⟩ := B.grid_law h hh n
  obtain ⟨hZ₀m,hZ₀law,_⟩ := B₀.grid_law h hh n
  let ν := P.map Z₀
  letI : IsProbabilityMeasure ν := by dsimp only [ν]; infer_instance
  have hmap : P.map Z=ν := Measure.ext_of_charFunDual (hZlaw.trans hZ₀law.symm)
  have hlaw : HasLaw Z ν P := ⟨hZm.aemeasurable,hmap⟩
  let g := fun z : (Fin dim → ℝ) × (Fin n → Fin noise → ℝ) => f (eulerNoiseMap μ σ h n z.1 z.2)
  have hgc : Continuous g := hf.comp (euler_noise_map_continuous μ σ hμ hσ h n)
  have hgb x z : ‖g (x,z)‖≤K := hb _
  have heq x : (∫ z,g (x,z) ∂ν)=∫ w,f (eulerGrid μ σ (fun j r => B₀.W j (realTimeClamp r)) (fun _ => x) h n w) ∂P := by
    have hgm : AEStronglyMeasurable (fun z => g (x,z)) (P.map Z₀) :=
      (hgc.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    change (∫ z,g (x,z) ∂P.map Z₀)=_
    rw [integral_map hZ₀m.aemeasurable hgm]
    apply integral_congr_ae
    apply ae_of_all
    intro w
    exact congrArg f (euler_noise_map_grid μ σ (fun j r => B₀.W j (realTimeClamp r)) (fun _ => x) h n w)
  obtain ⟨hqm,hqb⟩ := bounded_parameter_integral ν g hgc.measurable K hgb
  have he := independent_noise_parameter_condExp P (B.F ⊥) (B.le ⊥) Z hZm ν hlaw hZi η hη g hgc.measurable
    (fun z => hgc.comp (continuous_id.prodMk continuous_const)) K hgb
  have hleft : (fun w => g (η w,Z w))=(fun w => f (eulerGrid μ σ (fun j r => B.W j (realTimeClamp r)) η h n w)) := by
    funext w
    exact congrArg f (euler_noise_map_grid μ σ (fun j r => B.W j (realTimeClamp r)) η h n w)
  rw [hleft] at he
  simp_rw [heq] at he hqm hqb
  exact ⟨hqm,hqb,he⟩

end Asakura.Chapter4

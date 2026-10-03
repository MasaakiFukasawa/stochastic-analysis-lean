import Chapter10NoisePathGaussian
import Chapter10LinearSolutionOperator
import Chapter10LinearStateWitness

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Gaussianity of the actual linear state process, as a continuous random
path. No Gaussianity of the SDE solution is assumed. -/
theorem LinearStateWitness.gaussian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ s,‖A s‖≤K)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξg : HasGaussianLaw ξ P)
    (T : ℝ) (hT : 0≤T)
    (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X) : HasGaussianLaw X P := by
  obtain ⟨Z,_,_,hZe,hZg⟩ := initial_noise_path_gaussian P B G hG N h.noise h.ito ξ hξ hξg T hT
  obtain ⟨S,hS⟩ := linear_solution_operator_exists A hA K hAK T hT
  have he w : X w=S (ξ w,Z w) := by
    apply linear_forced_paths_unique A hA K hAK T hT (ξ w,Z w) _ _ ?_ (hS _)
    intro t
    ext i
    have hh := (h.decomposition i).decomposition (realTimeClamp t.val) (half_real_time_finite t.val) w
    have hp : finitePrefixTime T hT (realTimeClamp t.val)=t :=
      Subtype.ext (finite_prefix_time_of_real T t.val hT t.property le_top)
    rw [hp,min_eq_right (real_time_clamp_mono t.property.2)] at hh
    have hi : IntervalIntegrable (fun s => A s (X w (projIcc 0 T hT s))) volume 0 t.val := (hA.clm_apply ((X w).continuous.comp continuous_projIcc)).intervalIntegrable (μ := volume) 0 t.val
    have hc := (show (Fin d → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj i).intervalIntegral_comp_comm hi
    change (∫ s in 0..t.val,(A s (X w (projIcc 0 T hT s))) i)=(∫ s in 0..t.val,A s (X w (projIcc 0 T hT s))) i at hc
    change X w t i=ξ w i+(∫ s in 0..t.val,A s (X w (projIcc 0 T hT s))) i+Z w t i
    rw [hZe,← hc]
    exact hh
  have hg := hZg.map S
  exact hg.congr (ae_of_all _ fun w => (he w).symm)

end Asakura.Chapter10

import Chapter10BernsteinPath
import GaussianLimit
import Chapter2DominatedL2Convergence

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology unitInterval ENNReal
namespace Asakura.Chapter10
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Finite-dimensional Gaussianity gives a Gaussian random continuous path
when its path norm is square integrable. This also covers degenerate laws. -/
theorem gaussian_continuous_path {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (X : Ω → C(unitInterval,E)) (hX : MemLp X 2 P)
    (hg : ∀ n,HasGaussianLaw (fun w (k : Fin (n+1)) => X w (bernstein.z k)) P) :
    HasGaussianLaw X P := by
  let Y := fun n w => bernsteinApproximation n (X w)
  have hYg n : HasGaussianLaw (Y n) P := by
    have hh := (hg n).map (bernsteinSynthesisGeneral n E)
    simpa only [Function.comp_def,bernsteinSynthesisGeneral_apply] using hh
  have hY n : MemLp (Y n) 2 P := by
    apply hX.norm.of_le (hYg n).aemeasurable.aestronglyMeasurable
    exact ae_of_all _ fun w => by
      simpa only [norm_norm] using bernstein_path_norm_le n (X w)
  have hb : MemLp (fun w => 2*‖X w‖) 2 P := hX.norm.const_mul 2
  have hlim := Asakura.Chapter2Complete.dominated_l2_ae_convergence P
    (fun n w => ‖Y n w-X w‖) (fun _ => 0) (fun w => 2*‖X w‖) hb
    (fun n => ((hY n).aestronglyMeasurable.sub hX.aestronglyMeasurable).norm)
    aestronglyMeasurable_const
    (fun n => ae_of_all _ fun w => by
      rw [norm_norm,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤2*‖X w‖)]
      exact (norm_sub_le _ _).trans (by linarith [bernstein_path_norm_le n (X w)]))
    (ae_of_all _ fun _ => by simp)
    (ae_of_all _ fun w => by
      simpa only [sub_self,norm_zero] using
        ((bernsteinApproximation_uniform (X w)).sub_const (X w)).norm)
  have ht : Tendsto (fun n => (hY n).toLp (Y n)) atTop (𝓝 (hX.toLp X)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
    have he n : ((fun w => ‖Y n w-X w‖) - fun _ => (0:ℝ)) = fun w => ‖(Y n-X) w‖ := by
      funext w
      simp only [Pi.sub_apply,sub_zero]
    simp_rw [he] at hlim
    have hn n := eLpNorm_norm (Y n-X) ((hY n).aestronglyMeasurable.sub hX.aestronglyMeasurable) (p := 2)
    simp_rw [hn] at hlim
    exact hlim
  have hh := Asakura.gaussian_L2_limit_normed
    (fun n => (hYg n).congr ((hY n).coeFn_toLp).symm) ht
  exact hh.congr hX.coeFn_toLp

end Asakura.Chapter10

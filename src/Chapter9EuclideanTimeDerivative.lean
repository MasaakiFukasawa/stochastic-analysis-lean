import Chapter9EuclideanDensityRegularity
import Chapter9DirectionalJets
import Chapter9MixtureJets

open MeasureTheory Set
open scoped RealInnerProductSpace ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

/-- The actual time derivative of the same Euclidean mixture used by the ODE,
with its differentiated Gaussian kernel integrated against the initial law. -/
theorem euclidean_density_time_derivative {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
    (t : ℝ) (ht : 0<t) (y : EuclideanSpace ℝ (Fin d)) :
    let a := Real.exp (-t)
    let v := 1-Real.exp (-2*t)
    let c := Real.exp (-(d:ℝ)/2*Real.log (2*Real.pi*v))
    HasDerivAt (fun s => ouEuclideanDensity μ (s,y))
      (∫ x,(a^2*(‖y-a • x‖^2/v^2-(d:ℝ)/v)-a*⟪x,y-a • x⟫/v)*radialKernel c a v x y ∂μ) t := by
  let ν := μ.map WithLp.ofLp
  let p := fun z => ∫ x,Real.exp (ouExponent x z) ∂ν
  have hs := (ou_gaussian_mixture_smooth ν).contDiffAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds (show 0<(t,WithLp.ofLp y).1 from ht))
  have hd := (hs.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (WithLp.ofLp y)))
  have hd' : HasDerivAt (fun s => p (s,WithLp.ofLp y))
      (iteratedFDeriv ℝ 1 p (t,WithLp.ofLp y) (fun _ => (1,0))) t := by
    simpa only [p,iteratedFDeriv_one_apply,Function.comp_def,id_eq] using! hd
  have he : (fun s => p (s,WithLp.ofLp y))=(fun s => ouEuclideanDensity μ (s,y)) := by
    funext s
    exact (euclidean_density_coordinate_map μ (s,y)).symm
  rw [he] at hd'
  dsimp only [p] at hd'
  rw [ou_mixture_jet_apply ν 1 (t,WithLp.ofLp y) ht] at hd'
  simp_rw [ou_kernel_time_jet _ _ t ht] at hd'
  dsimp only at hd' ⊢
  have hmap : (∫ x,((Real.exp (-t))^2*((∑ i,(y i-Real.exp (-t)*x i)^2)/(1-Real.exp (-2*t))^2-
      (d:ℝ)/(1-Real.exp (-2*t)))-Real.exp (-t)*(∑ i,x i*(y i-Real.exp (-t)*x i))/(1-Real.exp (-2*t)))*
      gaussianKernel (Real.exp (-t)) (1-Real.exp (-2*t)) x (WithLp.ofLp y) ∂ν)=
      ∫ x,((Real.exp (-t))^2*(‖y-Real.exp (-t) • x‖^2/(1-Real.exp (-2*t))^2-
      (d:ℝ)/(1-Real.exp (-2*t)))-Real.exp (-t)*⟪x,y-Real.exp (-t) • x⟫/(1-Real.exp (-2*t)))*
      radialKernel (Real.exp (-(d:ℝ)/2*Real.log (2*Real.pi*(1-Real.exp (-2*t)))))
        (Real.exp (-t)) (1-Real.exp (-2*t)) x y ∂μ := by
    rw [integral_map ((WithLp.measurable_ofLp 2 _).aemeasurable) (by apply Continuous.aestronglyMeasurable; unfold gaussianKernel; fun_prop)]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only
    rw [gaussian_kernel_radial _ _ x y]
    simp only [EuclideanSpace.real_norm_sq_eq,PiLp.inner_apply,RCLike.inner_apply,
      conj_trivial,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    congr 4
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hmap] at hd'
  exact hd'
end Asakura.Chapter9

import Chapter9GaussianMoments
import Chapter9GaussianKernel

open MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter9
open Asakura.FullAudit
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def gaussianAffineLaw {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (a b : ℝ) :=
    (μ.prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).map
      (fun z => a • z.1+b • z.2)

theorem gaussian_affine_displacement_bound {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x => x) 2 μ) (a b : ℝ) :
    transportDistance (gaussianAffineLaw μ a b) μ ^2 ≤
      (a-1)^2*(∫ x,‖x‖^2 ∂μ)+b^2*d := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  have hγ : MemLp (fun x => x) 2 γ := IsGaussian.memLp_two_id
  have hx : MemLp (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => z.1) 2 (μ.prod γ) :=
    hμ.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := γ))
  have hy : MemLp (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => z.2) 2 (μ.prod γ) :=
    hγ.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := γ))
  have hdiff : MemLp (fun z => (a • z.1+b • z.2)-z.1) 2 (μ.prod γ) :=
    ((hx.const_smul a).add (hy.const_smul b)).sub hx
  have hi := (memLp_two_iff_integrable_sq_norm hdiff.aestronglyMeasurable).mp hdiff
  have hb := transport_distance_sq_le_displacement (μ.prod γ)
    (fun z => a • z.1+b • z.2) Prod.fst (by fun_prop) measurable_fst hi
  rw [(measurePreserving_fst (μ := μ) (ν := γ)).map_eq] at hb
  have he (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
      (a • z.1+b • z.2)-z.1=(a-1) • z.1+b • z.2 := by
    rw [sub_smul,one_smul]
    abel
  simp_rw [he] at hb
  rw [gaussian_affine_second_moment μ hμ (a-1) b] at hb
  exact hb

theorem ou_cutoff_bound {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x => x) 2 μ) (t : ℝ) (ht : 0≤t) :
    transportDistance (gaussianAffineLaw μ (Real.exp (-t))
      (Real.sqrt (1-Real.exp (-2*t)))) μ ^2 ≤
      (1-Real.exp (-t))^2*(∫ x,‖x‖^2 ∂μ)+(d:ℝ)*(1-Real.exp (-2*t)) := by
  have hv : 0≤1-Real.exp (-2*t) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hb := gaussian_affine_displacement_bound μ hμ (Real.exp (-t))
    (Real.sqrt (1-Real.exp (-2*t)))
  rw [Real.sq_sqrt hv] at hb
  convert hb using 1 <;> ring

theorem ou_cutoff_tendsto {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x => x) 2 μ) :
    Tendsto (fun t : ℝ => transportDistance (gaussianAffineLaw μ (Real.exp (-t))
      (Real.sqrt (1-Real.exp (-2*t)))) μ ^2) (𝓝 0) (𝓝 0) := by
  have hc : ContinuousAt (fun t : ℝ =>
      (Real.exp (-t)-1)^2*(∫ x,‖x‖^2 ∂μ)+
      (Real.sqrt (1-Real.exp (-2*t)))^2*(d:ℝ)) 0 := by fun_prop
  have hl : Tendsto (fun t : ℝ =>
      (Real.exp (-t)-1)^2*(∫ x,‖x‖^2 ∂μ)+
      (Real.sqrt (1-Real.exp (-2*t)))^2*(d:ℝ)) (𝓝 0) (𝓝 0) := by
    simpa using hc.tendsto
  exact squeeze_zero (fun t => sq_nonneg _) (fun t =>
    gaussian_affine_displacement_bound μ hμ _ _) hl
end Asakura.Chapter9

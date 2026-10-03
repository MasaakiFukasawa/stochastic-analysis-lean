import Chapter9VectorBayes
import Chapter9KernelDensity

open MeasureTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- A probability prior and normalized transition densities construct a
joint probability measure, even when the prior has atoms. -/
theorem joint_density_probability {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [SFinite ν]
    (k : A × B → ℝ) (hm : Measurable k) (hp : ∀ z,0≤k z)
    (hi : ∀ x,Integrable (fun y => k (x,y)) ν)
    (hone : ∀ x,(∫ y,k (x,y) ∂ν)=1) :
    IsProbabilityMeasure ((μ.prod ν).withDensity (fun z => ENNReal.ofReal (k z))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
  have hx x : (∫⁻ y,ENNReal.ofReal (k (x,y)) ∂ν)=1 := by
    rw [←ofReal_integral_eq_lintegral_ofReal (hi x) (ae_of_all _ (fun y => hp (x,y))),hone x]
    exact ENNReal.ofReal_one
  simp only [hx,lintegral_const,measure_univ,mul_one]

/-- Changing the reference observation measure to a positive density
divides the joint likelihood by that density. -/
theorem joint_density_reference {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (k : A × B → ℝ) (hm : Measurable k) (hp : ∀ z,0≤k z)
    (φ : B → ℝ) (hφ : Measurable φ) (hpos : ∀ y,0<φ y) :
    (μ.prod (ν.withDensity (fun y => ENNReal.ofReal (φ y)))).withDensity
      (fun z => ENNReal.ofReal (k z/φ z.2))=
      (μ.prod ν).withDensity (fun z => ENNReal.ofReal (k z)) := by
  have hm1 : Measurable (fun z : A × B => ENNReal.ofReal (φ z.2)) :=
    (hφ.comp measurable_snd).ennreal_ofReal
  have hm2 : Measurable (fun z : A × B => ENNReal.ofReal (k z/φ z.2)) :=
    (hm.div (hφ.comp measurable_snd)).ennreal_ofReal
  rw [prod_withDensity_right hφ.ennreal_ofReal,←withDensity_mul _ hm1 hm2]
  congr 1
  funext z
  dsimp only [Pi.mul_apply]
  rw [←ENNReal.ofReal_mul (hpos z.2).le]
  congr 1
  field_simp [(hpos z.2).ne']

/-- The Gaussian transition density therefore gives an actual joint law
for every initial probability measure on coordinate space. -/
theorem gaussian_joint_probability {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (a : ℝ) (v : ℝ≥0) (hv : v≠0) :
    IsProbabilityMeasure ((μ.prod volume).withDensity
      (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))) := by
  apply joint_density_probability μ volume (fun z => gaussianKernel a v z.1 z.2)
  · unfold gaussianKernel
    fun_prop
  · intro z
    exact (gaussian_kernel_positive a v z.1 z.2).le
  · intro x
    exact (gaussian_kernel_integral a v hv x).1
  · intro x
    exact (gaussian_kernel_integral a v hv x).2
end Asakura.Chapter9

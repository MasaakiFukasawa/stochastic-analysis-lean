import Chapter12BrownianTimeIsometry
import Chapter12TimeRealizationEquiv

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def brownianCoordinateInjection {d : ℕ} (T : ℝ) (i : Fin (d+1)) :
    Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) →L[ℝ] FiniteWienerHilbert d T :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin (d+1) => Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun j => if j=i then ContinuousLinearMap.id ℝ _ else 0))

theorem brownian_coordinate_injection_apply {d : ℕ} (T : ℝ) (i j : Fin (d+1))
    (u : Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) :
    brownianCoordinateProjection T j (brownianCoordinateInjection T i u)=if j=i then u else 0 := by
  classical
  by_cases h : j=i <;> simp [brownianCoordinateProjection,brownianCoordinateInjection,h]

theorem brownian_coordinate_random_injection {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d : ℕ} (T : ℝ) (i j : Fin (d+1))
    (U : Lp (Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) 2 P) :
    (brownianCoordinateProjection T j).compLp ((brownianCoordinateInjection T i).compLp U)=
      if j=i then U else 0 := by
  classical
  apply Lp.ext
  filter_upwards [(brownianCoordinateProjection T j).coeFn_compLp ((brownianCoordinateInjection T i).compLp U),
    (brownianCoordinateInjection T i).coeFn_compLp U,
    Lp.coeFn_zero (Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) 2 P] with w h1 h2 hz
  rw [h1,h2,brownian_coordinate_injection_apply]
  by_cases h : j=i
  · simp [h]
  · simp only [h,ite_false]
    exact hz.symm

theorem brownianTimeIsometry_surjective {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ} (T : ℝ) (hT : 0≤T) :
    Function.Surjective (brownianTimeIsometry (d := d) P T hT) := by
  classical
  intro v
  let U := fun i => (timeRealizationEquiv P T hT).symm (v i)
  refine ⟨∑ i,(brownianCoordinateInjection T i).compLp (U i),?_⟩
  apply PiLp.ext
  intro j
  rw [brownianTimeIsometry_apply]
  change timeRealization P T hT
    ((brownianCoordinateProjection T j).compLpL 2 P (∑ i,(brownianCoordinateInjection T i).compLp (U i)))=v j
  rw [map_sum]
  have he : (∑ i,(brownianCoordinateProjection T j).compLpL 2 P
      ((brownianCoordinateInjection T i).compLp (U i)))=U j := by
    change (∑ i,(brownianCoordinateProjection T j).compLp ((brownianCoordinateInjection T i).compLp (U i)))=U j
    simp only [brownian_coordinate_random_injection]
    simp
  rw [he,←timeRealizationEquiv_apply]
  exact (timeRealizationEquiv P T hT).apply_symm_apply _

end Asakura.Chapter12

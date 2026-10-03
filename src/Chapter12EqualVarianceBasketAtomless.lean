import Chapter12BasketAtomless
import Chapter12GaussianProductDensity
import Chapter12OrthogonalWienerLaw
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

theorem correlated_equal_variance_basket_atomless {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (d : ℕ) (e : Fin (d+1) → H) (T : ℝ≥0) (hT : T≠0)
    (he : ∀ i j,inner ℝ (e i) (e j)=if i=j then (T:ℝ) else 0)
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (hA : A.det≠0)
    (c : Fin (d+1) → ℝ) (hc : 0<c 0) (K : ℝ) :
    P {w | (∑ i,c i*Real.exp (W (∑ j,A i j • e j) w))=K}=0 := by
  let Z := fun w i => W (e i) w
  have hZm : Measurable Z := Measurable.of_eval (fun i => (Lp.stronglyMeasurable (W (e i))).measurable)
  have hZlaw := wiener_orthogonal_equal_variance_law P W hlaw e T he
  have hZac : P.map Z ≪ volume := by
    rw [hZlaw.map_eq]
    exact gaussian_product_absolutelyContinuous_volume (d+1) T hT
  let L := Matrix.toLin' A
  have hL : LinearMap.det L≠0 := by simpa only [L,LinearMap.det_toLin'] using hA
  have hac := linear_log_prices_absolutelyContinuous P d Z hZm hZac L hL
  have hm : Measurable (fun w => L (Z w)) := L.continuous_of_finiteDimensional.measurable.comp hZm
  have hz := exponential_basket_atomless_of_density P d _ hm hac c hc K
  have heq : (fun w => ∑ i,c i*Real.exp (W (∑ j,A i j • e j) w)) =ᵐ[P]
      (fun w => ∑ i,c i*Real.exp (L (Z w) i)) := by
    filter_upwards [ae_all_iff.mpr (fun i => wiener_finite_linearity P W.toLinearMap e (A i))] with w hw
    apply Finset.sum_congr rfl
    intro i _
    have hi : W (∑ j,A i j • e j) w=∑ j,A i j*W (e j) w := hw i
    exact congrArg (fun z => c i*Real.exp z) hi
  have hsets : {w | (∑ i,c i*Real.exp (W (∑ j,A i j • e j) w))=K} =ᵐ[P]
      {w | (∑ i,c i*Real.exp (L (Z w) i))=K} := heq.mono (fun w hw => by simp only [mem_setOf_eq,hw])
  exact (measure_congr hsets).trans hz

end Asakura.Chapter12

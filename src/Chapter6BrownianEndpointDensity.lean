import Chapter6BrownianGridSamplesGaussian
import Chapter6ProductDensity
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators ENNReal NNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem brownian_endpoint_product_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (t : ℝ) (ht : 0≤t) :
    P.map (fun w i => B.W i (realTimeClamp t) w)=Measure.pi (fun _ : Fin d => gaussianReal 0 ⟨t,ht⟩) := by
  let V := fun w i => B.W i (realTimeClamp t) w
  obtain ⟨hG,hmean,hcov⟩ := brownian_grid_samples_gaussian (n := 1) P B t ht
    (fun _ : Fin d => 1) (fun _ => le_rfl) id
  simp only [Nat.cast_one,one_mul,id_eq,min_self] at hG hmean hcov
  have hind : iIndepFun (fun i w => V w i) P := hG.iIndepFun_of_covariance_eq_zero
    (fun i j hij => by simpa only [hcov,if_neg hij])
  have hl i : P.map (fun w => V w i)=gaussianReal 0 ⟨t,ht⟩ := by
    have hv : Var[(fun w => V w i);P]=t := by
      simpa only [covariance_self (hG.eval i).aemeasurable,ite_true] using hcov i i
    rw [(hG.eval i).map_eq_gaussianReal,hmean i,hv]
    congr 1
    exact Real.toNNReal_of_nonneg ht
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hG.eval i).aemeasurable)).1 hind]
  congr 1
  funext i
  exact hl i

theorem brownian_endpoint_density {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (t : ℝ) (ht : 0<t) :
    P.map (fun w i => B.W i (realTimeClamp t) w)=
      (volume : Measure (Fin d → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i,gaussianPDFReal 0 ⟨t,ht.le⟩ (x i))) := by
  rw [brownian_endpoint_product_law P B t ht.le]
  exact independent_gaussian_density _ (by intro he; have hc := congrArg (fun v : ℝ≥0 => (v:ℝ)) he; exact ht.ne' hc)

end Asakura.Chapter6

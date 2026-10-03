import Chapter4BrownianSystem
import Chapter4FiniteCovarianceSum

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def brownianUnitDirection {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (hu : ∑ i,u i^2=1) : BrownianSystem P 1 where
  F := B.F
  mono := B.mono
  le := B.le
  null := B.null
  W := fun _ t w => ∑ i,u i*B.W i t w
  C := fun _ _ t w => ∑ j,u j*(∑ i,u i*B.C i j t w)
  martingale := fun _ => local_martingale_finset_sum P (by simp) B.F B.mono B.le Finset.univ
    (fun i t w => u i*B.W i t w) (fun i _ => (B.martingale i).smul P B.F (u i))
  cov := fun _ _ => weighted_covariance_sum P (by simp) B.F B.mono B.le B.W B.C u u B.cov
  clock := by
    intro j k w t ht
    have hjk : j=k := Subsingleton.elim _ _
    simp only [hjk,ite_true,B.clock _ _ w t ht,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    calc
      ∑ i,u i*(u i*t) = (∑ i,u i^2)*t := by rw [Finset.sum_mul];apply Finset.sum_congr rfl;intro i _;ring
      _ = t := by rw [hu,one_mul]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownianUnitDirection

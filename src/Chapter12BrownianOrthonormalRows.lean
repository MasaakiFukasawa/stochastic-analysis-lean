import Chapter12BrownianUnitDirection

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable def brownianOrthonormalRows {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) [IsProbabilityMeasure P] {d n:ℕ} (B:BrownianSystem P d)
    (A:Fin n → Fin d → ℝ) (hA:∀j k,∑i,A j i*A k i=if j=k then 1 else 0) :
    BrownianSystem P n where
  F := B.F
  mono := B.mono
  le := B.le
  null := B.null
  W := fun j t w => ∑i,A j i*B.W i t w
  C := fun j k t w => ∑l,A k l*(∑i,A j i*B.C i l t w)
  martingale := fun j => local_martingale_finset_sum P (by simp) B.F B.mono B.le Finset.univ
    (fun i t w => A j i*B.W i t w) (fun i _ => (B.martingale i).smul P B.F (A j i))
  cov := fun j k => weighted_covariance_sum P (by simp) B.F B.mono B.le B.W B.C (A j) (A k) B.cov
  clock := by
    intro j k w t ht
    simp only [B.clock _ _ w t ht,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    calc
      ∑i,A k i*(A j i*t)=(∑i,A j i*A k i)*t := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _=(if j=k then 1 else 0)*t := by rw [hA]
      _=if j=k then t else 0 := by split_ifs <;> simp
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownianOrthonormalRows

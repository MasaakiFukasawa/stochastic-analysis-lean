import Chapter4MatrixExpCalculus
import Chapter4FiniteItoSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Matrix Set
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The finite-sum and ordinary-integration step of the linear SDE formula.
The stochastic product identities are supplied separately by actual Ito
integration by parts. -/
theorem linear_flow_integral_assembly {dim noise : ℕ}
    (A : Matrix (Fin dim) (Fin dim) ℝ) (S : Matrix (Fin dim) (Fin noise) ℝ)
    (E : ℝ → Matrix (Fin dim) (Fin dim) ℝ)
    (hEc : ∀ i j,ContDiff ℝ 1 (fun r => E r i j))
    (hEd : ∀ r i j,HasDerivAt (fun s => E s i j) ((A*E r) i j) r)
    (hE0 : E 0=1) (y : Fin dim → ℝ) (d : ℝ) (hd : 0≤d)
    (N : Fin dim → Fin noise → ℝ → ℝ) (W : Fin noise → ℝ)
    (V : Fin dim → Fin dim → Fin noise → ℝ)
    (hNc : ∀ j k,ContinuousOn (N j k) (Icc 0 d))
    (hp : ∀ i j k,E d i j*N j k d=V i j k+∫ r in 0..d,(A*E r) i j*N j k r)
    (hV : ∀ i k,(∑ j,V i j k)=S i k*W k) :
    ∀ i,(∑ j,E d i j*(y j+∑ k,N j k d))=y i+
      (∫ r in 0..d,∑ l,A i l*(∑ j,E r l j*(y j+∑ k,N j k r)))+∑ k,S i k*W k := by
  classical
  have hDE i j : Continuous (fun r => (A*E r) i j) := by
    change Continuous (fun r => ∑ l,A i l*E r l j)
    exact continuous_finset_sum Finset.univ (fun l _ => continuous_const.mul (hEc l j).continuous)
  have hDY i j : IntervalIntegrable (fun r => (A*E r) i j*y j) volume 0 d :=
    ((hDE i j).mul continuous_const).intervalIntegrable _ _
  have hDN i j k : IntervalIntegrable (fun r => (A*E r) i j*N j k r) volume 0 d :=
    ((hDE i j).continuousOn.mul (hNc j k)).intervalIntegrable_of_Icc hd
  have hj i j : E d i j*(y j+∑ k,N j k d)=E 0 i j*y j+(∑ k,V i j k)+
      ∫ r in 0..d,(A*E r) i j*(y j+∑ k,N j k r) := by
    have hdet := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r (_ : r∈uIcc 0 d) => (hEd r i j).mul_const (y j)) (hDY i j)
    have hsum : IntervalIntegrable (fun r => ∑ k,(A*E r) i j*N j k r) volume 0 d := by
      convert IntervalIntegrable.sum Finset.univ (fun k _ => hDN i j k) using 1
      ext r
      simp only [Finset.sum_apply]
    have hint : (∫ r in 0..d,(A*E r) i j*(y j+∑ k,N j k r))=
        (∫ r in 0..d,(A*E r) i j*y j)+∑ k,∫ r in 0..d,(A*E r) i j*N j k r := by
      simp_rw [mul_add,Finset.mul_sum]
      rw [intervalIntegral.integral_add (hDY i j) hsum,
        intervalIntegral.integral_finsetSum (fun k _ => hDN i j k)]
    rw [hint,mul_add,Finset.mul_sum]
    simp_rw [hp i j]
    rw [Finset.sum_add_distrib]
    linarith
  intro i
  have hsumj j : IntervalIntegrable (fun r => (A*E r) i j*(y j+∑ k,N j k r)) volume 0 d :=
    ((hDE i j).continuousOn.mul (continuousOn_const.add
      (continuousOn_finset_sum Finset.univ (fun k _ => hNc j k)))).intervalIntegrable_of_Icc hd
  simp_rw [hj i]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← intervalIntegral.integral_finsetSum (fun j _ => hsumj j)]
  have hz : (∑ j,E 0 i j*y j)=y i := by
    simp only [hE0, Matrix.one_apply]
    simp
  have hv : (∑ j,∑ k,V i j k)=∑ k,S i k*W k := by rw [Finset.sum_comm];simp only [hV]
  rw [hz,hv]
  have hi : (∫ r in 0..d,∑ j,(A*E r) i j*(y j+∑ k,N j k r))=
      ∫ r in 0..d,∑ l,A i l*(∑ j,E r l j*(y j+∑ k,N j k r)) := by
    apply intervalIntegral.integral_congr
    intro r _
    simp only [Matrix.mul_apply,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hi]
  ring

end Asakura.Chapter4

import Chapter4MatrixExpCalculus
import Chapter4FiniteItoSum

open MeasureTheory Matrix Set Filter
open scoped Topology ENNReal BigOperators Matrix.Norms.Operator
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

lemma matrix_exp_flow_product {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t s : ℝ) :
    NormedSpace.exp (t • A)*NormedSpace.exp (s • A)=NormedSpace.exp ((t+s) • A) := by
  have hc : Commute (t • A) (s • A) := by
    change (t • A)*(s • A)=(s • A)*(t • A)
    rw [smul_mul_smul_comm,smul_mul_smul_comm,mul_comm t s]
  have hh := Matrix.exp_add_of_commute (t • A) (s • A) hc
  rw [← add_smul] at hh
  exact hh.symm

/-- At a fixed terminal time the matrix-exponential formula is the
actual convolution with exp((R-r)A), not merely a formal rearrangement. -/
theorem matrix_flow_stochastic_convolution
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t B,MeasurableSet[m] B → P B=0 → MeasurableSet[F t] B)
    (W : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    {dim : ℕ} (A : Matrix (Fin dim) (Fin dim) ℝ) (S : Fin dim → ℝ)
    (N : Fin dim → ClosedTime T → Ω → ℝ)
    (hN : ∀ j,LocalMProcessWitness P F (N j))
    (hNI : ∀ j,ItoCovarianceFormula P F W
      (fun z => ∑ k,NormedSpace.exp ((-z.2) • A) j k*S k) (N j))
    (R : ℝ) (i : Fin dim) :
    LocalMProcessWitness P F (fun t w => ∑ j,NormedSpace.exp (R • A) i j*N j t w) ∧
    ItoCovarianceFormula P F W (fun z => ∑ k,NormedSpace.exp ((R-z.2) • A) i k*S k)
      (fun t w => ∑ j,NormedSpace.exp (R • A) i j*N j t w) := by
  classical
  have hIj j : ItoCovarianceFormula P F W
      (fun z => NormedSpace.exp (R • A) i j*(∑ k,NormedSpace.exp ((-z.2) • A) j k*S k))
      (fun t w => NormedSpace.exp (R • A) i j*N j t w) := by
    have hh := (hNI j).add_smul P F hF hle W (N j) (N j) _ _ (hNI j)
      (NormedSpace.exp (R • A) i j-1)
    convert hh using 1 <;> ext z w <;> ring
  refine ⟨local_martingale_finset_sum P hT F hF hle Finset.univ _
    (fun j _ => (hN j).smul P F (NormedSpace.exp (R • A) i j)),?_⟩
  have hh := finite_ito_sum P hT F hF hle hnull W hW Finset.univ _ _ (fun j _ => hIj j)
  have he : (fun z : Ω × ℝ => ∑ j,NormedSpace.exp (R • A) i j*
      (∑ k,NormedSpace.exp ((-z.2) • A) j k*S k))=
      (fun z => ∑ k,NormedSpace.exp ((R-z.2) • A) i k*S k) := by
    funext z
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hm := congrArg (fun B : Matrix (Fin dim) (Fin dim) ℝ => ∑ k,B i k*S k)
      (matrix_exp_flow_product A R (-z.2))
    simpa only [Matrix.mul_apply,Finset.sum_mul,mul_assoc,sub_eq_add_neg] using hm
  rwa [he] at hh

end Asakura.Chapter4

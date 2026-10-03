import Chapter8MatrixOperatorExponential
import Chapter4LinearSDEConstructed
import Chapter8BrownianForcingPath

open MeasureTheory Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Construct the linear noise process in Euclidean coordinates and
identify every terminal value with the actual convolution Ito integrals. -/
theorem linear_noise_process_constructed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : Matrix (Fin d) (Fin d) ℝ) (S : Matrix (Fin d) (Fin n) ℝ) :
    ∃ (Z : ℝ → Ω → EuclideanSpace ℝ (Fin d))
      (J : ℝ → Fin d → Fin n → HalfClosedTime → Ω → ℝ),
      (∀ w,Continuous (fun r => Z r w)) ∧
      (∀ R i j,LocalMProcessWitness P B.F (J R i j)) ∧
      (∀ R i j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => (Matrix.toEuclideanCLM (𝕜 := ℝ) (NormedSpace.exp ((R-z.2) • A))
          (WithLp.toLp 2 (fun k => S k j))) i) (J R i j)) ∧
      (∀ R w,Z R w=WithLp.toLp 2 (fun i => ∑ j,J R i j (realTimeClamp R) w)) ∧
      (∀ᵐ w ∂P,∀ r≥0,Z r w=(∫ s in 0..r,Matrix.toEuclideanCLM (𝕜 := ℝ) A (Z s w))+
        ∑ j,B.W j (realTimeClamp r) w • WithLp.toLp 2 (fun i => S i j)) := by
  obtain ⟨N,hN,hNI,he⟩ := linear_sde_constructed P (show (0:EReal)<⊤ by simp)
    B.F B.mono B.le B.null B.W B.martingale (fun t _ => t.val.toReal)
    (fun _ _ => measurable_const)
    (fun w r hr _ => by rw [real_time_clamp_eq r hr le_top]; simp) A S 0
  let E0 := fun r : ℝ => NormedSpace.exp (r • A)
  let Z := fun r w => WithLp.toLp 2 (fun i => ∑ k,E0 r i k*(∑ j,N k j (realTimeClamp r) w))
  let J := fun R i j t w => ∑ k,E0 R i k*N k j t w
  have hEc i k : Continuous (fun r => E0 r i k) := (matrix_exp_entry_smooth A i k).continuous
  have hNc k j w : Continuous (fun r : ℝ => N k j (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact ((hN k j).path P B.F w _ (half_real_time_finite r)).comp real_time_clamp_continuous.continuousAt
  have hZc w : Continuous (fun r => Z r w) := by
    apply ((WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toContinuousLinearEquiv.continuous).comp
    apply continuous_pi
    intro i
    exact continuous_finsetSum _ (fun k _ => (hEc i k).mul (continuous_finsetSum _ (fun j _ => hNc k j w)))
  have hJdata R i j := matrix_flow_stochastic_convolution P (show (0:EReal)<⊤ by simp)
    B.F B.mono B.le B.null (B.W j) (B.martingale j) A (fun i => S i j)
    (fun k => N k j) (fun k => hN k j)
    (fun k => by simpa only [Matrix.mul_apply] using hNI k j) R i
  refine ⟨Z,J,hZc,(fun R i j => (hJdata R i j).1),?_,?_,?_⟩
  · intro R i j
    simpa only [Matrix.toEuclideanCLM_toLp,WithLp.ofLp_toLp,Matrix.mulVec,dotProduct] using (hJdata R i j).2
  · intro R w
    ext i
    simp only [Z,J,WithLp.ofLp_toLp,Finset.mul_sum]
    rw [Finset.sum_comm]
  · filter_upwards [he] with w hw
    intro r hr
    have hi : IntervalIntegrable (fun s => Matrix.toEuclideanCLM (𝕜 := ℝ) A (Z s w)) volume 0 r :=
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) A).continuous.comp (hZc w)).intervalIntegrable 0 r
    ext i
    have hp := (EuclideanSpace.proj i).intervalIntegral_comp_comm hi
    have heq s : (Matrix.toEuclideanCLM (𝕜 := ℝ) A (Z s w)) i=
        ∑ l,A i l*(∑ k,E0 s l k*(∑ j,N k j (realTimeClamp s) w)) := by rfl
    have hh := hw r hr (EReal.coe_lt_top r) i
    simp only [Pi.zero_apply,zero_add] at hh
    change (∑ k,E0 r i k*(∑ j,N k j (realTimeClamp r) w))=
      (∫ s in 0..r,Matrix.toEuclideanCLM (𝕜 := ℝ) A (Z s w)) i+
        (∑ j,B.W j (realTimeClamp r) w • WithLp.toLp 2 (fun k => S k j)) i
    change (∫ s in 0..r,(Matrix.toEuclideanCLM (𝕜 := ℝ) A (Z s w)) i)=(∫ s in 0..r,Matrix.toEuclideanCLM (𝕜 := ℝ) A (Z s w)) i at hp
    rw [←hp]
    simp only [ContinuousLinearMap.comp_apply,heq,WithLp.ofLp_sum,
      Finset.sum_apply,PiLp.smul_apply,WithLp.ofLp_toLp,smul_eq_mul]
    simpa only [E0,mul_comm] using hh
end Asakura.Chapter8

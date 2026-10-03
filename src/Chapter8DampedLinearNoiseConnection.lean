import Chapter8MatrixOperatorExponential
import Chapter8DampedNoiseMoment
import Chapter4LinearSDEConstructed

open MeasureTheory Matrix Set
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The convolution in the linear-SDE construction is the same actual
Ito integral whose O(m) bound was proved from isometry. -/
theorem damped_linear_noise_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (Γ : Matrix (Fin d) (Fin d) ℝ) (S : Matrix (Fin d) (Fin n) ℝ)
    (α m T : ℝ) (hα : 0<α) (hm : 0<m) (hT : 0≤T)
    (hΓ : ∀ x : EuclideanSpace ℝ (Fin d),α*‖x‖^2≤⟪x,Matrix.toEuclideanCLM (𝕜 := ℝ) Γ x⟫)
    (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => (NormedSpace.exp ((-z.2) • (-m⁻¹ • Γ))*S) i j) (N i j)) :
    (∫ w,‖WithLp.toLp 2 (fun i => ∑ k,NormedSpace.exp (T • (-m⁻¹ • Γ)) i k*
      (∑ j,N k j (realTimeClamp T) w))‖^2 ∂P)≤
        (∑ j,‖WithLp.toLp 2 (fun i => S i j)‖^2)*m/(2*α) := by
  let A := -m⁻¹ • Γ
  let E := fun r : ℝ => NormedSpace.exp (r • A)
  let b := fun j => WithLp.toLp 2 (fun i => S i j)
  obtain ⟨J,hJ,hJI,hJb⟩ := damped_noise_second_moment P B (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ)
    α m T hα hm hT hΓ b
  have hek r j i : (NormedSpace.exp (r • (-m⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) Γ)) (b j)) i=
      ∑ k,E r i k*S k j := by
    have he : Matrix.toEuclideanCLM (𝕜 := ℝ) (E r)=NormedSpace.exp (r • (-m⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) Γ)) := by
      dsimp only [E]
      rw [matrix_operator_exponential]
      congr 1
      simp only [A,map_smul]
    rw [←he]
    change ((E r) *ᵥ (fun k => S k j)) i=_
    rfl
  have hJIm i j : ItoCovarianceFormula P B.F (B.W j)
      (fun z => ∑ k,E (T-z.2) i k*S k j) (J i j) := by
    simpa only [hek] using hJI i j
  have he i j : ∀ᵐ w ∂P,∀ t,t<⊤ → (∑ k,E T i k*N k j t w)=J i j t w := by
    have hNI' k : ItoCovarianceFormula P B.F (B.W j)
        (fun z => ∑ l,NormedSpace.exp ((-z.2) • A) k l*S l j) (N k j) := by
      simpa only [A,Matrix.mul_apply] using hNI k j
    have hh := matrix_flow_stochastic_convolution P (show (0:EReal)<⊤ by simp) B.F B.mono B.le B.null
      (B.W j) (B.martingale j) A (fun i => S i j) (fun k => N k j) (fun k => hN k j) hNI' T i
    exact ItoCovarianceFormula.unique P (by simp) B.F B.mono B.le B.null (B.W j) _ _ _
      (B.martingale j) hh.1 (hJ i j) hh.2 (hJIm i j)
  have heall : ∀ᵐ w ∂P,∀ i j,∀ t,t<⊤ → (∑ k,E T i k*N k j t w)=J i j t w :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => he i j))
  have heq : (fun w => WithLp.toLp 2 (fun i => ∑ k,E T i k*(∑ j,N k j (realTimeClamp T) w)))=ᵐ[P]
      (fun w => WithLp.toLp 2 (fun i => ∑ j,J i j (realTimeClamp T) w)) := by
    filter_upwards [heall] with w hw
    ext i
    simp only [WithLp.ofLp_toLp,Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => hw i j _ (real_time_below T hT (EReal.coe_lt_top T)))
  calc
    _ = ∫ w,‖WithLp.toLp 2 (fun i => ∑ j,J i j (realTimeClamp T) w)‖^2 ∂P := by
      apply integral_congr_ae
      filter_upwards [heq] with w hw
      exact congrArg (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖^2) hw
    _ ≤ _ := hJb
end Asakura.Chapter8

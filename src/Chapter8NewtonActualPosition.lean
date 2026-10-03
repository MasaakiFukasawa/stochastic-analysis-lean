import Chapter8LinearNoiseProcess
import Chapter8NewtonMatrixRandomCoordinates
import Chapter8NewtonPositionFormula

open MeasureTheory Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

/-- Derive the position representation of the small-mass proof from the
actual Newton SDE and construct the Ito convolution appearing in its remainder. -/
theorem newton_actual_position {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (Γ : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hg : Continuous g)
    (m : ℝ) (hm : 0<m) (σ : Fin d → Fin n → ℝ)
    (ξ : Ω → Fin (d+d) → ℝ) (X : HalfClosedTime → Ω → Fin (d+d) → ℝ)
    (hX : VectorSDESolution P B.F B.W
      (Fin.addCases (fun i z => velocityProjection d z i)
        (fun i z => e.symm (-m⁻¹ • g (e (positionProjection d z))-(m⁻¹ • Γ.toContinuousLinearMap) (e (velocityProjection d z))) i))
      (Fin.addCases (fun _ _ _ => 0) (fun i j _ => m⁻¹*σ i j)) ξ X) :
    let Q := fun t w => e (positionProjection d (X (realTimeClamp t) w))
    let V0 := fun w => e (velocityProjection d (ξ w))
    let Q0 := fun w => e (positionProjection d (ξ w))
    ∃ J : ℝ → Fin d → Fin n → HalfClosedTime → Ω → ℝ,
      (∀ R i j,LocalMProcessWitness P B.F (J R i j)) ∧
      (∀ R i j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => (NormedSpace.exp ((R-z.2) • (-m⁻¹ • Γ.toContinuousLinearMap)) (e (fun k => σ k j))) i) (J R i j)) ∧
      ∀ᵐ w ∂P,∀ R≥0,
        Q R w=Q0 w-Γ.symm (∫ s in 0..R,g (Q s w))+
          Γ.symm (∑ j,B.W j (realTimeClamp R) w • e (fun i => σ i j))+
          (m • Γ.symm (V0 w-NormedSpace.exp (R • (-m⁻¹ • Γ.toContinuousLinearMap)) (V0 w))+
          Γ.symm (∫ s in 0..R,NormedSpace.exp ((R-s) • (-m⁻¹ • Γ.toContinuousLinearMap)) (g (Q s w)))-
          Γ.symm (WithLp.toLp 2 (fun i => ∑ j,J R i j (realTimeClamp R) w))) := by
  let A := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).symm (-m⁻¹ • Γ.toContinuousLinearMap)
  let S : Matrix (Fin d) (Fin n) ℝ := fun i j => e (fun k => σ k j) i
  have hA : Matrix.toEuclideanCLM (𝕜 := ℝ) A= -m⁻¹ • Γ.toContinuousLinearMap := (Matrix.toEuclideanCLM (𝕜 := ℝ)).apply_symm_apply _
  have hS j : WithLp.toLp 2 (fun i => S i j)=e (fun i => σ i j) := by ext i; rfl
  obtain ⟨Z,J,hZc,hJ,hJI,hZe,hZi⟩ := linear_noise_process_constructed P B A S
  dsimp only
  refine ⟨J,hJ,?_,?_⟩
  · intro R i j
    simpa only [matrix_operator_exponential,map_smul,hA,hS] using hJI R i j
  let Q := fun t w => e (positionProjection d (X (realTimeClamp t) w))
  let V := fun t w => e (velocityProjection d (X (realTimeClamp t) w))
  let Q0 := fun w => e (positionProjection d (ξ w))
  let V0 := fun w => e (velocityProjection d (ξ w))
  let W := fun t w => ∑ j,B.W j (realTimeClamp t) w • e (fun i => σ i j)
  have hX' : VectorSDESolution P B.F B.W
      (Fin.addCases (fun i z => velocityProjection d z i)
        (fun i z => e.symm (-(m⁻¹ • g (e (positionProjection d z)))-(m⁻¹ • Γ.toContinuousLinearMap) (e (velocityProjection d z))) i))
      (Fin.addCases (fun _ _ _ => 0) (fun i j _ => m⁻¹*σ i j)) ξ X := by
    simpa only [neg_smul] using hX
  have hg' : Continuous (fun y => m⁻¹ • g y) := by
    exact (continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin d) => (m⁻¹ : ℝ))).smul hg
  obtain ⟨hYc,hXY⟩ := newton_matrix_random_coordinates P B e (fun y => m⁻¹ • g y) hg'
    (m⁻¹ • Γ.toContinuousLinearMap) (fun i j => m⁻¹*σ i j) ξ X hX'
  filter_upwards [hXY,hZi] with w hw hz
  intro R hR
  have hQc : Continuous (fun t => Q t w) := (hYc w).fst
  have hVc : Continuous (fun t => V t w) := (hYc w).snd
  have hWscale t : (∑ j,B.W j (realTimeClamp t) w • e (fun i => m⁻¹*σ i j))=m⁻¹ • W t w := by
    have hh j : e (fun i => m⁻¹*σ i j)=m⁻¹ • e (fun i => σ i j) := e.map_smul m⁻¹ _
    simp_rw [hh]
    simp only [W,Finset.smul_sum,smul_smul,mul_comm]
  have hvi t (ht : t∈Icc 0 R) : V t w=V0 w+
      (∫ s in 0..t,(-m⁻¹) • Γ (V s w)+(-m⁻¹) • g (Q s w))+m⁻¹ • W t w := by
    have hh := hw.2.2 t ht.1
    rw [hWscale] at hh
    convert hh using 1
    congr 2
    apply intervalIntegral.integral_congr
    intro s hs
    change (-m⁻¹) • Γ (V s w)+(-m⁻¹) • g (Q s w)= -(m⁻¹ • g (Q s w))-(m⁻¹ • Γ (V s w))
    module
  have hni t (ht : t∈Icc 0 R) : m⁻¹ • Z t w=
      (∫ s in 0..t,(-m⁻¹) • Γ (m⁻¹ • Z s w))+m⁻¹ • W t w := by
    have hh := congrArg (fun z => m⁻¹ • z) (hz t ht.1)
    rw [hA] at hh
    simp only [hS,smul_add,←intervalIntegral.integral_smul,ContinuousLinearMap.smul_apply,
      ContinuousLinearEquiv.coe_coe] at hh
    convert hh using 1
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    change (-m⁻¹) • Γ (m⁻¹ • Z s w)=m⁻¹ • ((-m⁻¹) • Γ (Z s w))
    rw [map_smul,smul_smul,smul_smul,mul_comm]
  have hZscaled : Continuous (fun t => m⁻¹ • Z t w) := (continuous_const : Continuous (fun _ : ℝ => (m⁻¹ : ℝ))).smul (hZc w)
  have hp := (newton_position_formula Γ m hm.ne' (fun t => Q t w) (fun t => V t w)
    (fun t => m⁻¹ • Z t w) (fun t => W t w) g hg (Q0 w) (V0 w) R hR hQc hVc hZscaled
    (fun t ht => hw.2.1 t ht.1) hvi hni).2
  simpa only [map_smul,smul_smul,mul_inv_cancel₀ hm.ne',one_smul,hZe] using hp
end Asakura.Chapter8

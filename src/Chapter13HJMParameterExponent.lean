import Chapter13ParameterIntegralCoefficients
import Chapter13BrownianExponent

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The integrated HJM drift restriction from the original maturity fields.
The exponent, its semimartingale decomposition, and its bracket are constructed. -/
theorem hjm_parameter_exponent {Ω E:Type*} {m:MeasurableSpace Ω} [MeasurableSpace E]
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (μ:Measure E) [IsFiniteMeasure μ] (ξ:Ω → ℝ) (hξ:Measurable[B.F ⊥] ξ)
    (a:E × (Ω × ℝ) → ℝ) (σ:Fin d → E × (Ω × ℝ) → ℝ)
    (ham:Measurable a) (hσm:∀i,Measurable (σ i))
    (hap:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) => a (z.1,(z.2.1,z.2.2.val))))
    (hσp:∀i b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) => σ i (z.1,(z.2.1,z.2.2.val))))
    (hab:∀w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x r,r∈Icc 0 b → |a (x,(w,r))|≤K)
    (hσb:∀i w b,0≤b → ∃K:ℝ,0≤K ∧ ∀x r,r∈Icc 0 b → |σ i (x,(w,r))|≤K) :
    ∃(N:Fin d → HalfClosedTime → Ω → ℝ) (X A:HalfClosedTime → Ω → ℝ),
      (∀i,LocalMProcessWitness P B.F (N i)) ∧
      (∀i,ItoCovarianceFormula P B.F (B.W i) (fun z => -(∫x,σ i (x,z)∂μ)) (N i)) ∧
      SemimartingaleDecomposition P B.F X A (fun t w => ∑i,N i t w) ∧
      (∀w r,0≤r → X (realTimeClamp r) w=ξ w-(∫s in 0..r,∫x,a (x,(w,s))∂μ)+∑i,N i (realTimeClamp r) w) ∧
      (LocalMProcessWitness P B.F (fun t w => Real.exp (X t w)-Real.exp (X ⊥ w)) →
        ∀R,0≤R → ∀ᵐw∂P,∀ᵐr∂volume,r∈Ioo 0 R →
          (∫x,a (x,(w,r))∂μ)=(∑i,(∫x,σ i (x,(w,r))∂μ)^2)/2) := by
  obtain ⟨ham',hap',_,hai'⟩:=parameter_integral_coefficients B.F μ a ham hap hab
  have hσ':=fun i => parameter_integral_coefficients B.F μ (σ i) (hσm i) (hσp i) (hσb i)
  obtain ⟨N,X,A,hN,hNI,hX,hXe,hdrift⟩:=brownian_exponent_constructed P B ξ hξ
    (fun z => -(∫x,a (x,z)∂μ)) ham'.neg (fun R hR => (hap' R hR).neg) (fun w R hR => (hai' w R hR).neg)
    (fun i z => -(∫x,σ i (x,z)∂μ)) (fun i => (hσ' i).1.neg)
    (fun i R hR => ((hσ' i).2.1 R hR).neg)
    (fun i w R hR => by simpa only [neg_sq] using (hσ' i).2.2.1 w R hR)
  refine ⟨N,X,A,hN,hNI,hX,?_,?_⟩
  · intro w r hr
    simpa only [intervalIntegral.integral_neg,sub_eq_add_neg] using hXe w r hr
  · intro hE R hR
    filter_upwards [hdrift hE R hR] with w hw
    filter_upwards [hw] with r hr
    intro hri
    have hh:=hr hri
    simp only [neg_sq] at hh
    linarith
end Asakura.Chapter13
#print axioms Asakura.Chapter13.hjm_parameter_exponent

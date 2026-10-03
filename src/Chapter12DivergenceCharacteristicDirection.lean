import Chapter12DivergenceC1Direction
import Chapter12WeightedCharacteristicParts

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem divergence_characteristic_direction {Ω H:Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P:Measure Ω) [IsProbabilityMeasure P] (W:H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (D:Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD:D.IsClosed)
    (hg:(D.graph:Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (X:Lp ℝ 2 P) (V B:Lp H 2 P) (G Z:Lp ℝ 2 P)
    (hXV:(X,V)∈D.graph) (hBZ:IsDivergence D B Z)
    (c:ℝ) (hVB:∀ᵐw∂P,inner ℝ (V w) (B w)=c*G w) :
    (∫w,(Z w:ℂ)*Complex.exp (Complex.I*(X w:ℂ)) ∂P)=
      (Complex.I*(c:ℂ))*(∫w,(G w:ℂ)*Complex.exp (Complex.I*(X w:ℂ)) ∂P) := by
  apply characteristic_from_sin_cos_ibp P X G Z (Lp.aestronglyMeasurable X)
    (Lp.memLp G |>.integrable (by norm_num)) (Lp.memLp Z |>.integrable (by norm_num)) c
  · have hh := divergence_C1_direction P W S hS hcore D hD hg X V B G Z hXV hBZ c hVB
      Real.cos (fun x => -Real.sin x) Real.hasDerivAt_cos Real.continuous_sin.neg 1 (by norm_num)
      (fun x => by simpa only [abs_neg] using Real.abs_sin_le_one x)
    simpa only [mul_comm (Real.cos _) _,mul_neg,integral_neg,mul_neg,neg_mul] using hh
  · have hh := divergence_C1_direction P W S hS hcore D hD hg X V B G Z hXV hBZ c hVB
      Real.sin Real.cos Real.hasDerivAt_sin Real.continuous_cos 1 (by norm_num) Real.abs_cos_le_one
    simpa only [mul_comm (Real.sin _) _] using hh
end Asakura.Chapter12
#print axioms Asakura.Chapter12.divergence_characteristic_direction

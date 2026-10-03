import Chapter12DivergenceCharacteristicDirection
import Chapter12MalliavinLinearCombination

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem malliavin_characteristic_step {Ω I H:Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P:Measure Ω) [IsProbabilityMeasure P] (W:H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (D:Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD:D.IsClosed)
    (hg:(D.graph:Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (F:I → Lp ℝ 2 P) (U:I → Lp H 2 P) (hFU:∀j,(F j,U j)∈D.graph)
    (A:Ω → H) (i:I) (hdual:∀j,∀ᵐw∂P,inner ℝ (U j w) (A w)=if i=j then 1 else 0)
    (G Z:Lp ℝ 2 P) (B:Lp H 2 P)
    (hB:(B:Ω → H)=ᵐ[P] (fun w => G w • A w)) (hBZ:IsDivergence D B Z) (a:I → ℝ) :
    (∫w,(Z w:ℂ)*Complex.exp (Complex.I*((∑j,a j*F j w):ℂ)) ∂P)=
      (Complex.I*(a i:ℂ))*(∫w,(G w:ℂ)*Complex.exp (Complex.I*((∑j,a j*F j w):ℂ)) ∂P) := by
  obtain ⟨X,V,hXV,hX,hV⟩ := malliavin_linear_combination P D F U hFU a
  have hVB:∀ᵐw∂P,inner ℝ (V w) (B w)=a i*G w := by
    filter_upwards [hV,hB,ae_all_iff.mpr hdual] with w hv hb hd
    rw [hv,hb,real_inner_smul_right,sum_inner]
    simp only [real_inner_smul_left,hd]
    simp [mul_comm]
  have hh := divergence_characteristic_direction P W S hS hcore D hD hg X V B G Z hXV hBZ (a i) hVB
  have he (K:Lp ℝ 2 P):
      (∫w,(K w:ℂ)*Complex.exp (Complex.I*(X w:ℂ)) ∂P)=
      (∫w,(K w:ℂ)*Complex.exp (Complex.I*((∑j,a j*F j w):ℂ)) ∂P) := by
    apply integral_congr_ae
    filter_upwards [hX] with w hw
    rw [hw]
    push_cast
    rfl
  rwa [he G,he Z] at hh
end Asakura.Chapter12
#print axioms Asakura.Chapter12.malliavin_characteristic_step

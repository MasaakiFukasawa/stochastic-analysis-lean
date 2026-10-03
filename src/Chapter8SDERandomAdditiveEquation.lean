import Chapter8SDEGeneratorInterface
import Chapter4FiniteItoSum

open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000

/-- For constant diffusion, covariance uniqueness identifies each Ito
integral with its constant multiple of the Brownian coordinate. -/
theorem sde_random_additive_equation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ}
    (B : BrownianSystem P n) (b : Fin d → (Fin d → ℝ) → ℝ)
    (σ : Fin d → Fin n → ℝ) (ξ : Ω → Fin d → ℝ)
    (X : HalfClosedTime → Ω → Fin d → ℝ)
    (hX : VectorSDESolution P B.F B.W b (fun i j _ => σ i j) ξ X) :
    ∀ᵐ w ∂P, ∀ r : ℝ, 0≤r → ∀ i,
      X (realTimeClamp r) w i=ξ w i+(∫ s in 0..r,b i (X (realTimeClamp s) w))+
        ∑ j,σ i j*B.W j (realTimeClamp r) w := by
  obtain ⟨N,hN,hNI,he⟩ := hX.integrals
  have huniq i j : ∀ᵐ w ∂P, ∀ t,t<⊤ → N i j t w=σ i j*B.W j t w :=
    ItoCovarianceFormula.unique P (by simp) B.F B.mono B.le B.null (B.W j)
      (N i j) (fun t w => σ i j*B.W j t w) (fun _ => σ i j)
      (B.martingale j) (hN i j) ((B.martingale j).smul P B.F (σ i j)) (hNI i j)
      (constant_ito_integral P (by simp) B.F B.mono B.le B.null (B.W j) (B.martingale j) (σ i j))
  filter_upwards [he,ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => huniq i j))] with w hw hz
  intro r hr i
  rw [hw r hr (EReal.coe_lt_top r) i]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact hz i j _ (real_time_below r hr (EReal.coe_lt_top r))

end Asakura.Chapter8

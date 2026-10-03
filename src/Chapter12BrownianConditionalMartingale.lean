import Chapter5ItoRepresentationActual
import Chapter12VectorWienerGaussian
import Chapter12ConditionalProgressive
import Chapter12ItoIncrementPairing

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- The representation used in chapter 12 is obtained from the checked
chapter-5 construction for the same Brownian system. -/
theorem brownian_system_conditional_martingale {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (c : ℕ → ℝ) (hc : ∀ n,0<c n) (hcm : StrictMono c)
    (hct : StrictMono (fun n => realTimeClamp (T := ⊤) (c n)))
    (hcut : ∀ n,realTimeClamp (T := ⊤) (c n)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ n,t<realTimeClamp (c n))
    (hco : ∀ r : ℝ,∃ n,r≤c n) :
    let K := Σ _ : Fin (d+1),{r : ℝ // 0≤r ∧ (r:EReal)<⊤}
    ∀ U : Lp ℝ 2 P,
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w (z : K) => B.W z.1 (realTimeClamp z.2.val) w) inferInstance] U P →
      ∃ M : HalfClosedTime → Ω → ℝ,
        ContinuousM2Witness P B.F M ∧
        (U : Ω → ℝ) =ᵐ[P] fun w => (∫ z,U z ∂P)+M ⊤ w := by
  classical
  have hC i j : LocalCovarianceWitness P B.F (B.W i) (B.W j)
      (fun t w => if i=j then B.C 0 0 t w else 0) := by
    apply (B.cov i j).congr_values_before_terminal P B.F
    intro t ht
    obtain ⟨r,hr,_,he⟩ := finite_closed_time_real t ht
    rw [← he]
    funext w
    rw [B.clock i j w r hr,B.diagonal_clock 0 w r hr]
  dsimp only
  intro U hU
  obtain ⟨H,N,hN,hNI,he⟩ := brownian_ito_representation_actual P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null B.W (B.C 0 0) B.martingale hC
    (fun w r hr _ => B.diagonal_clock 0 w r hr) c hc hcm (fun _ => EReal.coe_lt_top _)
    hct hcut hcc hco U hU
  exact ⟨(fun t w => ∑ i,N i t w),finite_sum_continuous_m2 P B.F B.mono B.le N hN,he⟩

end Asakura.Chapter12

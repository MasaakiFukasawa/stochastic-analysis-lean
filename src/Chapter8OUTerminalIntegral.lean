import Chapter8SquareSemimartingaleIntegral
import Chapter8ScalarOUActualLaw
import Chapter8LongTimeRescaling
import Chapter4FiniteSDESemimartingale

open MeasureTheory Set
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- For the actual OU SDE, construct its stopped semimartingale integral
and obtain the terminal expression used to compute the MLE. -/
theorem ou_terminal_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (θ σ x : ℝ) (X : HalfClosedTime → Ω → Fin 1 → ℝ)
    (hX : VectorSDESolution P B.F B.W (fun _ y => -θ*y 0) (fun _ _ _ => σ) (fun _ _ => x) X)
    (R : ℝ) (hR : 0≤R) :
    ∃ (Y A I : HalfClosedTime → Ω → ℝ) (c : ℕ → ℝ) (hc : ∀ n,0≤c n),
      SemimartingaleDecomposition P B.F Y A (fun t w => σ*B.W 0 (min (realTimeClamp R) t) w) ∧
      (∀ᵐ w ∂P,∀ t,Y t w=X (min (realTimeClamp R) t) w 0) ∧
      SemimartingaleIntegralFormula P B.F c hc A
        (fun t w => σ*B.W 0 (min (realTimeClamp R) t) w)
        (fun z => Y (realTimeClamp z.2) z.1) I ∧
      (fun w => I (realTimeClamp R) w)=ᵐ[P]
        (fun w => ((X (realTimeClamp R) w 0)^2-x^2-σ^2*R)/2) := by
  let N := fun t w => σ*B.W 0 t w
  have hN : LocalMProcessWitness P B.F N := (B.martingale 0).smul P B.F σ
  let G := fun t w => -θ*X t w 0
  have hGa t (ht : t<⊤) : Measurable[B.F t] (G t) :=
    (((measurable_pi_apply 0).comp (hX.adapted t ht)).const_mul _)
  have hGc w t (ht : t<⊤) : ContinuousAt (fun s => G s w) t :=
    (((continuous_apply 0).continuousAt.comp (hX.path w t ht)).const_mul _)
  have he : ∀ᵐ w ∂P,∀ r∈Icc 0 R,X (realTimeClamp r) w 0=x+
      (∫ s in 0..r,G (realTimeClamp s) w)+N (realTimeClamp r) w := by
    filter_upwards [sde_additive_equation P B (fun _ y => -θ*y 0) (fun _ _ => σ) (fun _ => x) X hX] with w hw
    intro r hr
    simpa only [Fin.sum_univ_one,G,N] using hw r hr.1 0
  obtain ⟨Y,A,hY,hYc,hYe,_⟩ := finite_sde_semimartingale P (show (0:EReal)<⊤ by simp)
    B.F B.mono B.le (fun t w => X t w 0) N G (fun _ => x) measurable_const hN hGa hGc R hR (EReal.coe_lt_top _) he
  have hC := covariance_scalar_rescaling P B.F (B.W 0) (B.C 0 0) (B.cov 0 0) σ
  have hstop : ∀ t,MeasurableSet[B.F t] {w : Ω | realTimeClamp (T := ⊤) R≤t} := by
    intro t
    by_cases h : realTimeClamp (T := ⊤) R≤t <;> simp [h]
  have hCs := hC.stopped P B.F B.mono B.le _ hstop
  obtain ⟨c,hc,hcm,hct,_,_,hcc⟩ := positive_real_time_exhaustion (show (0:EReal)<⊤ by simp)
  obtain ⟨I,hI,hIe⟩ := square_semimartingale_integral P (show (0:EReal)<⊤ by simp)
    B.F B.mono B.le B.null Y A _ _ hY hCs c (fun n => (hc n).le) hcm.monotone hct hcc
  refine ⟨Y,A,I,c,(fun n => (hc n).le),hY,hYe,hI,?_⟩
  filter_upwards [hIe,hYe,hX.initial_value P (by simp) B.F B.W _ _ _ _] with w hi hy hx
  rw [hi _ (half_real_time_finite R),hy,hy]
  simp only [min_self,min_eq_right bot_le]
  rw [hx]
  rw [B.diagonal_clock 0 w R hR]
end Asakura.Chapter8

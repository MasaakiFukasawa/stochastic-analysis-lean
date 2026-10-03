import Chapter12StepTimeRealization
import Chapter12FinitePiInjection

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

theorem adapted_step_embedding {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T : ℝ) (hT : 0<T) [Fact (0≤T)]
    (F : Icc (0:ℝ) T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (i : Fin (d+1)) (a b : Icc (0:ℝ) T) (G : Ω → ℝ)
    (hG : Measurable[F a] G) (hGinf : MemLp G ∞ P) :
    let h : FiniteWienerHilbert d T := WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b))
    let hv : MemLp (fun w => G w • h) 2 P := hGinf.smul (memLp_const h (p:=2) (μ:=P))
    adaptedWienerEmbedding P T hT.le F hle
      (finitePiInjection i (timeElementaryLp P T hT F hF hle a b G hG hGinf))=hv.toLp _ := by
  classical
  dsimp only
  let h : FiniteWienerHilbert d T := WithLp.toLp 2 (Pi.single i (finiteTimeIntervalVector T a b))
  let hv : MemLp (fun w => G w • h) 2 P := hGinf.smul (memLp_const h (p:=2) (μ:=P))
  let v := hv.toLp _
  apply adapted_embedding_eq_of_time_kernel
  intro j
  have hc (j : Fin (d+1)) : Measurable (fun w => if j=i then G w else 0) := by
    by_cases hj : j=i <;> simp only [hj,ite_true,ite_false]
    · exact hG.mono (hle a) le_rfl
    · exact measurable_const
  have hvraw : (v : Ω → FiniteWienerHilbert d T)=ᵐ[P]
      (fun w => WithLp.toLp 2 (fun j => (if j=i then G w else 0) • finiteTimeIntervalVector T a b)) := by
    filter_upwards [hv.coeFn_toLp] with w hw
    rw [hw]
    apply PiLp.ext
    intro j
    by_cases hj : j=i <;> simp [h,PiLp.smul_apply,hj]
  have ht := interval_brownian_derivative_time P T hT.le a b v
    (fun j w => if j=i then G w else 0) hc hvraw j
  rw [finitePiInjection_apply]
  by_cases hj : j=i
  · simp only [hj,ite_true] at ht ⊢
    exact ht.trans (ae_eq_of_ae_eq_trim
      (time_elementary_memLp P T hT F hF hle a b G hG hGinf).coeFn_toLp).symm
  · simp only [hj,ite_false] at ht ⊢
    have hz := Lp.coeFn_zero ℝ 2 ((P.prod (compactTimeMeasure T hT.le)).trim
      (progressive_space_le_product F hle))
    exact ht.trans ((by simp : (fun z : Ω × Icc (0:ℝ) T =>
      (Ico a b).indicator (fun _ => (0:ℝ)) z.2)=ᵐ[P.prod (compactTimeMeasure T hT.le)]
        (fun _ => 0)).trans (ae_eq_of_ae_eq_trim hz).symm)

end Asakura.Chapter12

import Chapter10InnovationFutureMean

open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The innovation is a martingale in the smaller observation information.
The proof integrates its actual SDE against every observation event. -/
theorem innovation_conditional_mean {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d r n : ℕ} (B : BrownianSystem P n)
    (F : ℝ → Matrix (Fin d) (Fin d) ℝ) (L : ℝ → Matrix (Fin r) (Fin d) ℝ)
    (hF : Continuous F) (hL : Continuous L)
    (E : Fin (d+r) → Fin n → ℝ → ℝ) (hE : ∀ i j,Continuous (E i j))
    (ξ : Ω → Fin (d+r) → ℝ) (hξ : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T) (N : Fin (d+r) → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin (d+r) → ℝ))
    (h : LinearStateWitness P B
      (fun t => matrixOperatorMap (finiteBlocks (F t) 0 (L t) (0 : Matrix (Fin r) (Fin r) ℝ))) E ξ T hT N X)
    (s t : Icc (0:ℝ) T) (hst : s.val≤t.val)
    (H : MeasurableSpace Ω) (hH : H≤B.F (realTimeClamp s.val))
    (ha : ∀ j,Measurable[H] (fun w => X w s (tailIndex j)))
    (hz : ∀ u : Icc (0:ℝ) T,s.val≤u.val → ∀ i,
      P[(fun w => X w u (headIndex i))|H]=ᵐ[P] (fun _ => (0:ℝ))) (j : Fin r) :
    P[(fun w => X w t (tailIndex j))|H]=ᵐ[P] (fun w => X w s (tailIndex j)) := by
  letI : MeasurableSpace Ω := m
  let A := fun u => matrixOperatorMap (finiteBlocks (F u) 0 (L u) (0 : Matrix (Fin r) (Fin r) ℝ))
  have hHm : H≤m := hH.trans (B.le _)
  have hi u i := (h.coordinate_memLp P B A E ξ T hT N X u i).integrable (by norm_num)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hHm (hi t (tailIndex j))
    (fun _ _ _ => (hi s (tailIndex j)).integrableOn) ?_
    (ha j).stronglyMeasurable.aestronglyMeasurable).symm
  intro Q hQ _
  let η : Ω → ℝ := Q.indicator (fun _ => 1)
  have hηm : Measurable[B.F (realTimeClamp s.val)] η := measurable_const.indicator (hH Q hQ)
  have hη : MemLp η 2 P := (memLp_const (1:ℝ)).indicator (hHm Q hQ)
  have hind u i : (fun w => η w*X w u i)=Q.indicator (fun w => X w u i) := by
    funext w
    by_cases hw : w∈Q <;> simp [η,hw]
  have hzero u (hu : s.val≤u.val) i : (∫ w,η w*X w u (headIndex i) ∂P)=0 := by
    rw [hind,integral_indicator (hHm Q hQ),← setIntegral_condExp hHm (hi u (headIndex i)) hQ]
    rw [setIntegral_congr_ae (hHm Q hQ) ((hz u hu i).mono (fun w hw _ => hw))]
    simp
  have hh := innovation_future_weighted_mean P B F L hF hL E hE ξ hξ T hT N X h s t hst η hηm hη hzero j
  rw [hind,hind,integral_indicator (hHm Q hQ),integral_indicator (hHm Q hQ)] at hh
  exact hh.symm

end Asakura.Chapter10

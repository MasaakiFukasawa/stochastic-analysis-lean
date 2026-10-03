import Chapter7StrictClockCovariance
import Chapter7InverseClockODEConnection
import Chapter7NormalizeClock

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- Time-change weak-solution construction from the original clock ODE.
The coefficient is represented on real times by constant extension below
zero; only nonnegative times enter the SDE. The initial variable requires
measurability only, not integrability. -/
theorem time_change_sde_written
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (ξ : Ω → ℝ) (hξ : Measurable[B.F ⊥] ξ)
    (σ : ℝ → ℝ → ℝ) (hσ : Continuous (fun z : ℝ × ℝ => σ z.1 z.2))
    (hσn : ∀ x t,σ x t ≠ 0)
    (A : HalfClosedTime → Ω → ℝ)
    (hAa : ∀ t,t < ⊤ → Measurable[B.F t] (A t))
    (hAc : ∀ w t,t < ⊤ → ContinuousAt (fun s => A s w) t)
    (hA0 : ∀ w,A ⊥ w = 0) (hAu : ∀ w r,∃ t,t < ⊤ ∧ r < A t w)
    (hode : ∀ w r,0 < r → HasDerivAt (fun s => A (realTimeClamp s) w)
      (1/(σ (ξ w+B.W 0 (realTimeClamp r) w) (A (realTimeClamp r) w))^2) r) :
    let τ := fun r w => inverseRealClock (fun s => A s w) r
    let M := fun (t : HalfClosedTime) w => B.W 0 (τ (halfTimeReal t) w) w
    let X := fun (t : HalfClosedTime) w => ξ w+M t w
    ∃ hτ : ∀ r t,MeasurableSet[B.F t] {w | τ r w ≤ t},
      (∀ r w,τ r w < ⊤) ∧
      ∃ W : BrownianSystem P 1,
        W.F = halfClosedFiltration m (fun s : ℝ≥0 => writtenStoppedSpace m B.F (τ s) (hτ s)) ∧
        (∀ t,t < ⊤ → Measurable[W.F t] (X t)) ∧
        (∀ w t,t < ⊤ → ContinuousAt (fun s => X s w) t) ∧
        ItoCovarianceFormula P W.F M
          (fun z => 1/σ (X (realTimeClamp z.2) z.1) z.2) (W.W 0) ∧
        ∃ Z,LocalMProcessWitness P W.F Z ∧
          ItoCovarianceFormula P W.F (W.W 0)
            (fun z => σ (X (realTimeClamp z.2) z.1) z.2) Z ∧
          (∀ᵐ w ∂P,∀ t,t < ⊤ → X t w = ξ w+Z t w) := by
  let τ := fun r w => inverseRealClock (fun s => A s w) r
  let M := fun (t : HalfClosedTime) w => B.W 0 (τ (halfTimeReal t) w) w
  let X := fun (t : HalfClosedTime) w => ξ w+M t w
  let v := fun w r => σ (ξ w+B.W 0 (realTimeClamp r) w) (A (realTimeClamp r) w)
  have hT : (0:EReal) < ⊤ := by simp
  have hfinite r : realTimeClamp (T := (⊤:EReal)) r < ⊤ :=
    (real_time_clamp_mono (le_max_right 0 r)).trans_lt (changed_time_finite _ (le_max_left 0 r))
  have hvc w : Continuous (v w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact hσ.continuousAt.comp
      ((continuousAt_const.add ((B.martingale 0).path P B.F w _ (hfinite r) |>.comp
        real_time_clamp_continuous.continuousAt)).prodMk
        ((hAc w _ (hfinite r)).comp real_time_clamp_continuous.continuousAt))
  have hAm w : StrictMonoOn (fun t => A t w) (Iio ⊤) :=
    strict_clock_of_ode _ (hAc w) (v w) (fun _ _ => hσn _ _) (hode w)
  have hp w := real_clock_inverse_properties hT (fun t => A t w) (hAm w).monotoneOn
    (hAc w) (hA0 w) (hAu w)
  have hτ := real_clock_inverse_stopping hT B.F A hAa (fun w => (hAm w).monotoneOn) hAc hA0 hAu
  let G := halfClosedFiltration m (fun s : ℝ≥0 => writtenStoppedSpace m B.F (τ s) (hτ s))
  have hτt r w : τ r w < ⊤ := (hp w).2.2.1 r
  have hclock t (ht : t < ⊤) w : B.C 0 0 t w = (halfTimeReal t:ℝ) := by
    have hh := B.diagonal_clock 0 w (halfTimeReal t) (halfTimeReal t).property
    rwa [finite_clock_clamp_coordinate t ht] at hh
  have hCm w : MonotoneOn (fun t => B.C 0 0 t w) (Iio ⊤) := by
    intro s hs t ht hst
    change B.C 0 0 s w ≤ B.C 0 0 t w
    rw [hclock s hs w,hclock t ht w]
    exact half_time_real_mono hst ht
  obtain ⟨hM,hD⟩ := strict_clock_covariance P hT B.F B.mono B.le (B.W 0) (B.C 0 0)
    (B.martingale 0) (B.cov 0 0) hCm A hAa hAm hAc hA0 hAu
  let D := fun (t : HalfClosedTime) w => B.C 0 0 (τ (halfTimeReal t) w) w
  have hGm : Monotone G := half_closed_filtration_mono m _
    (fun s t hst => written_stoppedSpace_mono m B.F (τ s) (τ t) (hτ s) (hτ t)
      (fun w => (hp w).1 hst)) (fun _ _ he => he.1)
  have hGl : ∀ t,G t ≤ m := half_closed_filtration_le m _ (fun _ _ he => he.1)
  have hGn t N (hmN : MeasurableSet[m] N) (hzN : P N = 0) : MeasurableSet[G t] N := by
    by_cases ht : t < ⊤
    · have hi : writtenStoppedSpace m B.F (τ (halfTimeReal t)) (hτ _) ≤ G t := by
        simp only [G,halfClosedFiltration,if_pos ht,le_refl]
      exact hi N ⟨hmN,fun s => (B.null s N hmN hzN).inter (hτ _ s)⟩
    · have hi : m ≤ G t := by simp only [G,halfClosedFiltration,if_neg ht,le_refl]
      exact hi N hmN
  have hξG t : Measurable[G t] ξ := by
    apply hξ.mono _ le_rfl
    by_cases ht : t < ⊤
    · have hi : writtenStoppedSpace m B.F (τ (halfTimeReal t)) (hτ _) ≤ G t := by
        simp only [G,halfClosedFiltration,if_pos ht,le_refl]
      apply le_trans _ hi
      exact fun E hE => ⟨B.le ⊥ E hE,fun s => (B.mono bot_le E hE).inter (hτ _ s)⟩
    · have hi : m ≤ G t := by simp only [G,halfClosedFiltration,if_neg ht,le_refl]
      exact (B.le ⊥).trans hi
  let S := fun (t : HalfClosedTime) w => σ (X t w) (halfTimeReal t)
  have hSa t (ht : t < ⊤) : Measurable[G t] (S t) :=
    hσ.measurable.comp (((hξG t).add (hM.adapted P G t ht)).prodMk measurable_const)
  have hXc w t (ht : t < ⊤) : ContinuousAt (fun s => X s w) t :=
    continuousAt_const.add (hM.path P G w t ht)
  have hSc w t (ht : t < ⊤) : ContinuousAt (fun s => S s w) t :=
    hσ.continuousAt.comp ((hXc w t ht).prodMk (changed_time_coordinate_continuousAt t ht))
  have hDm w : MonotoneOn (fun t => D t w) (Iio ⊤) := by
    intro s hs t ht hst
    exact hCm w (hτt _ w) (hτt _ w) ((hp w).1 (half_time_real_mono hst ht))
  have hDr w r (hr : 0 ≤ r) : D (realTimeClamp r) w = (halfTimeReal (τ r w):ℝ) := by
    dsimp only [D]
    rw [changed_time_real r hr,hclock _ (hτt r w)]
  have hSr w r (hr : 0 ≤ r) : S (realTimeClamp r) w = v w (halfTimeReal (τ r w)) := by
    dsimp only [S,X,M,v]
    rw [changed_time_real r hr,finite_clock_clamp_coordinate _ (hτt r w),(hp w).2.2.2.1,max_eq_right hr]
  have hDd w r (hr : 0 < r) : HasDerivAt (fun s => D (realTimeClamp s) w) ((S (realTimeClamp r) w)^2) r := by
    have hh := (inverse_clock_ode_connection (fun t => A t w) (hAm w) (hAc w) (hA0 w) (hAu w)
      (v w) (hvc w) (fun _ _ => hσn _ _) (hode w)).1 r hr
    rw [hSr w r hr.le]
    apply hh.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact hDr w s hs.le
  obtain ⟨W,hWF,hWI,Z,hZ,hZI,hZM⟩ := normalize_clock_to_brownian P G hGm hGl hGn M D S
    hM hD hDm hSa hSc (fun w t ht => hσn _ _) hDd
  refine ⟨hτ,hτt,W,hWF,?_,hXc,?_,Z,?_,?_,?_⟩
  · intro t ht
    rw [hWF]
    exact (hξG t).add (hM.adapted P G t ht)
  · rw [hWF]
    apply hWI.congr_on_time_domain P G M (W.W 0)
      (fun z => 1/S (realTimeClamp z.2) z.1) _
    intro w r hr _
    simp only [S,X,M,τ,changed_time_real r hr]
  · rwa [hWF]
  · rw [hWF]
    apply hZI.congr_on_time_domain P G (W.W 0) Z
      (fun z => S (realTimeClamp z.2) z.1) _
    intro w r hr _
    simp only [S,X,M,τ,changed_time_real r hr]
  · filter_upwards [hZM] with w hw
    intro t ht
    change ξ w+M t w = ξ w+Z t w
    rw [hw t ht]

end Asakura.Chapter7

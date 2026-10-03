import Chapter7LocalClockTransfer
import Chapter7ClockInverseStopping
import Chapter4BrownianSystem
import Chapter7ForwardClockStopping

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- DDS for simultaneous regular representatives: both the local martingale
and its square-minus-clock are transferred from their original witnesses.
The resulting BrownianSystem has the actual time covariance, so Levy's
previously proved characterization applies. -/
theorem dds_system_from_regular_paths_with_filtration
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (hCm : ∀ w,MonotoneOn (fun t => C t w) (Iio ⊤))
    (hC0 : ∀ w,C ⊥ w = 0) (hCu : ∀ w r,∃ t,t < ⊤ ∧ r < C t w)
    (hflat : ∀ w a b,a < ⊤ → b < ⊤ → C a w = C b w → X a w = X b w) :
    ∃ B : BrownianSystem P 1,
      (∀ t w,B.W 0 t w = X (inverseRealClock (fun a => C a w) (halfTimeReal t)) w) ∧
      (∀ a,a < ⊤ → ∀ w,X a w = B.W 0 (realTimeClamp (C a w)) w) ∧
      (∀ a,a < ⊤ → ∀ t,MeasurableSet[B.F t] {w | realTimeClamp (T := (⊤:EReal)) (C a w) ≤ t}) ∧
      (∃ hτ : ∀ r t,MeasurableSet[F t] {w | inverseRealClock (fun a => C a w) r ≤ t},
        B.F = halfClosedFiltration m (fun s : ℝ≥0 =>
          ⨅ r : Ioi (s:ℝ),writtenStoppedSpace m F
            (fun w => inverseRealClock (fun a => C a w) r.val) (hτ r.val))) := by
  let τ := fun r w => inverseRealClock (fun t => C t w) r
  have hCc := local_covariance_path_continuous P F X X C hX hX hC
  have hp w := real_clock_inverse_properties hT (fun t => C t w) (hCm w) (hCc w) (hC0 w) (hCu w)
  have hτ r t : MeasurableSet[F t] {w | τ r w ≤ t} :=
    real_clock_inverse_stopping hT F C (hC.adapted P F hX hX) hCm hCc hC0 hCu r t
  have hτm w : Monotone (fun r => τ r w) := (hp w).1
  have hτ0 w : τ 0 w = ⊥ := (hp w).2.1
  have hτt r w : τ r w < ⊤ := (hp w).2.2.1 r
  have hCn w a (ha : a < ⊤) : 0 ≤ C a w := by
    simpa only [hC0 w] using hCm w (show (⊥ : ClosedTime T) < ⊤ from hT) ha bot_le
  have hBc w : Continuous (fun r => X (τ r w) w) :=
    real_clock_changed_path_continuous hT _ (hCm w) (hCc w) (hC0 w) (hCu w) _ (hX.path P F w) (hflat w)
  have hstop w a (ha : a < ⊤) r := real_clock_stopping_identities hT _ (hCm w) (hCc w)
    (hC0 w) (hCu w) _ (hflat w) a ha r
  let H := fun r => writtenStoppedSpace m F (τ r) (hτ r)
  let G := fun s : ℝ≥0 => ⨅ r : Ioi (s:ℝ),H r.val
  let G' := halfClosedFiltration m G
  let W := fun (t : HalfClosedTime) w => X (τ (halfTimeReal t) w) w
  let A := fun (t : HalfClosedTime) (_w : Ω) => (halfTimeReal t : ℝ)
  have hW : LocalMProcessWitness P G' W := local_martingale_clock_transfer P F hF hle X hX
    τ hτ hτm hτ0 hτt hBc C hCn hCm hCu (fun w a ha r => (hstop w a ha r).2)
  have hDc w : Continuous (fun r => X (τ r w) w*X (τ r w) w-C (τ r w) w) := by
    have he : (fun r => X (τ r w) w*X (τ r w) w-C (τ r w) w) =
        fun r => X (τ r w) w*X (τ r w) w-max 0 r := by
      funext r
      rw [(hp w).2.2.2.1]
    rw [he]
    exact ((hBc w).mul (hBc w)).sub (continuous_const.max continuous_id)
  have hD := local_martingale_clock_transfer P F hF hle _ hC.defect
    τ hτ hτm hτ0 hτt hDc C hCn hCm hCu (by
      intro w a ha r
      change X (min a (τ r w)) w*X (min a (τ r w)) w-C (min a (τ r w)) w =
        X (τ (min (C a w) r) w) w*X (τ (min (C a w) r) w) w-C (τ (min (C a w) r) w) w
      rw [(hstop w a ha r).1,(hstop w a ha r).2])
  have hDef : LocalMProcessWitness P G' (fun t w => W t w*W t w-A t w) := by
    have he : (fun t w => X (τ (halfTimeReal t) w) w*X (τ (halfTimeReal t) w) w-C (τ (halfTimeReal t) w) w) =
        fun t w => W t w*W t w-A t w := by
      funext t w
      rw [(hp w).2.2.2.1]
      rw [max_eq_right (show (0:ℝ) ≤ (halfTimeReal t:ℝ) from (halfTimeReal t).property)]
    rwa [he] at hD
  have hHm : Monotone H := fun a b hab => written_stoppedSpace_mono m F
    (τ a) (τ b) (hτ a) (hτ b) (fun w => hτm w hab)
  have hGm : Monotone G := fun s t hst => (right_filtration_mono H hHm).1 hst
  have hGl s : G s ≤ m :=
    (iInf_le_of_le (⟨(s:ℝ)+1,show (s:ℝ) < (s:ℝ)+1 from lt_add_one _⟩ : Ioi (s:ℝ)) le_rfl).trans (fun _ he => he.1)
  have hG'm := half_closed_filtration_mono m G hGm hGl
  have hG'l := half_closed_filtration_le m G hGl
  have hGn (s : ℝ≥0) N (hNm : MeasurableSet[m] N) (hN : P N = 0) : MeasurableSet[G s] N := by
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro r
    exact ⟨hNm,fun t => (hnull t N hNm hN).inter (hτ r.val t)⟩
  have hG'n t N (hNm : MeasurableSet[m] N) (hN : P N = 0) : MeasurableSet[G' t] N := by
    by_cases ht : t < ⊤
    · have hinc : G (halfTimeReal t) ≤ G' t := by simp only [G',halfClosedFiltration,if_pos ht,le_refl]
      exact hinc N (hGn (halfTimeReal t) N hNm hN)
    · have hinc : m ≤ G' t := by simp only [G',halfClosedFiltration,if_neg ht,le_refl]
      exact hinc N hNm
  have hAv := continuous_increasing_adapted_variation (show (0:EReal) < ⊤ by simp) G' hG'm A
    (fun _ _ => measurable_const)
    (fun _ s hs t ht hst => half_time_real_mono hst ht)
    (fun _ t ht => changed_time_coordinate_continuousAt t ht)
  let B : BrownianSystem P 1 := {
    F := G'
    mono := hG'm
    le := hG'l
    null := hG'n
    W := fun _ => W
    C := fun _ _ => A
    martingale := fun _ => hW
    cov := fun _ _ => ⟨hDef,hAv.toPathwise⟩
    clock := by
      intro j k w r hr
      simp only [Subsingleton.elim j k,ite_true]
      exact changed_time_real r hr }
  refine ⟨B,fun _ _ => rfl,?_,?_,hτ,rfl⟩
  · intro a ha w
    change X a w = X (τ (halfTimeReal (realTimeClamp (C a w))) w) w
    rw [changed_time_real _ (hCn w a ha)]
    apply hflat w a _ ha (hτt _ w)
    rw [(hp w).2.2.2.1,max_eq_right (hCn w a ha)]
  · intro a ha
    exact forward_clock_stopping hT F hF hle C (hC.adapted P F hX hX) hCm hCc hC0 hCu a ha

theorem dds_system_from_regular_paths
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (hCm : ∀ w,MonotoneOn (fun t => C t w) (Iio ⊤))
    (hC0 : ∀ w,C ⊥ w = 0) (hCu : ∀ w r,∃ t,t < ⊤ ∧ r < C t w)
    (hflat : ∀ w a b,a < ⊤ → b < ⊤ → C a w = C b w → X a w = X b w) :
    ∃ B : BrownianSystem P 1,
      (∀ t w,B.W 0 t w = X (inverseRealClock (fun a => C a w) (halfTimeReal t)) w) ∧
      (∀ a,a < ⊤ → ∀ w,X a w = B.W 0 (realTimeClamp (C a w)) w) ∧
      (∀ a,a < ⊤ → ∀ t,MeasurableSet[B.F t] {w | realTimeClamp (T := (⊤:EReal)) (C a w) ≤ t}) := by
  obtain ⟨B,hB,hr,hs,_⟩ := dds_system_from_regular_paths_with_filtration P hT F hF hle hnull
    X C hX hC hCm hC0 hCu hflat
  exact ⟨B,hB,hr,hs⟩

end Asakura.Chapter7

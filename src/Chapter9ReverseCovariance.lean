import Chapter9FiniteDriftBracket
import Chapter9ReverseCoordinateProcess

open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter5
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The reverse drift and the coordinate-product identities yield the
 actual bracket 2 δᵢⱼ times the frozen clock. -/
theorem reverse_coordinate_covariance {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → Fin d → ℝ) (hXm : ∀ r,Measurable (X r))
    (hXc : ∀ w,Continuous (fun r => X r w))
    (T b : ℝ) (hb : 0≤b) (hbT : b<T)
    (hlocal : ∀ q,ContDiff ℝ ∞ q → LocalMProcessWitness P
      (fun (t : HalfClosedTime) => reversedNaturalInformation P X T (finitePrefixTime b hb t).val)
      (fun t w => reverseCompensated μ T (fun r => X (T-r)) q (finitePrefixTime b hb t).val w))
    (i j : Fin d) :
    let p := fun t : HalfClosedTime => (finitePrefixTime b hb t).val
    let F := fun t => reversedNaturalInformation P X T (p t)
    let M := fun k t w => X (T-p t) w k-X T w k-
      ∫ r in 0..p t,ouReverseDrift μ (T-r,X (T-r) w) k
    LocalCovarianceWitness P F (M i) (M j) (fun t _ => 2*(if i=j then 1 else 0)*p t) := by
  classical
  let p := fun t : HalfClosedTime => (finitePrefixTime b hb t).val
  let F := fun t => reversedNaturalInformation P X T (p t)
  let Z := fun r w => X (T-r) w
  let a := fun k r w => ouReverseDrift μ (T-r,Z r w) k
  have hF : Monotone F := (reversed_information_monotone P X T).comp
    (fun s t hst => finite_prefix_time_mono b hb hst)
  have hle t : F t≤m := reversed_information_le P X hXm T (p t)
  have hnull t E (hE : MeasurableSet[m] E) (hPE : P E=0) : MeasurableSet[F t] E :=
    reversed_information_null P X T (p t) E hE hPE
  have hZ0 k : Measurable[F ⊥] (fun w => Z 0 w k) := by
    change Measurable[reversedNaturalInformation P X T (p ⊥)] (fun w => X (T-0) w k)
    have hp0 : p ⊥=0 := finite_prefix_bot b hb
    rw [hp0]
    exact (measurable_pi_apply k).comp (reversed_state_adapted P X T 0 le_rfl)
  have hZc k w : ContinuousOn (fun r => Z r w k) (Icc 0 b) :=
    ((continuous_apply k).comp ((hXc w).comp (by fun_prop))).continuousOn
  have ha k r (hr : r∈Icc 0 b) : Measurable[F (realTimeClamp r)] (a k r) := by
    have hpr : p (realTimeClamp r)=r := by
      dsimp only [p]
      rw [finite_prefix_time_min b r hb hr.1 le_top,min_eq_left hr.2]
    change Measurable[reversedNaturalInformation P X T (p (realTimeClamp r))] (a k r)
    rw [hpr]
    exact ((measurable_pi_apply k).comp (ou_reverse_drift_measurable μ)).comp
      (measurable_const.prodMk (reversed_state_adapted P X T r hr.1))
  have ham k w : Measurable (fun r => a k r w) :=
    ((measurable_pi_apply k).comp (ou_reverse_drift_measurable μ)).comp
      ((show Measurable (fun r : ℝ => T-r) by fun_prop).prodMk
        ((hXc w).measurable.comp (by fun_prop)))
  have hac k w : ContinuousOn (fun r => a k r w) (Icc 0 b) :=
    (ou_reverse_drift_coordinate_continuous μ k).comp
      ((show Continuous (fun r : ℝ => T-r) by fun_prop).prodMk
        ((hXc w).comp (by fun_prop))).continuousOn
      (fun r hr => ⟨show 0<T-r from sub_pos.mpr (hr.2.trans_lt hbT),mem_univ _⟩)
  have hM k := reverse_coordinate_local_martingale P μ T b hb F Z hlocal k
  have hQ := reverse_product_local_martingale P μ T b hb F Z hlocal i j
  have he := finite_drift_bracket P F hF hle hnull (fun r w => Z r w i) (fun r w => Z r w j)
    (a i) (a j) b hb (2*(if i=j then 1 else 0)) (hZ0 i) (hZ0 j) (hZc i) (hZc j)
    (ha i) (ha j) (ham i) (ham j) (hac i) (hac j) (hM i) (hM j) hQ
  simpa only [Z,a,sub_zero] using! he
end Asakura.Chapter9

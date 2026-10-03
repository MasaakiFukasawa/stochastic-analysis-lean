import Chapter3InitialWeight
import Chapter3IdentityItoIntegral
import Chapter3OpenProcessRegularity
import Chapter4PicardMapConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- An arbitrary finite initial-information scalar may multiply a local
martingale. Truncated initial weights identify the constructed Ito integral
on an increasing family of initial events. -/
theorem unbounded_initial_weight_local
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (M : ClosedTime T → Ω → ℝ) (hM : LocalMProcessWitness P F M)
    (A : Ω → ℝ) (hA : Measurable[F ⊥] A) :
    LocalMProcessWitness P F (fun t w => A w*M t w) := by
  classical
  have hAa t (_ : t<⊤) : Measurable[F t] A := hA.mono (hF bot_le) le_rfl
  have hAc w t (_ : t<⊤) : ContinuousAt (fun _ : ClosedTime T => A w) t := continuousAt_const
  have hreg := open_process_real_regularity F (fun _ w => A w) hAa hAc
  obtain ⟨N,hN,hNI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull M hM (fun z => A z.1) hreg.1 hreg.2
  let E := fun n : ℕ => {w | |A w|≤(n:ℝ)+1}
  let J := fun n => (E n).indicator (fun _ => (1:ℝ))
  let An := fun n => (E n).indicator A
  have hE n : MeasurableSet[F ⊥] (E n) := by
    letI : MeasurableSpace Ω := F ⊥
    exact measurableSet_le (continuous_abs.measurable.comp hA) measurable_const
  have hJm n : Measurable[F ⊥] (J n) := measurable_const.indicator (hE n)
  have hAnm n : Measurable[F ⊥] (An n) := hA.indicator (hE n)
  have hJb n : MemLp (J n) ∞ P := MemLp.of_bound
    ((hJm n).mono (hle ⊥) le_rfl).aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun w => by
      by_cases hw : w∈E n <;> simp [J,indicator,hw]))
  have hAnb n : MemLp (An n) ∞ P := MemLp.of_bound
    ((hAnm n).mono (hle ⊥) le_rfl).aestronglyMeasurable ((n:ℝ)+1) (Filter.Eventually.of_forall (fun w => by
      by_cases hw : w∈E n
      · simpa only [An,indicator_of_mem hw,Real.norm_eq_abs] using (show |A w|≤(n:ℝ)+1 from hw)
      · simp only [An,indicator_of_notMem hw,norm_zero];positivity))
  have he n : ∀ᵐ w ∂P,∀ t,t<⊤ → J n w*N t w=An n w*M t w := by
    have h₁ := bounded_initial_weight_ito_formula P F hF hle M N (fun z => A z.1) hNI (J n) (hJm n) (hJb n)
    have h₂ := bounded_initial_weight_ito_formula P F hF hle M M (fun _ => 1)
      (identity_ito_integral P hT F hF hle hnull M hM) (An n) (hAnm n) (hAnb n)
    have h₁' : ItoCovarianceFormula P F M (fun z => An n z.1) (fun t w => J n w*N t w) := by
      convert h₁ using 1
      funext z
      by_cases hw : z.1∈E n <;> simp [An,J,indicator,hw]
    have h₂' : ItoCovarianceFormula P F M (fun z => An n z.1) (fun t w => An n w*M t w) := by
      simpa only [mul_one] using h₂
    exact ItoCovarianceFormula.unique P hT F hF hle hnull M _ _ _ hM
      (bounded_initial_weight_local P F hF hle N hN (J n) (hJm n) (hJb n))
      (bounded_initial_weight_local P F hF hle M hM (An n) (hAnm n) (hAnb n)) h₁' h₂'
  have hall : ∀ᵐ w ∂P,∀ t,t<⊤ → N t w=A w*M t w := by
    filter_upwards [ae_all_iff.mpr he] with w hw
    obtain ⟨n,hn⟩ := exists_nat_gt |A w|
    have hwE : w∈E n := hn.le.trans (le_add_of_nonneg_right zero_le_one)
    intro t ht
    simpa only [J,An,indicator_of_mem hwE,one_mul] using hw n t ht
  exact Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P F hF hN
    (fun t ht => (hAa t ht).mul (hM.adapted P F t ht))
    (fun w t ht => continuousAt_const.mul (hM.path P F w t ht)) hall

end Asakura.Chapter4

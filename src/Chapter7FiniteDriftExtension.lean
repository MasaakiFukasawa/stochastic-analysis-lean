import Chapter7DriftedProjectionIncrement

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter7
set_option maxHeartbeats 1000000

noncomputable def finiteDriftExtension {Ω : Type*} (b : ℝ → Ω → ℝ) (T : ℝ) (r : ℝ) (w : Ω) : ℝ :=
  b (max 0 (min T r)) w

lemma finite_drift_extension {Ω : Type*} (b : ℝ → Ω → ℝ) (T : ℝ) (hT : 0≤T)
    (hb : ∀ w,ContinuousOn (fun r => b r w) (Icc 0 T)) :
    (∀ w,Continuous (fun r => finiteDriftExtension b T r w)) ∧
    (∀ r∈Icc 0 T,∀ w,finiteDriftExtension b T r w=b r w) := by
  have hm r : max 0 (min T r)∈Icc 0 T := ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩
  constructor
  · intro w
    exact (hb w).comp_continuous (continuous_const.max (continuous_const.min continuous_id)) hm
  · intro r hr w
    simp only [finiteDriftExtension,min_eq_right hr.2,max_eq_right hr.1]

lemma finite_drift_integral {Ω : Type*} (b : ℝ → Ω → ℝ) (T t : ℝ) (ht0 : 0≤t) (htT : t≤T) (w : Ω) :
    (∫ r in 0..t,finiteDriftExtension b T r w)=∫ r in 0..t,b r w := by
  rw [intervalIntegral.integral_of_le ht0,intervalIntegral.integral_of_le ht0]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  simp only [finiteDriftExtension,min_eq_right (hr.2.trans htT),max_eq_right hr.1.le]

end Asakura.Chapter7

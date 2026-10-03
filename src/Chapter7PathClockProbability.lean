import Chapter7PathSpaceTopology
import Chapter7MonotoneClockProbability

open MeasureTheory Set Filter TopologicalSpace
open scoped NNReal Topology ENNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 1500000

/-- Pointwise convergence in probability of nondecreasing clocks gives
concentration in every compact-open neighborhood of the identity path. -/
theorem monotone_clock_path_neighborhood_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : ℕ → Ω → C(ℝ≥0,ℝ≥0)) (hm : ∀ n w,Monotone (A n w))
    (hp : ∀ t : ℝ≥0,TendstoInMeasure P (fun n w => A n w t) atTop (fun _ => t))
    (U : Set C(ℝ≥0,ℝ≥0)) (hU : U ∈ 𝓝 (ContinuousMap.id ℝ≥0)) :
    Tendsto (fun n => P {w | A n w ∉ U}) atTop (𝓝 0) := by
  obtain ⟨K,ε,hε,hcontrol⟩ := path_neighborhood_control _ U hU
  let R := fun n (t : ℝ) w => (A n w t.toNNReal : ℝ)
  have hRm n w : MonotoneOn (fun t => R n t w) (Ici 0) := by
    intro s hs t ht hst
    exact_mod_cast hm n w (Real.toNNReal_le_toNNReal hst)
  have hRp t (ht : 0 ≤ t) : TendstoInMeasure P (fun n => R n t) atTop (fun _ => t) := by
    apply tendstoInMeasure_iff_dist.mpr
    intro δ hδ
    have hh := tendstoInMeasure_iff_dist.mp (hp t.toNNReal) δ hδ
    simpa only [R,NNReal.dist_eq,Real.coe_toNNReal t ht,Real.dist_eq] using hh
  have hh := monotone_clock_uniform_probability P R hRm hRp K K.property ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => bot_le)
  intro n
  apply measure_mono
  intro w hw
  by_contra hn
  apply hw
  apply hcontrol
  intro t ht
  have hnt : ¬ ε ≤ |R n (t : ℝ) w-(t : ℝ)| :=
    fun he => hn ⟨(t:ℝ),⟨t.property,by exact_mod_cast ht⟩,he⟩
  change dist (A n w t) t < ε
  simpa only [R,Real.toNNReal_coe,NNReal.dist_eq] using lt_of_not_ge hnt

end Asakura.Chapter7

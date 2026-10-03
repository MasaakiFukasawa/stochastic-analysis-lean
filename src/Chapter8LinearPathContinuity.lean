import Chapter8LinearPathStability

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter8
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Continuity of the whole solution path in a parameter, from continuous
coefficient paths and a common operator bound. -/
theorem linear_solution_parameter_continuous {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace P]
    (T : ℝ) (hT : 0 ≤ T) (L : ℝ) (hL : 0<L)
    (A : P → C(Icc (0:ℝ) T,E →L[ℝ] E))
    (R Y : P → C(Icc (0:ℝ) T,E)) (hcA : Continuous A) (hcR : Continuous R)
    (hAb : ∀ p,‖A p‖ ≤ L)
    (hY : ∀ p t,Y p t=∫ s in 0..t.val,
      A p (projIcc 0 T hT s) (Y p (projIcc 0 T hT s))+R p (projIcc 0 T hT s)) :
    Continuous Y := by
  have hb p q : ‖Y p-Y q‖ ≤ T*Real.exp (L*T)*(‖A p-A q‖*‖Y q‖+‖R p-R q‖) := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    have hp (s : ℝ) (hs : s∈Icc 0 T) : projIcc 0 T hT s=⟨s,hs⟩ := by
      apply Subtype.ext
      simp [projIcc,hs.1,hs.2]
    have he p s (hs : s∈Icc 0 T) := hY p ⟨s,hs⟩
    have hh := linear_path_stability
      (fun s => A p (projIcc 0 T hT s)) (fun s => A q (projIcc 0 T hT s))
      (fun s => R p (projIcc 0 T hT s)) (fun s => R q (projIcc 0 T hT s))
      (fun s => Y p (projIcc 0 T hT s)) (fun s => Y q (projIcc 0 T hT s))
      ((A p).continuous.comp continuous_projIcc) ((A q).continuous.comp continuous_projIcc)
      ((R p).continuous.comp continuous_projIcc) ((R q).continuous.comp continuous_projIcc)
      ((Y p).continuous.comp continuous_projIcc) ((Y q).continuous.comp continuous_projIcc)
      T L ‖A p-A q‖ ‖R p-R q‖ ‖Y q‖ hT hL (norm_nonneg (A p-A q)) (norm_nonneg (R p-R q)) (norm_nonneg (Y q))
      (fun s _ => ((A p).norm_coe_le_norm _).trans (hAb p))
      (fun s _ => (A p-A q).norm_coe_le_norm _) (fun s _ => (R p-R q).norm_coe_le_norm _)
      (fun s _ => (Y q).norm_coe_le_norm _)
      (fun s hs => by simpa only [hp s hs] using he p s hs)
      (fun s hs => by simpa only [hp s hs] using he q s hs) t.val t.property
    have hpt : projIcc 0 T hT t.val=t := by
      apply Subtype.ext
      simp [projIcc,t.property.1,t.property.2]
    change ‖Y p t-Y q t‖ ≤ _
    simpa only [hpt] using hh
  apply continuous_iff_continuousAt.mpr
  intro q
  have hnA : Continuous (fun p => ‖A p-A q‖) := by
    exact (continuous_norm (E := C(Icc (0:ℝ) T,E →L[ℝ] E))).comp (hcA.sub continuous_const)
  have hnR : Continuous (fun p => ‖R p-R q‖) := (hcR.sub continuous_const).norm
  have hc : Continuous (fun p => T*Real.exp (L*T)*(‖A p-A q‖*‖Y q‖+‖R p-R q‖)) :=
    continuous_const.mul ((hnA.mul continuous_const).add hnR)
  have hz : ‖A q-A q‖=0 := by
    rw [sub_self]
    exact norm_zero (E := C(Icc (0:ℝ) T,E →L[ℝ] E))
  have hzR : ‖R q-R q‖=0 := by simp
  have ht : Tendsto (fun p => T*Real.exp (L*T)*(‖A p-A q‖*‖Y q‖+‖R p-R q‖)) (𝓝 q) (𝓝 0) := by
    simpa only [hz,hzR,zero_mul,add_zero,mul_zero] using hc.continuousAt.tendsto (x := q)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp ht).2 ε hε] with p hp
  rw [dist_eq_norm]
  exact (hb p q).trans_lt hp

end Asakura.Chapter8

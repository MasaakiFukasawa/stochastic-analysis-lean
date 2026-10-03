import Chapter4PathRestriction
import Chapter4VolterraPathLimit
import Chapter4NormEnvelope

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

lemma prefix_norm_monotone_on {R : ℝ} (hR : 0≤R) (Y : C(Icc (0:ℝ) R,ℝ)) :
    MonotoneOn (fun r => ‖prefixPath hR Y r‖) (Icc 0 R) := by
  intro s hs t ht hst
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro r
  have hh := (prefixPath hR Y t).norm_coe_le_norm (min r ⟨s,hs⟩)
  change ‖Y (min (min r ⟨s,hs⟩) (projIcc 0 R hR t))‖≤_ at hh
  rw [projIcc_of_mem hR ht,min_eq_left ((min_le_right _ _).trans (show (⟨s,hs⟩ : Icc 0 R)≤⟨t,ht⟩ from hst))] at hh
  change ‖Y (min r (projIcc 0 R hR s))‖≤_
  rwa [projIcc_of_mem hR hs]

noncomputable def runningNormPath {R : ℝ} (hR : 0≤R) (Y : C(Icc (0:ℝ) R,ℝ)) :
    C(Icc (0:ℝ) R,ℝ) :=
  ⟨fun r => ‖prefixPath hR Y r.val‖,((prefix_path_time_continuous hR Y).norm).comp continuous_subtype_val⟩

lemma running_norm_path_prefix {R : ℝ} (hR : 0≤R) (Y : C(Icc (0:ℝ) R,ℝ))
    (t : ℝ) (ht : t∈Icc 0 R) :
    ‖prefixPath hR (runningNormPath hR Y) t‖=‖prefixPath hR Y t‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro r
    change ‖‖prefixPath hR Y (min r (projIcc 0 R hR t)).val‖‖≤_
    rw [norm_norm,projIcc_of_mem hR ht]
    apply prefix_norm_monotone_on hR Y (min r ⟨t,ht⟩).property ht
    exact min_le_right _ _
  · have hh := (prefixPath hR (runningNormPath hR Y) t).norm_coe_le_norm ⟨t,ht⟩
    change ‖‖prefixPath hR Y (min (⟨t,ht⟩ : Icc 0 R) (projIcc 0 R hR t)).val‖‖≤_ at hh
    simpa only [projIcc_of_mem hR ht,min_self,norm_norm] using hh

lemma running_norm_path_norm {R : ℝ} (hR : 0≤R) (Y : C(Icc (0:ℝ) R,ℝ)) :
    ‖runningNormPath hR Y‖=‖Y‖ := by
  simpa only [prefix_path_endpoint] using running_norm_path_prefix hR Y R ⟨hR,le_rfl⟩

lemma running_norm_path_measurable {Ω : Type*} [MeasurableSpace Ω]
    {R : ℝ} (hR : 0≤R) (Y : Ω → C(Icc (0:ℝ) R,ℝ)) (hm : Measurable Y) :
    Measurable (fun w => runningNormPath hR (Y w)) :=
  ContinuousMap.measurable_iff_eval.mpr fun r => (prefix_path_measurable hR Y hm r.val).norm

lemma running_norm_path_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {R : ℝ} (hR : 0≤R) (Y : Ω → C(Icc (0:ℝ) R,ℝ)) (hm : Measurable Y)
    (p : ℝ≥0∞) (hi : MemLp Y p P) : MemLp (fun w => runningNormPath hR (Y w)) p P := by
  apply hi.of_le_mul (c:=1) (running_norm_path_measurable hR Y hm).aestronglyMeasurable
  exact ae_of_all _ fun w => by rw [running_norm_path_norm,one_mul]

end Asakura.Chapter4

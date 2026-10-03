import Chapter4VectorPrefixMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
variable {dim : ℕ}
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

noncomputable def restrictRealPath {R d : ℝ} (hdR : d≤R)
    (Y : C(Icc (0:ℝ) R,Fin dim → ℝ)) : C(Icc (0:ℝ) d,Fin dim → ℝ) :=
  ⟨fun t => Y ⟨t.val,t.property.1,t.property.2.trans hdR⟩,
    Y.continuous.comp (continuous_subtype_val.subtype_mk _)⟩

lemma restrict_real_path_norm_le {R d : ℝ} (hdR : d≤R) (Y : C(Icc (0:ℝ) R,Fin dim → ℝ)) :
    ‖restrictRealPath hdR Y‖≤‖Y‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro r
  exact ContinuousMap.norm_coe_le_norm Y _

lemma restrict_real_path_measurable {Ω : Type*} [MeasurableSpace Ω]
    {R d : ℝ} (hdR : d≤R) (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (hm : Measurable Y) :
    Measurable (fun w => restrictRealPath hdR (Y w)) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  change Measurable (fun w => Y w ⟨r.val,r.property.1,r.property.2.trans hdR⟩)
  exact (continuous_eval_const _).measurable.comp hm

lemma restrict_real_path_memLp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {R d : ℝ} (hdR : d≤R) (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (hm : Measurable Y) (hi : MemLp Y 2 P) :
    MemLp (fun w => restrictRealPath hdR (Y w)) 2 P := by
  apply hi.of_le_mul (c := 1) (restrict_real_path_measurable hdR Y hm).aestronglyMeasurable
  exact .of_forall (fun w => by simpa only [one_mul] using restrict_real_path_norm_le hdR (Y w))

lemma restrict_real_path_sub {R d : ℝ} (hdR : d≤R) (Y Z : C(Icc (0:ℝ) R,Fin dim → ℝ)) :
    restrictRealPath hdR (Y-Z)=restrictRealPath hdR Y-restrictRealPath hdR Z := by ext r; rfl

lemma interval_min_mk {a b : ℝ} (s t : Icc a b) :
    min s t=⟨min s.val t.val,le_min s.property.1 t.property.1,(min_le_left _ _).trans s.property.2⟩ := by
  apply Subtype.ext
  simp only [min_def]
  split_ifs <;> first | rfl | contradiction

lemma restriction_eq_prefix_norm {R d : ℝ} (hd : 0≤d) (hdR : d≤R)
    (Y : C(Icc (0:ℝ) R,Fin dim → ℝ)) :
    ‖restrictRealPath hdR Y‖=‖prefixPath (hd.trans hdR) Y d‖ := by
  have hp : projIcc 0 R (hd.trans hdR) d=⟨d,hd,hdR⟩ := projIcc_of_mem _ ⟨hd,hdR⟩
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro r
    have h := ContinuousMap.norm_coe_le_norm (prefixPath (hd.trans hdR) Y d)
      ⟨r.val,r.property.1,r.property.2.trans hdR⟩
    simpa only [restrictRealPath,prefixPath,ContinuousMap.coe_mk,hp,min_eq_left (show (⟨r.val,r.property.1,r.property.2.trans hdR⟩ : Icc (0:ℝ) R)≤⟨d,hd,hdR⟩ from r.property.2)] using h
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro r
    have h := ContinuousMap.norm_coe_le_norm (restrictRealPath hdR Y)
      ⟨min r.val d,le_min r.property.1 hd,min_le_right _ _⟩
    simpa only [prefixPath,restrictRealPath,ContinuousMap.coe_mk,hp,interval_min_mk] using h

lemma restricted_prefix_norm {R d : ℝ} (hd : 0≤d) (hdR : d≤R)
    (Y : C(Icc (0:ℝ) R,Fin dim → ℝ)) (t : ℝ) (ht : t∈Icc 0 d) :
    ‖prefixPath hd (restrictRealPath hdR Y) t‖=‖prefixPath (hd.trans hdR) Y t‖ := by
  have htd : projIcc 0 d hd t=⟨t,ht⟩ := projIcc_of_mem _ ht
  have htR : projIcc 0 R (hd.trans hdR) t=⟨t,ht.1,ht.2.trans hdR⟩ := projIcc_of_mem _ ⟨ht.1,ht.2.trans hdR⟩
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro r
    have h := ContinuousMap.norm_coe_le_norm (prefixPath (hd.trans hdR) Y t)
      ⟨r.val,r.property.1,r.property.2.trans hdR⟩
    simpa only [prefixPath,restrictRealPath,ContinuousMap.coe_mk,htd,htR,interval_min_mk] using h
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro r
    have h := ContinuousMap.norm_coe_le_norm (prefixPath hd (restrictRealPath hdR Y) t)
      ⟨min r.val t,le_min r.property.1 ht.1,(min_le_right _ _).trans ht.2⟩
    simpa only [prefixPath,restrictRealPath,ContinuousMap.coe_mk,htd,htR,interval_min_mk,min_assoc,min_self] using h

end Asakura.Chapter4.Vector

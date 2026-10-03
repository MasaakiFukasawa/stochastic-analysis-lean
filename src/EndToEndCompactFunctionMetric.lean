import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.PiNat

open Set Filter Metric
open scoped Topology PiCountable
namespace Asakura.EndToEnd
set_option backward.isDefEq.respectTransparency false

section CompactCover
variable {A F : Type*} [TopologicalSpace A] [MetricSpace F]
variable (K : ℕ → Set A) [∀ n, CompactSpace (K n)]

def compactRestrictions (f : C(A,F)) (n : ℕ) : C(K n,F) :=
  f.comp ⟨Subtype.val,continuous_subtype_val⟩

theorem compactRestrictions_embedding
    (hcover : ∀ S : Set A, IsCompact S → ∃ n, S ⊆ K n) :
    IsUniformEmbedding (compactRestrictions (F:=F) K) := by
  have hu : UniformContinuous (compactRestrictions (F:=F) K) := by
    apply uniformContinuous_pi.mpr
    intro n
    exact ContinuousMap.uniformContinuous_comp_left ⟨Subtype.val,continuous_subtype_val⟩
  have hind : IsUniformInducing (compactRestrictions (F:=F) K) := by
    rw [isUniformInducing_iff']
    refine ⟨hu,?_⟩
    apply ((Metric.uniformity_basis_dist.comap
      (Prod.map (compactRestrictions (F:=F) K) (compactRestrictions K))).le_basis_iff
      Metric.uniformity_basis_dist.compactConvergenceUniformity).mpr
    rintro ⟨S,ε⟩ ⟨hS,hε⟩
    obtain ⟨n,hn⟩ := hcover S hS
    refine ⟨min ε ((2:ℝ)⁻¹^n),lt_min hε (by positivity),?_⟩
    intro fg hfg x hx
    have hsmall : dist (compactRestrictions K fg.1) (compactRestrictions K fg.2) < (2:ℝ)⁻¹^n :=
      lt_of_lt_of_le hfg (min_le_right _ _)
    have hc := PiCountable.dist_le_dist_pi_of_dist_lt (i:=n) hsmall
    have he := ContinuousMap.dist_apply_le_dist
      (f:=compactRestrictions K fg.1 n) (g:=compactRestrictions K fg.2 n) ⟨x,hn hx⟩
    exact lt_of_le_of_lt (he.trans hc) (lt_of_lt_of_le hfg (min_le_left _ _))
  refine ⟨hind,?_⟩
  intro f g h
  ext x
  obtain ⟨n,hn⟩ := hcover {x} isCompact_singleton
  exact congrArg (fun z : ∀ n, C(K n,F) => z n ⟨x,hn (mem_singleton x)⟩) h

attribute [local instance] PiCountable.metricSpace

noncomputable abbrev compactSeriesMetric
    (hcover : ∀ S : Set A, IsCompact S → ∃ n, S ⊆ K n) : MetricSpace C(A,F) :=
  (compactRestrictions_embedding K hcover).comapMetricSpace (compactRestrictions K)

theorem compactSeriesMetric_formula
    (hcover : ∀ S : Set A, IsCompact S → ∃ n, S ⊆ K n) (f g : C(A,F)) :
    @dist _ (compactSeriesMetric (F:=F) K hcover).toDist f g =
      ∑' n, min ((2:ℝ)⁻¹^n) (dist (compactRestrictions K f n) (compactRestrictions K g n)) := rfl

theorem compactSeriesMetric_complete [CompactlyCoherentSpace A] [CompleteSpace F]
    (hcover : ∀ S : Set A, IsCompact S → ∃ n, S ⊆ K n) :
    @CompleteSpace C(A,F) (compactSeriesMetric (F:=F) K hcover).toUniformSpace := by
  change CompleteSpace C(A,F)
  infer_instance

#print axioms compactRestrictions_embedding
#print axioms compactSeriesMetric_complete
end CompactCover
end Asakura.EndToEnd

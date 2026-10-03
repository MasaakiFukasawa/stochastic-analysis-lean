import EndToEndCompactFunctionMetric
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

open Set Filter Metric
open scoped Topology
namespace Asakura.EndToEnd
set_option backward.isDefEq.respectTransparency false

variable {A F : Type*} [NormedAddCommGroup A] [ProperSpace A] [MetricSpace F]

def ballExhaustion : ℕ → Set A
  | 0 => ∅
  | n+1 => closedBall 0 (n+1 : ℝ)

private theorem ballExhaustion_compact (n : ℕ) : IsCompact (ballExhaustion (A:=A) n) := by
  cases n
  · exact isCompact_empty
  · exact isCompact_closedBall _ _

instance (n : ℕ) : CompactSpace (ballExhaustion (A:=A) n) :=
  isCompact_iff_compactSpace.mp (ballExhaustion_compact (A:=A) n)

theorem ballExhaustion_covers (S : Set A) (hS : IsCompact S) :
    ∃ n, S ⊆ ballExhaustion n := by
  obtain ⟨r,hr⟩ := (Metric.isBounded_iff_subset_closedBall (0:A)).mp hS.isBounded
  obtain ⟨n,hn⟩ := exists_nat_ge r
  refine ⟨n+1,hr.trans (closedBall_subset_closedBall ?_)⟩
  linarith

/-- The exact metric in the unnumbered Appendix B example, with the first
term indexed by 1. Its uniformity is compact convergence. -/
noncomputable abbrev continuousFSpaceMetric : MetricSpace C(A,F) :=
  compactSeriesMetric ballExhaustion ballExhaustion_covers

theorem continuousFSpaceMetric_formula (f g : C(A,F)) :
    @dist _ (continuousFSpaceMetric (A:=A) (F:=F)).toDist f g =
      ∑' n : ℕ, min ((2:ℝ)⁻¹^(n+1))
        (⨆ x : closedBall (0:A) (n+1:ℝ), dist (f x) (g x)) := by
  rw [compactSeriesMetric_formula]
  have hs := PiCountable.dist_summable
    (compactRestrictions ballExhaustion f) (compactRestrictions ballExhaustion g)
  have hs' : Summable (fun n : ℕ => min ((2:ℝ)⁻¹^n)
      (dist (compactRestrictions ballExhaustion f n) (compactRestrictions ballExhaustion g n))) := hs
  rw [hs'.tsum_eq_zero_add]
  have hz : dist (compactRestrictions ballExhaustion f 0) (compactRestrictions ballExhaustion g 0) = 0 := by
    apply dist_eq_zero.mpr
    ext x
    exact False.elim x.property
  rw [hz,min_eq_right (by positivity),zero_add]
  apply tsum_congr
  intro n
  rw [ContinuousMap.dist_eq_iSup]
  rfl

theorem compact_distance_maximum (f g : C(A,F)) (n : ℕ) :
    ∃ x : closedBall (0:A) (n+1:ℝ),
      (⨆ y : closedBall (0:A) (n+1:ℝ), dist (f y) (g y)) = dist (f x) (g x) := by
  have hne : (closedBall (0:A) (n+1:ℝ)).Nonempty :=
    ⟨0,mem_closedBall_self (by positivity)⟩
  obtain ⟨x,hx,hm⟩ := (isCompact_closedBall (0:A) (n+1:ℝ)).exists_isMaxOn hne
    (f.continuous.dist g.continuous).continuousOn
  letI : Nonempty (closedBall (0:A) (n+1:ℝ)) := ⟨⟨x,hx⟩⟩
  refine ⟨⟨x,hx⟩,?_⟩
  apply le_antisymm
  · apply ciSup_le
    intro y
    exact hm y.property
  · apply le_ciSup (f := fun y : closedBall (0:A) (n+1:ℝ) => dist (f y) (g y)) ?_ ⟨x,hx⟩
    exact ⟨dist (f x) (g x), fun z hz => by
      obtain ⟨y,rfl⟩ := hz
      exact hm y.property⟩

theorem continuousFSpaceMetric_complete [CompleteSpace F] :
    @CompleteSpace C(A,F) (continuousFSpaceMetric (A:=A) (F:=F)).toUniformSpace := by
  exact compactSeriesMetric_complete ballExhaustion ballExhaustion_covers

section Vector
variable [AddCommGroup F] [Module ℝ F] [ContinuousAdd F] [ContinuousSMul ℝ F]

theorem continuousFSpaceMetric_add :
    @ContinuousAdd C(A,F) (continuousFSpaceMetric (A:=A) (F:=F)).toUniformSpace.toTopologicalSpace _ := by
  change ContinuousAdd C(A,F)
  infer_instance

theorem continuousFSpaceMetric_smul :
    @ContinuousSMul ℝ C(A,F) _ _ (continuousFSpaceMetric (A:=A) (F:=F)).toUniformSpace.toTopologicalSpace := by
  change ContinuousSMul ℝ C(A,F)
  infer_instance

theorem continuousFSpaceMetric_translation
    (htrans : ∀ a b c : F, dist (a+c) (b+c) = dist a b) (f g h : C(A,F)) :
    @dist _ (continuousFSpaceMetric (A:=A) (F:=F)).toDist (f+h) (g+h) =
      @dist _ (continuousFSpaceMetric (A:=A) (F:=F)).toDist f g := by
  rw [continuousFSpaceMetric_formula,continuousFSpaceMetric_formula]
  apply tsum_congr
  intro n
  congr 1
  apply congrArg iSup
  funext x
  exact htrans (f x) (g x) (h x)

end Vector
#print axioms compact_distance_maximum
#print axioms continuousFSpaceMetric_formula
#print axioms continuousFSpaceMetric_complete
#print axioms continuousFSpaceMetric_add
#print axioms continuousFSpaceMetric_smul
#print axioms continuousFSpaceMetric_translation
end Asakura.EndToEnd

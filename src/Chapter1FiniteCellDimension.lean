import FullAuditPartitionExercise
import FullAuditProjectionRules
import Mathlib.LinearAlgebra.Dimension.Finrank

open MeasureTheory Set Filter Function
open scoped ENNReal BigOperators
namespace Asakura.Chapter1Complete
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- Positive-mass cells give exactly one independent L² coordinate each.
Both spanning and independence are proved in the a.e. quotient space. -/
theorem finite_cell_L2_dimension {Ω ι : Type*} [Fintype ι] {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (A : ι → Set Ω)
    (hA : ∀ i,MeasurableSet (A i)) (hd : Pairwise (Disjoint on A))
    (hcover : ∑ i,P (A i)=1) (hpos : ∀ i,0<P (A i)) :
    Module.finrank ℝ (lpMeas ℝ ℝ (⨆ i,MeasurableSpace.comap ((A i).indicator (fun _ => (1:ℝ))) inferInstance) 2 P)=Fintype.card ι := by
  classical
  let G := ⨆ i,MeasurableSpace.comap ((A i).indicator (fun _ => (1:ℝ))) inferInstance
  letI : MeasurableSpace Ω := m
  have hG : G≤m := iSup_le (fun i => (measurable_const.indicator (hA i)).comap_le)
  have hAG i : MeasurableSet[G] (A i) := by
    have hEq : G=MeasurableSpace.generateFrom (range A) := Asakura.FullAudit.indicator_generated_sigma A
    rw [hEq]
    exact MeasurableSpace.measurableSet_generateFrom (mem_range_self i)
  let e : ι → lpMeas ℝ ℝ G 2 P := fun i =>
    ⟨indicatorConstLp 2 (hA i) (measure_ne_top P _) (1:ℝ),
      mem_lpMeas_indicatorConstLp hG (hAG i) (measure_ne_top P _)⟩
  let L : (ι → ℝ) →ₗ[ℝ] lpMeas ℝ ℝ G 2 P := {
    toFun := fun a => ∑ i,a i • e i
    map_add' := by intro a b; simp [add_smul,Finset.sum_add_distrib]
    map_smul' := by intro c a; simp [Finset.smul_sum,mul_smul] }
  have he (a : ι → ℝ) : ((L a).val : Ω → ℝ) =ᵐ[P]
      fun w => ∑ i,(A i).indicator (fun _ => a i) w := by
    have hh := Lp.coeFn_fun_finsetSum Finset.univ (fun i => a i • (e i).val)
    have hi : ∀ i,((a i • (e i).val : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
        (A i).indicator (fun _ => a i) := by
      intro i
      filter_upwards [Lp.coeFn_smul (a i) (e i).val,indicatorConstLp_coeFn (p := 2)
        (hs := hA i) (hμs := measure_ne_top P _) (c := (1:ℝ))] with w hw hw'
      rw [hw]
      change a i * (e i).val w=_
      change (e i).val w=(A i).indicator (fun _ => (1:ℝ)) w at hw'
      rw [hw']
      by_cases hm : w∈A i <;> simp [hm]
    filter_upwards [hh,ae_all_iff.mpr hi] with w hw hw'
    have hv : (L a).val=(∑ i,a i • (e i).val : Lp ℝ 2 P) := by simp [L]
    rw [hv,hw]
    exact Finset.sum_congr rfl (fun i _ => hw' i)
  have hcell (a : ι → ℝ) (i : ι) :
      ∀ w∈A i,(∑ j,(A j).indicator (fun _ => a j) w)=a i := by
    intro w hw
    rw [Finset.sum_eq_single i]
    · simp [hw]
    · intro j _ hji
      have hj : w∉A j := fun hwj => Set.disjoint_left.mp (hd hji) hwj hw
      simp [hj]
    · simp
  have hinj : Injective L := by
    intro a b hab
    have hae : (fun w => ∑ i,(A i).indicator (fun _ => a i) w) =ᵐ[P]
        fun w => ∑ i,(A i).indicator (fun _ => b i) w := (he a).symm.trans (hab ▸ he b)
    funext i
    obtain ⟨w,hw,heq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (ne_of_gt (hpos i)) (ae_restrict_of_ae hae)
    dsimp only at heq
    rw [hcell a i w hw,hcell b i w hw] at heq
    exact heq
  have hsurj : Surjective L := by
    intro X
    let a := fun i => (P.real (A i))⁻¹ * ∫ w in A i,(X.val : Ω → ℝ) w ∂P
    refine ⟨a,Subtype.ext (Lp.ext ?_)⟩
    apply (he a).trans
    apply (Asakura.FullAudit.finite_cells_condExp P A hA hd hcover
      ((Lp.memLp X.val).integrable (by norm_num))).trans
    exact condExp_of_aestronglyMeasurable' hG (lpMeas.aestronglyMeasurable X)
      ((Lp.memLp X.val).integrable (by norm_num))
  have hdim := (LinearEquiv.ofBijective L ⟨hinj,hsurj⟩).finrank_eq
  simpa using hdim.symm

end Asakura.Chapter1Complete

import GaussianCopies
import ContinuousGluing

open MeasureTheory ProbabilityTheory Set
namespace Asakura
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

noncomputable def gluedProcess (W : (ℕ × UnitCube 1) → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  gluedPath (fun k u => W (k,u) ω) t

lemma glued_process_gaussian (W : (ℕ × UnitCube 1) → Ω → ℝ)
    (hG : IsGaussianProcess W P) (h0 : ∀ k ω, W (k,cubeZero) ω = 0) :
    IsGaussianProcess (gluedProcess W) P := by
  classical
  apply hG.of_isGaussianProcess
  intro t
  obtain ⟨N,hN⟩ := exists_nat_gt t
  let f : ℕ → ℕ × UnitCube 1 := fun k => (k,unitTimeCube k t)
  let I := (Finset.range N).image f
  refine ⟨I, ∑ i : I, ContinuousLinearMap.proj i, ?_⟩
  intro ω
  rw [show gluedProcess W t ω = ∑ k ∈ Finset.range N, W (k,unitTimeCube k t) ω from
    gluedPath_eq_sum _ (fun k => h0 k ω) N t hN.le]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.proj_apply, Finset.restrict_def]
  rw [Finset.sum_coe_sort I (fun p => W p ω)]
  change _ = ∑ i ∈ (Finset.range N).image f, W i ω
  rw [Finset.sum_image]
  intro a ha b hb he
  exact congrArg Prod.fst he

lemma glued_process_measurable (W : (ℕ × UnitCube 1) → Ω → ℝ)
    (hm : ∀ p, Measurable (W p)) (h0 : ∀ k ω, W (k,cubeZero) ω = 0) (t : ℝ) :
    Measurable (gluedProcess W t) := by
  obtain ⟨N,hN⟩ := exists_nat_gt t
  have he : gluedProcess W t = fun ω => ∑ k ∈ Finset.range N, W (k,unitTimeCube k t) ω := by
    funext ω
    exact gluedPath_eq_sum _ (fun k => h0 k ω) N t hN.le
  rw [he]
  fun_prop
end Asakura

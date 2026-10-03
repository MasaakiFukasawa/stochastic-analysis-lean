import Chapter5ScalarLiftCalculus
import Mathlib.Geometry.Manifold.PartitionOfUnity

open Set Filter Function
open scoped Topology
namespace Asakura.Chapter5
set_option maxHeartbeats 2400000

/-- A C² function defined on a neighborhood of a closed strip has a global
C² extension agreeing on a neighborhood of that strip. This removes the
extra global regularity imposed by the formal global Ito theorem. -/
theorem closed_set_contDiff_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S U : Set E) (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    (f : E → ℝ) (hf : ContDiffOn ℝ 2 f U) :
    ∃ g : E → ℝ,ContDiff ℝ 2 g ∧ ∀ x ∈ S,g =ᶠ[𝓝 x] f := by
  obtain ⟨V,hVo,hSV,hVU⟩ := normal_exists_closure_subset hS hU hSU
  obtain ⟨W,hWo,hVW,hWU⟩ := normal_exists_closure_subset isClosed_closure hU hVU
  obtain ⟨χ,hχ,_,hsupp,hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := (2:ℕ∞)) hWo isClosed_closure hVW
  let g := fun x => χ x*f x
  refine ⟨g,contDiff_iff_contDiffAt.mpr ?_,?_⟩
  · intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.mul ((hf x hx).contDiffAt (hU.mem_nhds hx))
    · have hxW : x ∉ closure W := fun hw => hx (hWU hw)
      have he : g =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxW] with y hy
        have hyW : y ∉ W := fun hyw => hy (subset_closure hyw)
        have hχ0 : χ y = 0 := notMem_support.mp (by rwa [hsupp])
        simp only [g,hχ0,zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · intro x hx
    filter_upwards [hVo.mem_nhds (hSV hx)] with y hy
    have hχ1 := (hone y).mp (subset_closure hy)
    simp only [g,hχ1,one_mul]

/-- Application to exactly the closed time strip occurring in the nonlinear
Feynman--Kac theorem. Values and first and second derivatives agree there. -/
theorem time_strip_C2_extension (R : ℝ) (U : Set (Fin 2 → ℝ)) (hU : IsOpen U)
    (hstrip : {x : Fin 2 → ℝ | x 0 ∈ Icc 0 R} ⊆ U)
    (v : (Fin 2 → ℝ) → ℝ) (hv : ContDiffOn ℝ 2 v U) :
    ∃ g : (Fin 2 → ℝ) → ℝ,ContDiff ℝ 2 g ∧
      ∀ x : Fin 2 → ℝ,x 0 ∈ Icc 0 R →
        g x = v x ∧ fderiv ℝ g x = fderiv ℝ v x ∧
          fderiv ℝ (fderiv ℝ g) x = fderiv ℝ (fderiv ℝ v) x := by
  obtain ⟨g,hg,he⟩ := closed_set_contDiff_extension
    {x : Fin 2 → ℝ | x 0 ∈ Icc 0 R} U
    (isClosed_Icc.preimage (continuous_apply 0)) hU hstrip v hv
  refine ⟨g,hg,?_⟩
  intro x hx
  have hh := he x hx
  exact ⟨hh.eq_of_nhds,hh.fderiv_eq,hh.fderiv.fderiv_eq⟩

end Asakura.Chapter5

import Chapter2FiniteDensityReal
import Chapter2WeightedPaths

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 1500000

/-- Convert the subtype Ico approximation to the real-time Ioc integrand
 used by the actual elementary Ito integral. -/
theorem finite_grid_projection_Ioc_ae (μ : Measure ℝ) [NullSingletonClass μ]
    (R : ℝ) (hR : 0≤R) (hμ : ∀ᵐ r ∂μ,r∈Icc 0 R)
    (N : ℕ) (u : ℕ → Icc (0:ℝ) R) (G : ℕ → ℝ) :
    (fun r => ∑ j∈Finset.range N,(Ico (u j) (u (j+1))).indicator (fun _ => G j) (projIcc 0 R hR r))=ᵐ[μ]
      fun r => ∑ j∈Finset.range N,(Ioc (u j).val (u (j+1)).val).indicator (fun _ => G j) r := by
  classical
  have he (j : Fin N) : (Ico (u j).val (u (j.val+1)).val).indicator (fun _ => G j)=ᵐ[μ]
      (Ioc (u j).val (u (j.val+1)).val).indicator (fun _ => G j) := by
    filter_upwards [Ico_ae_eq_Ioc (μ:=μ) (a:=(u j).val) (b:=(u (j.val+1)).val)] with r hr
    simp only [Set.indicator,hr]
  filter_upwards [hμ,ae_all_iff.mpr he] with r hr he
  rw [finite_grid_projection_identity 0 R hR N u G r hr]
  exact Finset.sum_congr rfl (fun j hj => he ⟨j,Finset.mem_range.mp hj⟩)

end Asakura.Chapter11

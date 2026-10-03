import Chapter8ProbabilityContinuous

open MeasureTheory Filter Set Finset Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false

/-- In finite dimension, the entrywise information limit is convergence
of the matrix itself in probability. -/
theorem probability_matrix_of_entries {Ω I ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (l : Filter I) (J : I → Ω → Matrix ι ι ℝ) (S : Matrix ι ι ℝ)
    (hJ : ∀ i j,TendstoInMeasure P (fun t ω => J t ω i j) l (fun _ => S i j)) :
    TendstoInMeasure P J l (fun _ => S) := by
  have hi (p : ι × ι) : TendstoInMeasure P
      (fun t ω => |J t ω p.1 p.2-S p.1 p.2|) l (fun _ => 0) := by
    have hh := probability_continuous_at_constant P l _ (S p.1 p.2) (hJ p.1 p.2)
      (fun x => |x-S p.1 p.2|) (by fun_prop)
    simpa only [sub_self,abs_zero] using hh
  have hs := probability_sum_filter P l (univ : Finset (ι × ι))
    (fun p t ω => |J t ω p.1 p.2-S p.1 p.2|) (fun _ _ => 0) (fun p _ => hi p)
  simp only [sum_const_zero] at hs
  apply tendstoInMeasure_iff_norm.mpr
  intro ε hε
  have hh := tendstoInMeasure_iff_dist.mp hs ε hε
  simp only [Real.dist_eq,sub_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => bot_le)
  intro t
  apply measure_mono
  intro ω hω
  have hn : ‖J t ω-S‖ ≤ ∑ p : ι × ι, |J t ω p.1 p.2-S p.1 p.2| := by
    apply (Matrix.norm_le_iff (sum_nonneg (fun _ _ => abs_nonneg _))).mpr
    intro i j
    simpa only [Matrix.sub_apply,Real.norm_eq_abs] using
      (single_le_sum (f := fun p : ι × ι => |J t ω p.1 p.2-S p.1 p.2|)
        (fun _ _ => abs_nonneg _) (mem_univ (i,j)))
  exact (hω.trans hn).trans (le_abs_self _)

end Asakura.Chapter8

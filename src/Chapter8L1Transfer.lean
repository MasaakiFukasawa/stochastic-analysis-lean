import Chapter8L1Approximation

open MeasureTheory Filter
open scoped Topology
namespace Asakura.Chapter8
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- Transfer L1 convergence along a coupling whose expected error vanishes. -/
theorem l1_limit_transfer {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (l : Filter I)
    (X Y : I → Ω → ℝ) (c : ℝ)
    (hY : ∀ i,Integrable (Y i) P) (hR : ∀ i,Integrable (fun w => X i w-Y i w) P)
    (hYlim : Tendsto (fun i => ∫ w,|Y i w-c| ∂P) l (nhds 0))
    (hRlim : Tendsto (fun i => ∫ w,|X i w-Y i w| ∂P) l (nhds 0)) :
    Tendsto (fun i => ∫ w,|X i w-c| ∂P) l (nhds 0) ∧
      TendstoInMeasure P X l (fun _ => c) := by
  have hX i : Integrable (X i) P := by
    convert (hR i).add (hY i) using 1
    funext w
    simp only [Pi.add_apply,sub_add_cancel]
  have hh : Tendsto (fun i => ∫ w,|X i w-c| ∂P) l (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun i => (∫ w,|X i w-Y i w| ∂P)+(∫ w,|Y i w-c| ∂P)) l (nhds 0) from by
        simpa only [add_zero] using hRlim.add hYlim)
      (fun i => integral_nonneg (fun w => abs_nonneg _))
    intro i
    have hb := integral_mono (((hX i).sub (integrable_const c)).abs)
      ((hR i).abs.add (((hY i).sub (integrable_const c)).abs)) (fun w => by
        change |X i w-c| ≤ |X i w-Y i w|+|Y i w-c|
        calc
          _ = |(X i w-Y i w)+(Y i w-c)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _)
    simp only [Pi.add_apply,Pi.sub_apply] at hb
    rw [integral_add (f := fun w => |X i w-Y i w|) (g := fun w => |Y i w-c|)
      (hR i).abs (((hY i).sub (integrable_const c)).abs)] at hb
    exact hb
  exact ⟨hh,probability_of_l1_limit P l X c (fun i => (hX i).sub (integrable_const c)) hh⟩

end Asakura.Chapter8

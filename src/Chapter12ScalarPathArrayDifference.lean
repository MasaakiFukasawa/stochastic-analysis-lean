import Chapter12LinearArrayBound
import Chapter12PathRemainderContinuity

open Set
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem scalar_path_array_difference {K E G I : Type*}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [Fintype I]
    (X Y : G → C(K,E)) (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    (ell : E →L[ℝ] ℝ) (k : ℕ) (z : G) (v : I → Fin k → G) (t : K) :
    Real.sqrt (∑i,‖iteratedFDeriv ℝ k (fun y => ell (X y t)) z (v i)-
      iteratedFDeriv ℝ k (fun y => ell (Y y t)) z (v i)‖^2)≤
    ‖ell‖*Real.sqrt (∑i,‖(iteratedFDeriv ℝ k X z (v i)) t-
      (iteratedFDeriv ℝ k Y z (v i)) t‖^2) := by
  let R : C(K,E) →L[ℝ] ℝ := ell.comp (ContinuousMap.evalCLM ℝ t)
  have hx i : iteratedFDeriv ℝ k (fun y => ell (X y t)) z (v i)=
      ell ((iteratedFDeriv ℝ k X z (v i)) t) :=
    congrArg (fun D => D (v i)) (R.iteratedFDeriv_comp_left hX.contDiffAt (by simp))
  have hy i : iteratedFDeriv ℝ k (fun y => ell (Y y t)) z (v i)=
      ell ((iteratedFDeriv ℝ k Y z (v i)) t) :=
    congrArg (fun D => D (v i)) (R.iteratedFDeriv_comp_left hY.contDiffAt (by simp))
  simp_rw [hx,hy,←map_sub]
  exact linear_array_bound ell _
end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_path_array_difference

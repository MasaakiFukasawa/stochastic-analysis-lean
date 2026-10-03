import Chapter12AdditiveSolutionStability
import Chapter12DominatedLpLimit

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The actual solution map transfers dominated uniform approximations of
the driving path to Lp convergence of the solution paths. -/
theorem additive_approximation_Lp {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsFiniteMeasure P]
    (b : E → E) (K : ℝ≥0) (hb : LipschitzWith K b) (T : ℝ) (hT : 0≤T)
    (S : E × C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (hcS : Continuous S)
    (hS : ∀ q t,S q t=q.1+(∫ s in 0..t.val,b (S q (projIcc 0 T hT s)))+q.2 t)
    (x : E) (X : Ω → C(Icc (0:ℝ) T,E)) (Q : ℕ → Ω → C(Icc (0:ℝ) T,E))
    (hQ : ∀ n,AEStronglyMeasurable (Q n) P)
    (hbound : ∀ n,∀ᵐ w ∂P,‖Q n w‖≤‖X w‖)
    (hlim : ∀ᵐ w ∂P,Tendsto (fun n => Q n w) atTop (𝓝 (X w)))
    (p : ℝ≥0∞) (hp : 1≤p) (hpt : p≠⊤) (hX : MemLp X p P) :
    Tendsto (fun n => eLpNorm (fun w => S (x,Q n w)-S (x,X w)) p P) atTop (𝓝 0) := by
  let C := Real.exp (((K:ℝ)+1)*T)
  have hC : 0<C := Real.exp_pos _
  have hqm (n : ℕ) : AEStronglyMeasurable (fun w => S (x,Q n w)-S (x,X w)) P :=
    (hcS.comp_aestronglyMeasurable (aestronglyMeasurable_const.prodMk (hQ n))).sub
      (hcS.comp_aestronglyMeasurable (aestronglyMeasurable_const.prodMk hX.aestronglyMeasurable))
  have hh := dominated_Lp_limit P p hp hpt
    (fun n w => S (x,Q n w)-S (x,X w)) 0 (fun w => (2*C) • X w)
    (hX.const_smul (2*C)) hqm (memLp_const (0 : C(Icc (0:ℝ) T,E)))
  simp only [sub_zero] at hh
  apply hh
  · intro n
    filter_upwards [hbound n] with w hw
    have hs := additive_solution_path_stability b K hb T hT S hS x (Q n w) (X w)
    have hd := (norm_sub_le (Q n w) (X w)).trans (add_le_add hw le_rfl)
    change ‖S (x,Q n w)-S (x,X w)‖≤‖(2*C) • X w‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (mul_pos (by norm_num) hC)]
    change ‖S (x,Q n w)-S (x,X w)‖≤C*‖Q n w-X w‖ at hs
    nlinarith
  · filter_upwards [hlim] with w hw
    have hs := (hcS.tendsto (x,X w)).comp (tendsto_const_nhds.prodMk_nhds hw)
    simpa using hs.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => S (x,X w)) atTop (𝓝 (S (x,X w))))

end Asakura.Chapter12

import Chapter4BrownianSystem
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Any finite list of samples on one common grid has the same law for
two constructed Brownian systems. The assertion is deduced from Levy's
joint increment characteristic function and the initial value zero. -/
theorem brownian_grid_samples_law
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι]
    (B B0 : BrownianSystem P 1) (h : ℝ) (hh : 0 ≤ h) (k : ι → ℕ) :
    IdentDistrib (fun w i => B.W 0 (realTimeClamp ((k i:ℝ)*h)) w)
      (fun w i => B0.W 0 (realTimeClamp ((k i:ℝ)*h)) w) P P := by
  classical
  let N := Finset.univ.sup k
  have hk i : k i ≤ N := Finset.le_sup (f := k) (Finset.mem_univ i)
  let f := fun z : Fin N → Fin 1 → ℝ => fun i => ∑ j : Fin (k i),z ⟨j.val,j.isLt.trans_le (hk i)⟩ 0
  have hfm : Measurable f := by
    apply measurable_pi_iff.mpr
    intro i
    exact Finset.measurable_sum _ (fun j _ => (measurable_pi_apply 0).comp (measurable_pi_apply _))
  obtain ⟨hm,hcl,_⟩ := B.grid_law h hh N
  obtain ⟨hm0,hcl0,_⟩ := B0.grid_law h hh N
  have hl : IdentDistrib (finiteNoiseGrid (fun j r => B.W j (realTimeClamp r)) h N)
      (finiteNoiseGrid (fun j r => B0.W j (realTimeClamp r)) h N) P P :=
    ⟨hm.aemeasurable,hm0.aemeasurable,Measure.ext_of_charFunDual (hcl.trans hcl0.symm)⟩
  have hf := hl.comp hfm
  have he (V : BrownianSystem P 1) :
      (fun w => f (finiteNoiseGrid (fun j r => V.W j (realTimeClamp r)) h N w)) =ᵐ[P]
        (fun w i => V.W 0 (realTimeClamp ((k i:ℝ)*h)) w) := by
    filter_upwards [(V.martingale 0).initial P V.F] with w hw
    funext i
    dsimp only [f,finiteNoiseGrid]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => V.W 0 (realTimeClamp (((j:ℝ)+1)*h)) w-V.W 0 (realTimeClamp ((j:ℝ)*h)) w)]
    have heq : (∑ j ∈ Finset.range (k i),
        (V.W 0 (realTimeClamp (((j:ℝ)+1)*h)) w-V.W 0 (realTimeClamp ((j:ℝ)*h)) w)) =
        V.W 0 (realTimeClamp ((k i:ℝ)*h)) w-V.W 0 (realTimeClamp ((0:ℝ)*h)) w := by
      simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_zero] using
        Finset.sum_range_sub (fun j : ℕ => V.W 0 (realTimeClamp ((j:ℝ)*h)) w) (k i)
    rw [heq]
    have hz : realTimeClamp (T := (⊤:EReal)) 0 = ⊥ := by
      apply Subtype.ext
      exact real_time_clamp_eq 0 le_rfl le_top
    simp only [zero_mul,hz,hw,Pi.zero_apply,sub_zero]
  exact (IdentDistrib.of_ae_eq hf.aemeasurable_fst (he B)).symm.trans
    (hf.trans (IdentDistrib.of_ae_eq hf.aemeasurable_snd (he B0)))

end Asakura.Chapter7

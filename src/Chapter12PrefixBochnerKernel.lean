import Chapter12AsianDerivativeKernel

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem integrated_prefix_L2_kernel (T : ℝ) (a : ℝ → ℝ) (ha : Measurable a)
    (hi : Integrable (fun t => a t • finiteTimeIntervalVector T 0 t) (volume.restrict (Ioc (0:ℝ) T))) :
    ((∫ t in Ioc (0:ℝ) T,a t • finiteTimeIntervalVector T 0 t :
      Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) : ℝ → ℝ) =ᵐ[
      (volume.restrict (Ioi (0:ℝ))).restrict (Iic T)] (fun s => ∫ t in s..T,a t) := by
  let ν := (volume.restrict (Ioi (0:ℝ))).restrict (Iic T)
  let K := fun z : ℝ × ℝ => a z.1 * (Ioc (0:ℝ) z.1).indicator (fun _ => (1:ℝ)) z.2
  have hKm : Measurable K := by
    have hs : MeasurableSet {z : ℝ × ℝ | 0 < z.2 ∧ z.2 ≤ z.1} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst)
    have he : K = fun z => a z.1 * ({z : ℝ × ℝ | 0 < z.2 ∧ z.2 ≤ z.1}.indicator (fun _ => (1:ℝ))) z := by
      funext z
      simp only [K,indicator_apply,mem_Ioc,mem_setOf_eq]
    rw [he]
    exact (ha.comp measurable_fst).mul (measurable_const.indicator hs)
  have hKe (t : ℝ) : ((a t • finiteTimeIntervalVector T 0 t : Lp ℝ 2 ν) : ℝ → ℝ) =ᵐ[ν] fun s => K (t,s) := by
    have hp : (finiteTimeIntervalVector T 0 t : ℝ → ℝ) =ᵐ[ν]
        (Ioc (0:ℝ) t).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
    filter_upwards [Lp.coeFn_smul (a t) (finiteTimeIntervalVector T 0 t),hp] with s h1 h2
    rw [h1,Pi.smul_apply,h2]
    rfl
  have hL (t) : MemLp (fun s => K (t,s)) 2 ν :=
    (Lp.memLp (a t • finiteTimeIntervalVector T 0 t)).ae_eq (hKe t)
  have hLe (t) : (hL t).toLp _ = a t • finiteTimeIntervalVector T 0 t :=
    Lp.ext ((hL t).coeFn_toLp.trans (hKe t).symm)
  have hLi : Integrable (fun t => (hL t).toLp _) (volume.restrict (Ioc (0:ℝ) T)) := by
    simpa only [hLe] using hi
  have he := l2_bochner_integral_pointwise (volume.restrict (Ioc (0:ℝ) T)) ν K hKm hL hLi
  simp only [hLe] at he
  have hpos : ∀ᵐ s ∂ν, 0 < s := ae_restrict_of_ae (ae_restrict_mem measurableSet_Ioi)
  have hle : ∀ᵐ s ∂ν, s ≤ T := ae_restrict_mem measurableSet_Iic
  filter_upwards [he,hpos,hle] with s h1 h2 h3
  rw [h1]
  exact integrated_prefix_kernel T s h2 h3 a

end Asakura.Chapter12

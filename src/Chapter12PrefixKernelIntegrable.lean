import Chapter12PrefixBochnerKernel

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem weighted_prefix_stronglyMeasurable (T : ℝ) (a : ℝ → ℝ) (ha : Measurable a) :
    StronglyMeasurable (fun t => a t • finiteTimeIntervalVector T 0 t) := by
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
  simpa only [hLe] using stronglyMeasurable_L2_sections ν K hKm hL

theorem weighted_prefix_integrable (T : ℝ) (a : ℝ → ℝ) (ha : Measurable a)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ∈ Ioc (0:ℝ) T, ‖a t‖ ≤ C) :
    Integrable (fun t => a t • finiteTimeIntervalVector T 0 t) (volume.restrict (Ioc (0:ℝ) T)) := by
  apply Integrable.of_bound (weighted_prefix_stronglyMeasurable T a ha).aestronglyMeasurable (C*Real.sqrt T)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_smul,finite_time_interval_norm T 0 t (le_refl 0) ht.1.le ht.2,sub_zero]
  exact mul_le_mul (hb t ht) (Real.sqrt_le_sqrt ht.2) (Real.sqrt_nonneg _) hC

theorem bounded_integrated_prefix_L2_kernel (T : ℝ) (a : ℝ → ℝ) (ha : Measurable a)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ∈ Ioc (0:ℝ) T, ‖a t‖ ≤ C) :
    ((∫ t in Ioc (0:ℝ) T,a t • finiteTimeIntervalVector T 0 t :
      Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) : ℝ → ℝ) =ᵐ[
      (volume.restrict (Ioi (0:ℝ))).restrict (Iic T)] (fun s => ∫ t in s..T,a t) :=
  integrated_prefix_L2_kernel T a ha (weighted_prefix_integrable T a ha C hC hb)

end Asakura.Chapter12

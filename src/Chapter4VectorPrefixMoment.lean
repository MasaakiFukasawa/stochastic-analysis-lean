import Chapter4VectorCoefficientEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
variable {dim : ℕ}
set_option backward.isDefEq.respectTransparency false

/-- Stop a path at a real time, clamped to its finite domain. -/
noncomputable def prefixPath {d : ℝ} (hd : 0 ≤ d)
    (Y : C(Icc (0:ℝ) d,Fin dim → ℝ)) (t : ℝ) : C(Icc (0:ℝ) d,Fin dim → ℝ) :=
  ⟨fun s => Y (min s (projIcc 0 d hd t)), by fun_prop⟩

theorem prefix_path_norm_le {d : ℝ} (hd : 0 ≤ d)
    (Y : C(Icc (0:ℝ) d,Fin dim → ℝ)) (t : ℝ) : ‖prefixPath hd Y t‖ ≤ ‖Y‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro s
  exact ContinuousMap.norm_coe_le_norm Y _

theorem prefix_path_time_continuous {d : ℝ} (hd : 0 ≤ d)
    (Y : C(Icc (0:ℝ) d,Fin dim → ℝ)) : Continuous (prefixPath hd Y) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : ℝ × Icc (0:ℝ) d => Y (min z.2 (projIcc 0 d hd z.1)))
  fun_prop

theorem prefix_path_measurable {Ω : Type*} [MeasurableSpace Ω]
    {d : ℝ} (hd : 0 ≤ d) (Y : Ω → C(Icc (0:ℝ) d,Fin dim → ℝ))
    (hY : Measurable Y) (t : ℝ) : Measurable (fun ω => prefixPath hd (Y ω) t) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro s
  exact (continuous_eval_const (min s (projIcc 0 d hd t))).measurable.comp hY

/-- The squared prefix L2 norm used as u(t) in the manuscript is continuous.
This justifies the continuity assumption in the factorial and Gronwall steps. -/
theorem prefix_square_moment_continuous {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d : ℝ} (hd : 0 ≤ d) (Y : Ω → C(Icc (0:ℝ) d,Fin dim → ℝ))
    (hY : Measurable Y) (hi : MemLp Y 2 P) :
    Continuous (fun t : ℝ => ∫ ω, ‖prefixPath hd (Y ω) t‖^2 ∂P) := by
  apply continuous_of_dominated (bound := fun ω => ‖Y ω‖^2)
  · intro t
    exact ((prefix_path_measurable hd Y hY t).norm.pow_const 2).aestronglyMeasurable
  · intro t
    exact .of_forall (fun ω => by
      simpa only [Real.norm_eq_abs,abs_sq] using
        pow_le_pow_left₀ (norm_nonneg _) (prefix_path_norm_le hd (Y ω) t) 2)
  · exact hi.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  · exact .of_forall (fun ω => (prefix_path_time_continuous hd (Y ω)).norm.pow 2)

/-- Point evaluation is bounded by the prefix supremum at that same time. -/
theorem evaluation_le_prefix_square {d : ℝ} (hd : 0 ≤ d)
    (Y : C(Icc (0:ℝ) d,Fin dim → ℝ)) (t : ℝ) :
    ‖Y (projIcc 0 d hd t)‖^2 ≤ ‖prefixPath hd Y t‖^2 := by
  have h := ContinuousMap.norm_coe_le_norm (prefixPath hd Y t) (projIcc 0 d hd t)
  change ‖Y (min (projIcc 0 d hd t) (projIcc 0 d hd t))‖ ≤ _ at h
  simp only [min_self] at h
  simpa only using pow_le_pow_left₀ (norm_nonneg _) h 2

/-- Fubini and point evaluation convert coefficient energy to the Volterra
right-hand side. No continuity or integrability of that right-hand side
is assumed: both follow from the L2 path hypothesis. -/
theorem time_energy_le_prefix_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℝ} (hd : 0 ≤ d)
    (Y : Ω → C(Icc (0:ℝ) d,Fin dim → ℝ)) (hm : Measurable Y) (hi : MemLp Y 2 P) :
    (∫ z : Ω × ℝ, ‖Y z.1 (projIcc 0 d hd z.2)‖^2
      ∂(P.prod (volume.restrict (Ioc (0:ℝ) d)))) ≤
    ∫ r in 0..d, (∫ ω, ‖prefixPath hd (Y ω) r‖^2 ∂P) := by
  let ν := volume.restrict (Ioc (0:ℝ) d)
  let x := fun z : Ω × ℝ => Y z.1 (projIcc 0 d hd z.2)
  have hx : Measurable x := clamped_path_evaluation_measurable d hd Y hm
  have hpoint (z : Ω × ℝ) : ‖x z‖^2 ≤ ‖Y z.1‖^2 := by
    have h := ContinuousMap.norm_coe_le_norm (Y z.1) (projIcc 0 d hd z.2)
    simpa only using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hNorm := hi.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hix : Integrable (fun z => ‖x z‖^2) (P.prod ν) := by
    apply (hNorm.comp_fst ν).mono' (hx.norm.pow_const 2).aestronglyMeasurable
    exact .of_forall (fun z => by simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_sq] using hpoint z)
  have hprefix r : Integrable (fun ω => ‖prefixPath hd (Y ω) r‖^2) P := by
    apply hNorm.mono' ((prefix_path_measurable hd Y hm r).norm.pow_const 2).aestronglyMeasurable
    exact .of_forall (fun ω => by
      simpa only [Real.norm_eq_abs,abs_sq] using
        pow_le_pow_left₀ (norm_nonneg _) (prefix_path_norm_le hd (Y ω) r) 2)
  have hxi r : Integrable (fun ω => ‖x (ω,r)‖^2) P := by
    apply hNorm.mono' ((hx.comp (measurable_id.prodMk measurable_const)).norm.pow_const 2).aestronglyMeasurable
    exact .of_forall (fun ω => by simpa only [Pi.pow_apply,Function.comp_apply,id_eq,Real.norm_eq_abs,abs_sq] using hpoint (ω,r))
  rw [integral_prod _ hix,integral_integral_swap hix,intervalIntegral.integral_of_le hd]
  apply integral_mono hix.integral_prod_right
    ((prefix_square_moment_continuous P hd Y hm hi).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  intro r
  exact integral_mono (hxi r) (hprefix r) (fun ω => evaluation_le_prefix_square hd (Y ω) r)

end Asakura.Chapter4.Vector

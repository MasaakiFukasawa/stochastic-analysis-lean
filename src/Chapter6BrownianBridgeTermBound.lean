import Chapter6BrownianWeightedRegression
import Chapter6BrownianBridgeNorm
import Chapter6ConditionalInnerBound

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators InnerProductSpace
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem brownian_bridge_grid_term_bound {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (h : ℝ) (hh : 0<h) (k : ℕ) (hk : k<n)
    (b : (Fin d → ℝ) → (Fin d → ℝ)) (hb : Measurable b) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ x,‖WithLp.toLp 2 (b x)‖≤K) :
    let U := fun w i => B.W i (realTimeClamp ((k:ℝ)*h)) w
    let V := fun w i => B.W i (realTimeClamp ((n:ℝ)*h)) w
    ∀ᵐ w ∂P,|P[(fun w => ∑ i,b (U w) i*(B.W i (realTimeClamp (((k:ℝ)+1)*h)) w-U w i))|MeasurableSpace.comap V inferInstance] w|
      ≤ h/((n:ℝ)*h-(k:ℝ)*h)*K*
        (((n:ℝ)*h-(k:ℝ)*h)/((n:ℝ)*h)*‖WithLp.toLp 2 (V w)‖+Real.sqrt ((d:ℝ)*((n:ℝ)*h-(k:ℝ)*h))) := by
  let U := fun w i => B.W i (realTimeClamp ((k:ℝ)*h)) w
  let V := fun w i => B.W i (realTimeClamp ((n:ℝ)*h)) w
  let c := h/((n:ℝ)*h-(k:ℝ)*h)
  let G := MeasurableSpace.comap V inferInstance
  letI : MeasurableSpace Ω := m
  have hc : 0≤c := div_nonneg hh.le (sub_nonneg.mpr (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk.le) hh.le))
  have hWa (i : Fin d) (a : ℕ) : Measurable (B.W i (realTimeClamp ((a:ℝ)*h))) :=
    ((B.martingale i).adapted P B.F _ (changed_time_finite _ (mul_nonneg (Nat.cast_nonneg a) hh.le))).mono (B.le _) le_rfl
  have hUm : Measurable U := measurable_pi_iff.mpr (fun i => hWa i k)
  let times : Bool × Fin d → ℕ := fun p => if p.1 then n else k
  have ht p : times p≤n := by dsimp [times]; split_ifs <;> omega
  obtain ⟨hg,_,_⟩ := brownian_grid_samples_gaussian P B h hh.le times ht (fun p => p.2)
  let L : ((Bool × Fin d) → ℝ) →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.pi (fun i => (ContinuousLinearMap.proj (true,i) : ((Bool × Fin d) → ℝ) →L[ℝ] ℝ)-(ContinuousLinearMap.proj (false,i) : ((Bool × Fin d) → ℝ) →L[ℝ] ℝ))
  have hdiff : HasGaussianLaw (fun w => V w-U w) P := hg.map L
  have hdiffe : HasGaussianLaw (fun w => WithLp.toLp 2 (V w-U w)) P :=
    hdiff.map_equiv (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hbm : AEStronglyMeasurable (fun w => WithLp.toLp 2 (b (U w))) P :=
    ((WithLp.measurable_toLp 2 _).comp (hb.comp hUm)).aestronglyMeasurable
  have hi := conditional_inner_bound P (fun w => WithLp.toLp 2 (b (U w)))
    (fun w => WithLp.toLp 2 (V w-U w)) hbm hdiffe.integrable K hK (ae_of_all _ (fun w => hbound _)) G
  have hn := brownian_bridge_grid_conditional_norm P B h hh k hk
  have hr := brownian_weighted_grid_regression P B h hh k hk b hb K hbound
  let f := fun w => ⟪WithLp.toLp 2 (b (U w)),WithLp.toLp 2 (V w-U w)⟫_ℝ
  have he : (fun w => ∑ i,b (U w) i*(c*(V w i-U w i)))=(fun w => c*f w) := by
    funext w
    simp only [f,PiLp.inner_apply,WithLp.ofLp_toLp,Pi.sub_apply,Real.inner_apply,mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have hsc := condExp_smul (μ := P) c f G
  filter_upwards [hi,hn,hr,hsc] with w hi hn hr hsc
  rw [he] at hr
  change P[(fun w => c*f w)|G] w=c*P[f|G] w at hsc
  rw [hr,hsc,abs_mul,abs_of_nonneg hc]
  exact (mul_le_mul_of_nonneg_left hi hc).trans (by nlinarith [mul_nonneg hc hK])

end Asakura.Chapter6

import Chapter4EulerLocalMoment
import Chapter4EulerCellCover
import Chapter4FiniteStepEnergy
import Chapter4CoefficientSplitMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- The coefficient error of the actual Euler interpolation is bounded by
the running solution error and the proved within-cell remainder. -/
theorem euler_coefficient_error_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hA : ∀ j,LocalCovarianceWitness P F (W j) (W j) (A j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → A j (realTimeClamp r) w=r)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (L : ℝ) (hL : 0≤L)
    (hμ : ∀ i x y,(μ i x-μ i y)^2≤L*‖x-y‖^2)
    (hσ : ∀ i j x y,(σ i j x-σ i j y)^2≤L*‖x-y‖^2)
    (ξ : Ω → Fin dim → ℝ) (hξa : Measurable[F ⊥] ξ) (hξ : MemLp ξ 2 P)
    (h : ℝ) (hh : 0≤h)
    (n : ℕ) (hnT : (((n:ℝ)*h : ℝ):EReal)<T)
    (K : ℝ) (hK : 0≤K)
    (hμg : ∀ i x,(μ i x)^2≤K*(1+‖x‖^2))
    (hσg : ∀ i j x,(σ i j x)^2≤K*(1+‖x‖^2))
    (V : Ω → C(Icc (0:ℝ) ((n:ℝ)*h),Fin dim → ℝ))
    (hVm : Measurable[m] V) (hVi : MemLp V 2 P)
    (hV : ∀ w r,V w r=eulerInterpolation μ σ (fun j r => W j (realTimeClamp r)) ξ h n r.val w)

    (X : Ω → C(Icc (0:ℝ) ((n:ℝ)*h),Fin dim → ℝ))
    (hXm : Measurable[m] X) (hXi : MemLp X 2 P)
    (b : (Fin dim → ℝ) → ℝ) (Lb : ℝ) (hLb : 0≤Lb)
    (hb : ∀ x y,(b x-b y)^2≤Lb*‖x-y‖^2)
    (t : ℝ) (ht : t∈Icc 0 ((n:ℝ)*h)) :
    let R := (n:ℝ)*h
    let hR : 0≤R := mul_nonneg (Nat.cast_nonneg n) hh
    let Y := eulerGrid μ σ (fun j r => W j (realTimeClamp r)) ξ h
    let U := fun z : Ω × ℝ => b (X z.1 (projIcc 0 R hR z.2))-
      ∑ k∈Finset.range n,(Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => b (Y k z.1)) z.2
    let B := (2*(dim:ℝ)*(R+(noise:ℝ)^2)*K)*(1+∫ w,‖V w‖^2 ∂P)*h
    MemLp U 2 (P.prod (volume.restrict (Ioc 0 t))) ∧
    (∫ z,U z^2 ∂P.prod (volume.restrict (Ioc 0 t)))≤
      ∫ r in 0..t,2*Lb*((∫ w,‖Vector.prefixPath hR (X w-V w) r‖^2 ∂P)+B) := by
  classical
  letI : MeasurableSpace Ω := m
  dsimp only
  let R := (n:ℝ)*h
  have hR : 0≤R := by dsimp only [R];positivity
  let Wr := fun j r => W j (realTimeClamp r)
  let Y := eulerGrid μ σ Wr ξ h
  let S := fun z : Ω × ℝ => ∑ k∈Finset.range n,
    (Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => b (Y k z.1)) z.2
  let U := fun z : Ω × ℝ => b (X z.1 (projIcc 0 R hR z.2))-S z
  let B := (2*(dim:ℝ)*(R+(noise:ℝ)^2)*K)*(1+∫ w,‖V w‖^2 ∂P)*h
  let q := fun r => ∫ w,‖Vector.prefixPath hR (X w-V w) r‖^2 ∂P
  have hbc := Vector.coordinate_continuous_of_square_lipschitz b Lb hLb hb
  have hY := euler_grid_adapted_memLp P hT F hF hle hnull W A hW hA hclock μ σ L hL hμ hσ ξ hξa hξ h hh
  have hkT k (hk : k∈Finset.range n) : (((k:ℝ)*h : ℝ):EReal)<T := by
    apply lt_of_le_of_lt _ hnT
    apply EReal.coe_le_coe
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hk).le) hh
  have hSa k (hk : k∈Finset.range n) : Measurable[F (realTimeClamp ((k:ℝ)*h))] (fun w => b (Y k w)) :=
    hbc.measurable.comp (hY k (hkT k hk)).1
  have hSi k (hk : k∈Finset.range n) : MemLp (fun w => b (Y k w)) 2 P :=
    square_lipschitz_coefficient_memLp P b Lb hLb hb (Y k) (hY k (hkT k hk)).2
  have hSd := finite_step_integrand_domain F hF hle (Finset.range n)
    (fun k => (k:ℝ)*h) (fun k => ((k:ℝ)+1)*h) (fun k w => b (Y k w)) hSa
  have hSR := finite_step_integrand_memLp P (Finset.range n)
    (fun k => (k:ℝ)*h) (fun k => ((k:ℝ)+1)*h) (fun k w => b (Y k w)) hSi R
  have hXR := (Vector.coefficient_path_memLp P R Lb hR hLb b (fun _ => 0) hbc continuous_const
    (by simpa only [sub_self,zero_pow (by decide : (2:ℕ)≠0),add_zero] using hb) X hXm hXi).1
  have hUi : MemLp U 2 (P.prod (volume.restrict (Ioc 0 t))) := (hXR.sub hSR).mono_measure
    (Measure.prod_mono le_rfl (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2)))
  have hUsq := (memLp_two_iff_integrable_sq hUi.aestronglyMeasurable).1 hUi
  have hq : Continuous q := Vector.prefix_square_moment_continuous P hR (fun w => X w-V w) (hXm.sub hVm) (hXi.sub hVi)
  have hpoint r (hr : r∈Ioc 0 t) : (∫ w,U (w,r)^2 ∂P)≤2*Lb*(q r+B) := by
    have hrR : r∈Icc 0 R := ⟨hr.1.le,hr.2.trans ht.2⟩
    obtain ⟨k,hk,hkr⟩ := uniform_grid_interval_cover h hh n r ⟨hr.1,hrR.2⟩
    have he : ∀ w,U (w,r)=b (X w ⟨r,hrR⟩)-b (Y k w) := by
      intro w
      dsimp only [U,S]
      rw [projIcc_of_mem hR hrR,uniform_grid_step_on_cell h hh n k (Finset.mem_range.mp hk) (fun l => b (Y l w)) r hkr]
    have hlocal := euler_interpolation_cell_moment P hT F hF hle hnull W A hW hA hclock
      μ σ L hL hμ hσ ξ hξa hξ h hh n hnT K hK hμg hσg V hVm hVi hV k (Finset.mem_range.mp hk) ⟨r,hrR⟩ ⟨hkr.1.le,hkr.2⟩
    simp_rw [he]
    exact coefficient_prefix_split_moment P R hR b Lb hLb hb X V hXm hVm hXi hVi
      (Y k) (hY k (hkT k hk)).2 ⟨r,hrR⟩ B hlocal.2
  change MemLp U 2 (P.prod (volume.restrict (Ioc 0 t))) ∧
    (∫ z,U z^2 ∂P.prod (volume.restrict (Ioc 0 t)))≤∫ r in 0..t,2*Lb*(q r+B)
  refine ⟨hUi,?_⟩
  rw [integral_prod _ hUsq,integral_integral_swap hUsq,intervalIntegral.integral_of_le ht.1]
  apply integral_mono_ae hUsq.integral_prod_right
    (((hq.add continuous_const).const_mul (2*Lb)).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact hpoint r hr

end Asakura.Chapter4

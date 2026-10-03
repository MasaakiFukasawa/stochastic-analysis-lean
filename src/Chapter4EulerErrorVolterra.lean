import Chapter4EulerCoefficientEnergy
import Chapter4ProgressiveVectorMoment
import Chapter4ContinuousStepDomain
import Chapter4VectorPathRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- The actual solution-minus-Euler equation gives the Volterra error
inequality; neither the local increment estimate nor Ito bounds are assumed. -/
theorem euler_actual_error_volterra
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

    (hXa : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => X w r))
    (NX : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hNX : ∀ i j,LocalMProcessWitness P F (NX i j))
    (hXI : ∀ i j,ItoCovarianceFormula P F (W j)
      (fun z => σ i j (X z.1 (finitePrefixTime (T:=T) ((n:ℝ)*h) (mul_nonneg (Nat.cast_nonneg n) hh) (realTimeClamp z.2)))) (NX i j))
    (hXe : ∀ᵐ w ∂P,∀ r i,X w r i=ξ w i+
      (∫ s in 0..r.val,μ i (X w (projIcc 0 ((n:ℝ)*h) (mul_nonneg (Nat.cast_nonneg n) hh) s)))+
      ∑ j,NX i j (realTimeClamp r.val) w)
    (t : ℝ) (ht : t∈Icc 0 ((n:ℝ)*h)) :
    let R := (n:ℝ)*h
    let hR : 0≤R := mul_nonneg (Nat.cast_nonneg n) hh
    let q := fun r => ∫ w,‖Vector.prefixPath hR (X w-V w) r‖^2 ∂P
    let B := (2*(dim:ℝ)*(R+(noise:ℝ)^2)*K)*(1+∫ w,‖V w‖^2 ∂P)*h
    q t≤((dim:ℝ)*(2*R+8*(noise:ℝ)^2))*(∫ r in 0..t,2*L*(q r+B)) := by
  classical
  letI : MeasurableSpace Ω := m
  let R := (n:ℝ)*h
  have hR : 0≤R := by dsimp only [R];positivity
  let Wr := fun j r => W j (realTimeClamp r)
  let Y := eulerGrid μ σ Wr ξ h
  let S := fun (b : (Fin dim → ℝ) → ℝ) (z : Ω × ℝ) => ∑ k∈Finset.range n,
    (Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => b (Y k z.1)) z.2
  let U := fun i (z : Ω × ℝ) => μ i (X z.1 (projIcc 0 R hR z.2))-S (μ i) z
  let H := fun i j a w => σ i j (X w (finitePrefixTime (T:=T) R hR a))
  let G := fun i j (z : Ω × ℝ) => H i j (realTimeClamp z.2) z.1-S (σ i j) z
  let G0 := fun i j (z : Ω × ℝ) => σ i j (X z.1 (projIcc 0 R hR z.2))-S (σ i j) z
  let q := fun r => ∫ w,‖Vector.prefixPath hR (X w-V w) r‖^2 ∂P
  let B := (2*(dim:ℝ)*(R+(noise:ℝ)^2)*K)*(1+∫ w,‖V w‖^2 ∂P)*h
  let E := ∫ r in 0..t,2*L*(q r+B)
  have htT : (t:EReal)<T := (EReal.coe_le_coe ht.2).trans_lt hnT
  have hY := euler_grid_adapted_memLp P hT F hF hle hnull W A hW hA hclock μ σ L hL hμ hσ ξ hξa hξ h hh
  have hkT k (hk : k∈Finset.range n) : (((k:ℝ)*h : ℝ):EReal)<T := by
    apply lt_of_le_of_lt _ hnT
    apply EReal.coe_le_coe
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hk).le) hh
  have hμc i := Vector.coordinate_continuous_of_square_lipschitz (μ i) L hL (hμ i)
  have hσc i j := Vector.coordinate_continuous_of_square_lipschitz (σ i j) L hL (hσ i j)
  have hμa i k (hk : k∈Finset.range n) := (hμc i).measurable.comp (hY k (hkT k hk)).1
  have hσa i j k (hk : k∈Finset.range n) := (hσc i j).measurable.comp (hY k (hkT k hk)).1
  have hSd i := finite_step_integrand_domain F hF hle (Finset.range n)
    (fun k => (k:ℝ)*h) (fun k => ((k:ℝ)+1)*h) (fun k w => μ i (Y k w)) (hμa i)
  have hXreg := Vector.finite_path_lift_regular F hF R hR hnT.le X hXa
  have hGd i j := continuous_minus_step_domain F hF hle (H i j)
    (fun a => (hσc i j).measurable.comp (hXreg.1 a))
    (fun w => (hσc i j).comp (hXreg.2 w)) (Finset.range n)
    (fun k => (k:ℝ)*h) (fun k => ((k:ℝ)+1)*h) (fun k w => σ i j (Y k w)) (hσa i j)
  have hUE i := euler_coefficient_error_energy P hT F hF hle hnull W A hW hA hclock μ σ L hL hμ hσ
    ξ hξa hξ h hh n hnT K hK hμg hσg V hVm hVi hV X hXm hXi (μ i) L hL (hμ i) t ht
  have hGE0 i j := euler_coefficient_error_energy P hT F hF hle hnull W A hW hA hclock μ σ L hL hμ hσ
    ξ hξa hξ h hh n hnT K hK hμg hσg V hVm hVi hV X hXm hXi (σ i j) L hL (hσ i j) t ht
  have htime : ∀ᵐ z : Ω × ℝ ∂P.prod (volume.restrict (Ioc 0 t)),z.2∈Ioc 0 t := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).mpr
    exact Filter.Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Ioc)
  have hGeq i j : G i j=ᵐ[P.prod (volume.restrict (Ioc 0 t))] G0 i j := by
    filter_upwards [htime] with z hz
    dsimp only [G,G0,H]
    rw [Vector.finite_path_lift_real R hR hnT.le X z.1 z.2 ⟨hz.1.le,hz.2.trans ht.2⟩]
  have hGe i j : MemLp (G i j) 2 (P.prod (volume.restrict (Ioc 0 t))) := (memLp_congr_ae (hGeq i j)).mpr (hGE0 i j).1
  have hGE i j : (∫ z,(G i j z)^2 ∂P.prod (volume.restrict (Ioc 0 t)))≤E := by
    rw [integral_congr_ae ((hGeq i j).mono (fun z hz => congrArg (fun x : ℝ => x^2) hz))]
    exact (hGE0 i j).2
  obtain ⟨NV,hNV2,hNV,hVI,hVe⟩ := euler_interpolation_ito_equation P hT F hF hle hnull W A hW hA hclock
    μ σ L hL hμ hσ ξ hξa hξ h hh n hnT
  let N := fun i j a w => NX i j a w-NV i j a w
  have hN i j : LocalMProcessWitness P F (N i j) := by
    simpa only [neg_one_mul,neg_add_eq_sub] using ((hNV i j).smul P F (-1)).add P F hF hle (hNX i j)
  have hNI i j : ItoCovarianceFormula P F (W j) (G i j) (N i j) := by
    simpa only [neg_one_mul,neg_add_eq_sub] using
      (hVI i j).add_smul P F hF hle (W j) (NV i j) (NX i j) _ _ (hXI i j) (-1)
  let D := fun w => Vector.restrictRealPath ht.2 (X w-V w)
  have hDm : Measurable D := Vector.restrict_real_path_measurable ht.2 _ (hXm.sub hVm)
  have hrep : ∀ᵐ w ∂P,∀ r i,D w r i=(∫ s in 0..r.val,U i (w,s))+∑ j,N i j (realTimeClamp r.val) w := by
    filter_upwards [hXe] with w hw
    intro r i
    have hx := hw ⟨r.val,r.property.1,r.property.2.trans ht.2⟩ i
    have hv := hVe w r.val r.property.1 i
    have hv' : V w ⟨r.val,r.property.1,r.property.2.trans ht.2⟩ i=ξ w i+
      (∫ s in 0..r.val,S (μ i) (w,s))+∑ j,NV i j (realTimeClamp r.val) w := by rw [hV];exact hv
    have huc : Continuous (fun s => μ i (X w (projIcc 0 R hR s))) := (hμc i).comp ((X w).continuous.comp continuous_projIcc)
    have hsi : IntervalIntegrable (fun s => S (μ i) (w,s)) volume 0 r.val := by
      have hh := IntervalIntegrable.sum (μ:=volume) (a:=0) (b:=r.val) (Finset.range n)
        (f := fun k s => (Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => μ i (Y k w)) s)
        (fun k _ => (intervalIntegrable_iff_integrableOn_Ioc_of_le r.property.1).mpr
          ((integrable_const _).indicator measurableSet_Ioc))
      convert hh using 1
      funext s
      simp only [S,Finset.sum_apply]
    have he : (∫ s in 0..r.val,U i (w,s))=(∫ s in 0..r.val,μ i (X w (projIcc 0 R hR s)))-(∫ s in 0..r.val,S (μ i) (w,s)) :=
      intervalIntegral.integral_sub (huc.intervalIntegrable _ _) hsi
    rw [he]
    change X w ⟨r.val,r.property.1,r.property.2.trans ht.2⟩ i-V w ⟨r.val,r.property.1,r.property.2.trans ht.2⟩ i=_
    rw [hx,hv']
    simp only [N,Finset.sum_sub_distrib]
    ring
  have hUm i : Measurable (U i) := ((hμc i).measurable.comp (Vector.clamped_path_evaluation_measurable R hR X hXm)).sub (hSd i).1
  obtain ⟨_,hbnd⟩ := progressive_vector_integral_second_moment P hT F hF hle hnull W A hW hA hclock N hN U G hUm
    (fun i j d hd _ => (hGd i j).1 d hd)
    (fun i j d hd _ => Filter.Eventually.of_forall (fun w => (hGd i j).2 w d hd))
    hNI t ht.1 htT (fun i => (hUE i).1) hGe E (fun i => (hUE i).2) hGE D hDm hrep
  have hE : 0≤E := intervalIntegral.integral_nonneg_of_forall ht.1 (fun r => by dsimp only [q,B];positivity)
  have hd : ∀ w,‖D w‖=‖Vector.prefixPath hR (X w-V w) t‖ :=
    fun w => Vector.restriction_eq_prefix_norm ht.1 ht.2 (X w-V w)
  simp_rw [hd] at hbnd
  apply hbnd.trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [ht.2]) (Nat.cast_nonneg dim)) hE

end Asakura.Chapter4

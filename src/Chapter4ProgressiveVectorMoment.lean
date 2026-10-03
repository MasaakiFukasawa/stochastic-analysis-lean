import Chapter4ProgressiveFiniteMoment
import Chapter4ClockRegularity
import Chapter4VectorDifferenceAssembly
import Chapter4DriftMomentBound

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- A finite-dimensional drift-plus-Ito process obeys the L2 maximal
estimate for progressive coefficients, including Euler step differences. -/
theorem progressive_vector_integral_second_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hA : ∀ j,LocalCovarianceWitness P F (W j) (W j) (A j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → A j (realTimeClamp r) w=r)
    (N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P F (N i j))
    (U : Fin dim → Ω × ℝ → ℝ) (G : Fin dim → Fin noise → Ω × ℝ → ℝ)
    (hUm : ∀ i,Measurable[m.prod inferInstance] (U i))
    (hGp : ∀ i j (R : ℝ),0≤R → (R:EReal)<T →
      @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) R => G i j (z.1,z.2.val)))
    (hGi : ∀ i j (R : ℝ),0≤R → (R:EReal)<T → ∀ᵐ w ∂P,
      Integrable (fun r => G i j (w,r)^2) (volume.restrict (Ioc 0 R)))
    (hNI : ∀ i j,ItoCovarianceFormula P F (W j) (G i j) (N i j))
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hUi : ∀ i,MemLp (U i) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hGe : ∀ i j,MemLp (G i j) 2 (P.prod (volume.restrict (Ioc 0 R))))
    (E : ℝ)
    (hUE : ∀ i,(∫ z,(U i z)^2 ∂P.prod (volume.restrict (Ioc 0 R)))≤E)
    (hGE : ∀ i j,(∫ z,(G i j z)^2 ∂P.prod (volume.restrict (Ioc 0 R)))≤E)
    (V : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (hVm : Measurable[m] V)
    (hrep : ∀ᵐ w ∂P,∀ r i,V w r i=(∫ s in 0..r.val,U i (w,s))+∑ j,N i j (realTimeClamp r.val) w) :
    MemLp V 2 P ∧
    (∫ w,‖V w‖^2 ∂P)≤((dim:ℝ)*(2*R+8*(noise:ℝ)^2))*E := by
  classical
  letI : MeasurableSpace Ω := m
  have hsq i j := (memLp_two_iff_integrable_sq (hGe i j).aestronglyMeasurable).1 (hGe i j)
  have hNi i j := by
    obtain ⟨hAm,hAc⟩ := clock_regular_from_identity (A j) (hclock j)
    have hei : Integrable (fun w => ∫ r in 0..R,(G i j (w,r))^2) P := by
      simp_rw [intervalIntegral.integral_of_le hR]
      exact (hsq i j).integral_prod_left
    exact brownian_progressive_ito_finite_path_moment P hT F hF hle hnull (W j) (A j) (N i j) (G i j)
      (hW j) (hA j) hAm hAc (hclock j) (hGp i j) (hGi i j) (hN i j) (hNI i j) R hR hRT hei
  choose hc hZi hZb using hNi
  let Z := fun i j => finiteRealPath (N i j) R (hc i j)
  have hZm i j : Measurable (Z i j) := finite_real_path_measurable F hle (N i j) R hRT _ (fun t ht => (hN i j).adapted P F t ht)
  have hZb' i j : (∫ w,‖Z i j w‖^2 ∂P)≤4*E := by
    have he : (∫ w,(∫ r in 0..R,(G i j (w,r))^2) ∂P)=∫ z,(G i j z)^2 ∂P.prod (volume.restrict (Ioc 0 R)) := by
      simp_rw [intervalIntegral.integral_of_le hR]
      exact (integral_prod _ (hsq i j)).symm
    have hb := hZb i j
    rw [he] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (hGE i j) (by norm_num))
  let D := fun i w => coordinateRealPath (V w) i-∑ j,Z i j w
  have hDm i : Measurable (D i) := (coordinate_path_measurable V hVm i).sub
    (Finset.measurable_sum _ (fun j _ => hZm i j))
  have hDr i : ∀ᵐ w ∂P,∀ r,D i w r=∫ s in 0..r.val,U i (w,s) := by
    filter_upwards [hrep] with w hw
    intro r
    have he := hw r i
    dsimp only [D]
    simp only [ContinuousMap.sub_apply,ContinuousMap.sum_apply,Z,finiteRealPath]
    change V w r i-∑ j,N i j (realTimeClamp r.val) w=_
    linarith only [he]
  have hD i := drift_path_moment_bound P R hR (U i) (hUm i) (hUi i) (D i) (hDm i).aestronglyMeasurable (hDr i)
  have hDb i : (∫ w,‖D i w‖^2 ∂P)≤R*E := by
    have hs := (memLp_two_iff_integrable_sq (hUi i).aestronglyMeasurable).1 (hUi i)
    have he : (∫ r in 0..R,(∫ w,(U i (w,r))^2 ∂P))=∫ z,(U i z)^2 ∂P.prod (volume.restrict (Ioc 0 R)) := by
      rw [intervalIntegral.integral_of_le hR,← integral_integral_swap hs]
      exact (integral_prod _ hs).symm
    have hb := (hD i).2
    rw [he] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (hUE i) hR)
  have he i : ∀ᵐ w ∂P,coordinateRealPath (V w) i=D i w+∑ j,Z i j w := by
    exact Filter.Eventually.of_forall (fun w => by dsimp only [D];abel)
  obtain ⟨hVi,hVb⟩ := Vector.coordinate_estimates_assemble P V hVm D Z (fun i => (hD i).1) hZi (R*E) (4*E) hDb hZb' he
  refine ⟨hVi,?_⟩
  convert hVb using 1 <;> ring

end Asakura.Chapter4

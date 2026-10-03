import Chapter5FrozenBrownianBSDE
import Chapter5FiniteSemimartingaleRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

/-- Assemble the constructed frozen solution into the actual analytic
data required by the weighted Ito a-priori estimate. -/
theorem frozen_finite_energy_data_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (W A : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ j,0<c j) (hcm : StrictMono c) (hcT : ∀ j,(c j:EReal)<T)
    (hct : StrictMono (fun j => realTimeClamp (T := T) (c j)))
    (hcut : ∀ j,realTimeClamp (T := T) (c j)<⊤)
    (hcc : ∀ t,t<⊤ → ∃ j,t<realTimeClamp (T := T) (c j))
    (hco : ∀ r,∃ j,r≤c j)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hFnat : F (realTimeClamp R)=Asakura.nullAugmentation (m := m) P (pastSigma W (realTimeClamp R)))
    (ξ : Ω → ℝ) (hξ : MemLp ξ 2 P) (hξm : Measurable[F (realTimeClamp R)] ξ)
    (f : Ω × ℝ → ℝ) (hfm : Measurable f)
    (hfp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => f (z.1,z.2.val)))
    (hfi : MemLp f 2 (P.prod (volume.restrict (Ioc 0 R)))) :
    ∃ u : BSDEFiniteEnergyData P F W c R,
      (u.Y (realTimeClamp R) =ᵐ[P] ξ) ∧
      (∀ w r,r∈Icc 0 R → u.B (w,r)= -f (w,r)) ∧
      (@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) R => u.Y (realTimeClamp z.2.val) z.1)) := by
  obtain ⟨Y₀,Z,M,hM,hMI,hY₀m,hZm,hY₀L,hZL,hY₀p,hZp,hY₀a,hY₀c,hY₀T,hBSDE,⟨a,hY₀eq⟩,hZG,hZpc⟩ :=
    frozen_brownian_bsde_constructed P hT F hF hle hnull W A hW hA hclock c hc hcm hcT hct hcut hcc hco
      R hR hRT hFnat ξ hξ hξm f hfm hfp hfi
  have hMl := continuous_m2_is_local P F hF hle (fun j => realTimeClamp (T := T) (c j))
    hct.monotone hcut hcc M hM
  obtain ⟨Y,V,hY,hYc,hYe,hVB⟩ := frozen_semimartingale_constructed P hT F hF hnull R hR hRT.le
    f hfm hfp hfi M hM hMl a
  have hfinite (r : ℝ) : realTimeClamp (T := T) r<⊤ := by
    obtain ⟨j,hj⟩ := hco r
    exact (real_time_clamp_mono hj).trans_lt (hcut j)
  have hYm := semimartingale_real_measurable P F hle Y V M hY hYc hfinite
  have he : ∀ᵐ w ∂P,∀ r∈Icc 0 R,Y (realTimeClamp r) w=Y₀ (w,r) := by
    rw [hY₀eq]
    exact hYe
  have heP := common_finite_process_product_congr P R _ Y₀ hYm hY₀m he
  have hYT : Y (realTimeClamp R) =ᵐ[P] ξ := by
    filter_upwards [he,hY₀T] with w hw htw
    exact (hw R ⟨hR,le_rfl⟩).trans htw
  let B := fun z : Ω × ℝ => -(Iic R).indicator (fun r => f (z.1,r)) z.2
  have hBm : Measurable B := (hfm.indicator (measurableSet_Iic.preimage measurable_snd)).neg
  have hBL : MemLp B 2 (P.prod (volume.restrict (Ioc 0 R))) :=
    (hfi.indicator (measurableSet_Iic.preimage measurable_snd)).neg
  have hBi : ∀ j,∀ᵐ w ∂P,IntervalIntegrable (fun r => B (w,r)) volume 0 (c j) := by
    intro j
    filter_upwards [(finite_time_L2_sections P R hR f hfm hfi).1] with w hw
    exact (clipped_driver_interval_integrable _ R _ hR (hc j).le (hw.integrable (by norm_num))).neg
  have hZi : ∀ j,∀ᵐ w ∂P,IntervalIntegrable (fun r => Z (w,r)^2) volume 0 (c j) := by
    intro j
    have hzj := hZG.mono_measure (Measure.prod_mono (le_refl P)
      (Measure.restrict_mono (show Ioc (0:ℝ) (c j) ⊆ Ioi 0 from fun _ hr => hr.1) (le_refl volume)))
    filter_upwards [(finite_time_L2_sections P (c j) (hc j).le Z hZm hzj).1] with w hw
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (hc j).le).mpr
      ((memLp_two_iff_integrable_sq hw.aestronglyMeasurable).mp hw)
  let u : BSDEFiniteEnergyData P F W c R := {
    Y := Y
    V := V
    M := M
    Z := Z
    B := B
    decomposition := hY
    measurableZ := hZm
    measurableB := hBm
    progressiveZ := hZpc
    squareZ := hZi
    integrableB := hBi
    drift := fun j => hVB.mono (fun w hw r hr => hw r hr.1 ((EReal.coe_le_coe hr.2).trans (hcT j).le))
    integral := hMI
    measurableY := hYm
    energyY := hY₀L.ae_eq heP.symm
    energyZ := hZL
    energyB := hBL
    terminal := hξ.ae_eq hYT.symm }
  refine ⟨u,hYT,?_,finite_semimartingale_progressive P F hF Y V M hY hYc R hR hRT⟩
  intro w r hr
  change -(Iic R).indicator (fun r => f (w,r)) r= -f (w,r)
  simp only [Set.indicator,hr.2,mem_Iic,ite_true]

end Asakura.Chapter5

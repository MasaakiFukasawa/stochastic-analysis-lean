import EndToEndM2Representative
import Chapter13LocalParameterFubini
import Chapter13StoppedIntegralIdentification
import Chapter13BoundedCoefficient

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter13
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Construct a jointly measurable fixed-time coordinate of a locally
bounded parameter family of actual Ito integrals. No joint measurability of
those integrals is an assumption. -/
theorem local_ito_joint_coordinate {Ω E : Type} {m : MeasurableSpace Ω} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d) (i : Fin d)
    (μ : Measure E) [IsFiniteMeasure μ]
    (H : E × (Ω × ℝ) → ℝ) (hm : Measurable H)
    (hp : ∀ b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z : E × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val))))
    (hb : ∀ w b,0≤b → ∃ K : ℝ,0≤K ∧ ∀ x r,r∈Icc 0 b → |H (x,(w,r))|≤K)
    (N : E → HalfClosedTime → Ω → ℝ) (hN : ∀ x,LocalMProcessWitness P B.F (N x))
    (hNI : ∀ x,ItoCovarianceFormula P B.F (B.W i) (fun z => H (x,z)) (N x))
    (r : ℝ) (hr : 0≤r) :
    ∃ G : E × Ω → ℝ, Measurable G ∧ ∀ᵐ x ∂μ, ∀ᵐ w ∂P, G (x,w)=N x (realTimeClamp r) w := by
  classical
  let R := r+1
  have hR : 0<R := by dsimp [R];linarith
  have hrR : realTimeClamp (T:=(⊤:EReal)) r ≤ realTimeClamp R :=
    real_time_clamp_mono (by dsimp [R];linarith)
  have hrt : realTimeClamp (T:=(⊤:EReal)) r<⊤ := real_time_below r hr (EReal.coe_lt_top r)
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion (by simp : (0:EReal)<⊤)
  have hMloc (Y : HalfClosedTime → Ω → ℝ) (hY : ContinuousM2Witness P B.F Y) :
      LocalMProcessWitness P B.F Y :=
    continuous_m2_is_local P B.F B.mono B.le (fun n => realTimeClamp (c n)) hct.monotone hcut hcc Y hY
  obtain ⟨τ,hτ,htop,hfib⟩ := local_parameter_fubini P B i μ R hR H hm hp (fun w => hb w R hR.le)
  have hv n := m2_joint_representative_ae P B.F B.le B.null μ
    (hfib n).choose (hfib n).choose_spec.1.aestronglyMeasurable
  choose V hVm hVa hVe using hv
  have he n : ∀ᵐ x ∂μ, ∀ᵐ w ∂P,
      V n x (realTimeClamp r) w = N x (min (min (realTimeClamp R) (τ n w)) (realTimeClamp r)) w := by
    filter_upwards [(hfib n).choose_spec.2.1,hVe n] with x hx hvx
    obtain ⟨Y,hY,hYI,hYZ⟩ := hx
    obtain ⟨hV,hVZ⟩ := hvx
    have hterm : Y ⊤=ᵐ[P] V n x ⊤ := by
      have heq := congrArg (fun v : continuousM2Terminal P B.F => (v : Lp ℝ 2 P)) (hYZ.symm.trans hVZ.symm)
      have hraw : (((hY.moment ⊤).toLp (Y ⊤)) : Ω → ℝ) =ᵐ[P]
          (((hV.moment ⊤).toLp (V n x ⊤)) : Ω → ℝ) :=
        Filter.Eventually.of_forall (congrFun (congrArg (fun v : Lp ℝ 2 P => (v : Ω → ℝ)) heq))
      exact (hY.moment ⊤).coeFn_toLp.symm.trans (hraw.trans (hV.moment ⊤).coeFn_toLp)
    have hYV := continuous_m2_terminal_injective P B.F B.mono B.le Y (V n x) hY hV hterm
    have hHi b (hb0 : 0≤b) : ∀ᵐ w ∂P, IntervalIntegrable (fun s => H (x,(w,s))^2) volume 0 b := by
      apply ae_of_all
      intro w
      exact bounded_coefficient_square (fun z => H (x,z)) (hm.comp measurable_prodMk_left)
        (fun w b hb0 => by
          obtain ⟨K,hK,hbound⟩ := hb w b hb0
          exact ⟨K,hK,fun s hs => hbound x s hs⟩) w b hb0
    have hs := stopped_integral_identified P B i (fun z => H (x,z))
      (fun b hb0 => (hp b hb0).comp measurable_prodMk_left) hHi
      (N x) (hN x) (hNI x) R hR.le (τ n) (hτ n) Y (hMloc Y hY) hYI
    filter_upwards [hYV,hs] with w hw hs
    exact (hw (realTimeClamp r)).symm.trans (hs _ hrt)
  let G := fun z : E × Ω => limUnder atTop (fun n => V n z.1 (realTimeClamp r) z.2)
  have hG : Measurable G := (StronglyMeasurable.limUnder (fun n =>
    ((hVm n).comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))).stronglyMeasurable)).measurable
  refine ⟨G,hG,?_⟩
  filter_upwards [ae_all_iff.mpr he] with x hx
  filter_upwards [ae_all_iff.mpr hx] with w hw
  obtain ⟨k,hk⟩ := htop w
  have hevent : (fun n => V n x (realTimeClamp r) w) =ᶠ[atTop] (fun _ => N x (realTimeClamp r) w) := by
    filter_upwards [eventually_ge_atTop k] with n hn
    rw [hw n,hk n hn,min_top_right,min_eq_right hrR]
  exact (tendsto_const_nhds.congr' hevent.symm).limUnder_eq

#print axioms local_ito_joint_coordinate
end Asakura.EndToEnd

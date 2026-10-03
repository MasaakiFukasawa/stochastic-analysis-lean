import Chapter7FutureProcessRegularity
import Chapter7BrownianQuadraticIto
import Chapter7GridMartingaleConstruction
import Chapter4ShiftedBrownianIto
import Chapter2ItoStoppedInterval

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- One cell: construct its Ito integrals and identify their sum with the
centered quadratic Brownian increment by the product formula. -/
theorem brownian_cell_terminal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (K : Fin d → Fin d → ℝ) (hK : ∀ i j,K i j=K j i)
    (s e R : ℝ) (hs : 0≤s) (hse : s≤e) (heR : e≤R) :
    ∃ Z : Fin d → HalfClosedTime → Ω → ℝ,
      (∀ i,LocalMProcessWitness P B.F (Z i)) ∧
      (∀ i,ItoCovarianceFormula P B.F (B.W i) (brownianCellIntegrand B (K i) s e) (Z i)) ∧
      (∀ i r,0≤r → r≤s → Z i (realTimeClamp r) =ᵐ[P] 0) ∧
      (∀ᵐ w ∂P,2*(∑ i,Z i (realTimeClamp R) w)=
        (∑ i,∑ j,K i j*(B.W i (realTimeClamp e) w-B.W i (realTimeClamp s) w)*
          (B.W j (realTimeClamp e) w-B.W j (realTimeClamp s) w))-(e-s)*(∑ i,K i i)) := by
  have hT : (0:EReal)<⊤ := by simp
  let H := fun i => futureBrownianProjection B (K i) s
  have hr i := future_brownian_process_regular P B (K i) s hs
  have hreg i := open_process_real_regularity B.F (H i) (hr i).1 (hr i).2
  have hyex i := continuous_adapted_ito_exists P hT B.F B.mono B.le B.null (B.W i) (B.martingale i)
    (fun z => H i (realTimeClamp z.2) z.1) (hreg i).1 (hreg i).2
  choose Y hY hYi using hyex
  have hcell i := brownian_cell_integrand_regular P B (K i) s e hs
  obtain ⟨Z,hZ,hZi⟩ := locally_square_integrable_vector_integrals P B
    (fun i => brownianCellIntegrand B (K i) s e) (fun i => (hcell i).1)
    (fun i b hb => (hcell i).2.1 b hb.le) (fun i b hb => ae_of_all P (fun w => (hcell i).2.2 b hb.le w))
  have hstop (a : ℝ) t : MeasurableSet[B.F t] {w : Ω | realTimeClamp a≤t} := by
    by_cases h : realTimeClamp a≤t <;> simp [h]
  have hZic i : ItoCovarianceFormula P B.F (B.W i)
      (fun z => (Ioc s e).indicator (fun r => H i (realTimeClamp r) z.1) z.2) (Z i) := by
    apply (hZi i).congr_on_time_domain P B.F (B.W i) (Z i)
    intro w r hr _
    by_cases hm : r∈Ioc s e
    · simp only [brownianCellIntegrand,indicator_of_mem hm,H,future_brownian_process_real B (K i) s r hr]
    · simp only [brownianCellIntegrand,indicator_of_notMem hm]
  have hstopZ i := ito_stochastic_interval_identity P hT B.F B.mono B.le B.null
    (B.W i) (Y i) (Z i) (fun z => H i (realTimeClamp z.2) z.1)
    (B.martingale i) (hY i) (hZ i) (fun w => (half_line_integral_continuous _ ((hr i).2 w)).measurable)
    (fun _ => s) (fun _ => e) (fun _ => hs) (fun _ => hs.trans hse) (fun _ => hse)
    (hstop s) (hstop e) (hYi i) (hZic i)
  let Bs := B.shift s hs
  let Ys := fun i t w => Y i (deterministicTimeShift s hs t) w-Y i (deterministicTimeShift s hs ⊥) w
  have hYs i : LocalMProcessWitness P Bs.F (Ys i) :=
    local_martingale_shifted_future P B.F B.mono B.le (Y i) (hY i) s hs
  have hYsi i : ItoCovarianceFormula P Bs.F (Bs.W i)
      (fun z => ∑ j,K i j*Bs.W j (realTimeClamp z.2) z.1) (Ys i) := by
    have hi := brownian_ito_shifted_future P B.F B.mono B.le B.null
      (B.W i) (Y i) (B.C i i) (H i) (B.martingale i) (hY i) (B.cov i i)
      (B.diagonal_clock i) (hr i).1 (hr i).2 (hYi i) s hs
    apply hi.congr_on_time_domain P Bs.F (Bs.W i) (Ys i)
    intro w r hr _
    have hsr := real_time_clamp_mono (T := ⊤) (le_add_of_nonneg_right hr : s≤s+r)
    simp only [H,futureBrownianProjection,deterministic_shift_real s hs r hr,
      min_eq_left hsr,Bs,BrownianSystem.shift,deterministic_shift_bot s hs]
  obtain ⟨J,hJ,hJi,hquad⟩ := brownian_quadratic_ito P Bs K hK
  have hsame i := ItoCovarianceFormula.unique P hT Bs.F Bs.mono Bs.le Bs.null (Bs.W i) (Ys i) (J i) _
    (Bs.martingale i) (hYs i) (hJ i) (hYsi i) (hJi i)
  have hall : ∀ᵐ w ∂P,∀ i,∀ t,t<⊤ → Z i t w=Y i (min (realTimeClamp e) t) w-Y i (min (realTimeClamp s) t) w :=
    ae_all_iff.mpr hstopZ
  have heq : ∀ᵐ w ∂P,∀ i,∀ t,t<⊤ → Ys i t w=J i t w := ae_all_iff.mpr hsame
  refine ⟨Z,hZ,hZi,?_,?_⟩
  · intro i r hr hrs
    filter_upwards [hall] with w hw
    have hsmin := real_time_clamp_mono (T := ⊤) hrs
    have hemin := real_time_clamp_mono (T := ⊤) (hrs.trans hse)
    simpa only [min_eq_right hsmin,min_eq_right hemin,sub_self,Pi.zero_apply] using
      hw i (realTimeClamp r) (real_time_below r hr (EReal.coe_lt_top _))
  filter_upwards [hall,heq,hquad] with w hz heq hq
  have hlen : 0≤e-s := sub_nonneg.mpr hse
  have hew i : Z i (realTimeClamp R) w=J i (realTimeClamp (e-s)) w := by
    rw [hz i _ (real_time_below R (hs.trans (hse.trans heR)) (EReal.coe_lt_top _)),
      min_eq_left (real_time_clamp_mono heR),min_eq_left (real_time_clamp_mono (hse.trans heR))]
    have he' := heq i (realTimeClamp (e-s)) (real_time_below _ hlen (EReal.coe_lt_top _))
    simpa only [Ys,deterministic_shift_real s hs (e-s) hlen,deterministic_shift_bot s hs,add_sub_cancel] using he'
  rw [show (∑ i,Z i (realTimeClamp R) w)=(∑ i,J i (realTimeClamp (e-s)) w) from sum_congr rfl (fun i _ => hew i)]
  have hq' := (hq (e-s) hlen).symm
  simpa only [Bs,BrownianSystem.shift,deterministic_shift_real s hs (e-s) hlen,deterministic_shift_bot s hs,add_sub_cancel] using hq'

end Asakura.Chapter7

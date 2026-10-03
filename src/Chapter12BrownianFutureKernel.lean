import Chapter12WienerFutureConditional

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

/-- From the original Brownian motion construct a single Wiener map and,
for every integrable cylinder, a progressive conditional expectation by
integrating an independent copy of the future Gaussian variables. -/
theorem brownian_future_kernel_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (T : ℝ) (hT : 0≤T)
    (hnat : ∀ a : Icc (0:ℝ) T,B.F (realTimeClamp a.val)=
      Asakura.nullAugmentation (m := m) P
        (MeasurableSpace.comap (fun w (z : {z : BrownianTimeCoordinates d T // z.2.val≤a.val}) =>
          brownianTimeCoordinate P B T z.val w) inferInstance)) :
    ∃ W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P,
      (∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P) ∧
      (∀ h,AEStronglyMeasurable[B.F (realTimeClamp T)] (W h : Ω → ℝ) P) ∧
      (∀ z,brownianTimeCoordinate P B T z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ)) ∧
      ∀ n (u : Fin n → FiniteWienerHilbert d T) (f : (Fin n → ℝ) → ℝ),Measurable f →
        Integrable (fun w => f (fun i => W (u i) w)) P →
        ∃ N : Fin n → HalfClosedTime → Ω → ℝ,
          (∀ i,ContinuousM2Witness P B.F (N i)) ∧
          @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val))) inferInstance
            (fun z : Ω × Icc (0:ℝ) T => ∫ v,
              f ((fun i => N i (realTimeClamp z.2.val) z.1)+
                (fun i => N i ⊤ v-N i (realTimeClamp z.2.val) v)) ∂P) ∧
          (∀ t : Icc (0:ℝ) T,
            P[(fun w => f (fun i => W (u i) w))|B.F (realTimeClamp t.val)]=ᵐ[P]
              fun w => ∫ v,f ((fun i => N i (realTimeClamp t.val) w)+
                (fun i => N i ⊤ v-N i (realTimeClamp t.val) v)) ∂P) := by
  obtain ⟨W,hW,hmeas,hinc,hfuture⟩ := finite_horizon_wiener_with_future_process P B T hT
  have hcoord z : brownianTimeCoordinate P B T z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ) := by
    have hzero : realTimeClamp (T:=(⊤:EReal)) 0=⊥ :=
      Subtype.ext (real_time_clamp_eq 0 le_rfl le_top)
    have h := hinc z.1 0 z.2.val le_rfl z.2.property.1 z.2.property.2
    rw [hzero] at h
    filter_upwards [h,(B.martingale z.1).initial P B.F] with w hw h0
    change B.W z.1 (realTimeClamp z.2.val) w=_
    dsimp only [brownianTimeDirection]
    rw [hw,h0]
    simp
  refine ⟨W,hW,hmeas,hcoord,?_⟩
  intro n u f hf hi
  have hpair : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => f (z.1+z.2)) :=
    hf.comp (measurable_fst.add measurable_snd)
  obtain ⟨N,hN,hterm,hfut,hprog,havg⟩ :=
    wiener_future_average_constructed P B T W hfuture n u _ hpair
  refine ⟨N,hN,hprog,?_⟩
  intro t
  have hcond := wiener_future_conditional_expectation P B T t.val W hW
    (brownianTimeCoordinate P B T)
    (fun z => (brownian_time_coordinate_measurable P B T z).mono (B.le _) le_rfl)
    hcoord (hnat t) n u N hN hterm (hfut t.val t.property.1) f hf hi
  apply hcond.trans
  exact ae_of_all _ (fun w => (havg t w).symm)

end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_future_kernel_constructed

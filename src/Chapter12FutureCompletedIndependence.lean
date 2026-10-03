import Chapter12FiniteFutureIndependence
import Extended

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem independent_null_augmentation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H G : MeasurableSpace Ω)
    (hH : H≤m) (hG : G≤m) (hind : Indep H G P) :
    Indep H (Asakura.nullAugmentation (m := m) P G) P := by
  apply (indep_iff_forall_indepSet P).mpr
  intro A B hA hB
  obtain ⟨hBm,C,hC,hBC⟩ := hB
  apply (indepSet_iff_measure_inter_eq_mul (hH A hA) hBm P).mpr
  have he : A∩B=ᵐ[P] A∩C := by
    filter_upwards [hBC] with w hw
    simp only [mem_inter_iff,hw]
  rw [measure_congr he,measure_congr hBC]
  exact (indepSet_iff_measure_inter_eq_mul (hH A hA) (hG C hC) P).mp
    (hind.indepSet_of_measurableSet hA hC)

/-- The actual future Wiener vector is independent also of the completed
natural past used by the manuscript. -/
theorem finite_future_independent_completed_past {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T a : ℝ)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : BrownianTimeCoordinates d T → Ω → ℝ) (hm : ∀ z,Measurable (X z))
    (he : ∀ z,X z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (n : ℕ) (u : Fin n → FiniteWienerHilbert d T) :
    Indep (MeasurableSpace.comap (fun w i => W (finiteFuturePart T a (u i)) w) inferInstance)
      (Asakura.nullAugmentation (m := m) P
        (MeasurableSpace.comap (fun w (z : {z : BrownianTimeCoordinates d T // z.2.val≤a}) => X z.val w) inferInstance)) P := by
  apply independent_null_augmentation P
  · exact (measurable_pi_iff.mpr (fun i => (Lp.stronglyMeasurable _).measurable)).comap_le
  · exact (measurable_pi_iff.mpr (fun z : {z : BrownianTimeCoordinates d T // z.2.val≤a} => hm z.val)).comap_le
  · exact finite_future_independent_past P T a W hlaw X hm he n u

end Asakura.Chapter12
#print axioms Asakura.Chapter12.finite_future_independent_completed_past

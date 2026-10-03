import Chapter10GaussianHistory
import Chapter9InformationCompletion

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter10
open Asakura.Chapter9
set_option backward.isDefEq.respectTransparency false

/-- Adjoining the ambient null events preserves independence from the error. -/
theorem independent_completed_history {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H G : MeasurableSpace Ω)
    (hH : H≤m) (hG : G≤m) (hind : Indep H G P) :
    Indep H (nullAugmentedInformation (m := m) P G) P := by
  apply (indep_iff_forall_indepSet P).mpr
  intro A B hA hB
  obtain ⟨C,hC,hBC⟩ := null_augmented_event (m := m) P G B hB
  apply (indepSet_iff_measure_inter_eq_mul (hH A hA)
    (null_augmented_le (m := m) P G hG B hB) P).mpr
  have he : A∩B =ᵐ[P] A∩C := by
    filter_upwards [hBC] with w hw
    simp only [mem_inter_iff,hw]
  rw [measure_congr he, measure_congr hBC]
  exact (indepSet_iff_measure_inter_eq_mul (hH A hA) (hG C hC) P).mp
    (hind.indepSet_of_measurableSet hA hC)

end Asakura.Chapter10

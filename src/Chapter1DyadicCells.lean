import Chapter1DyadicDigits
import Chapter1FiniteCellDimension
import FullAuditDiceExercise
import Mathlib.MeasureTheory.Function.Floor

open MeasureTheory Set Function
open scoped ENNReal BigOperators
namespace Asakura.Chapter1Complete
set_option maxHeartbeats 3000000

noncomputable def unitIntervalLaw : Measure ℝ := volume.restrict (Ioc 0 1)
instance : IsProbabilityMeasure unitIntervalLaw := by
  constructor
  simp [unitIntervalLaw]

lemma unitIntervalLaw_eq : unitIntervalLaw=volume.restrict (Ico 0 1) :=
  restrict_Ico_eq_restrict_Ioc.symm

lemma measurable_dyadicCode (n : ℕ) : Measurable (dyadicCode n) := by
  unfold dyadicCode dyadicFloor
  exact ((measurable_const.mul measurable_id).floor).sub
    (measurable_const.mul measurable_id.floor)

def dyadicCell (n : ℕ) (k : Fin (2^n)) : Set ℝ := {x | dyadicCode n x=(k.val:ℤ)}

lemma measurable_dyadicCell (n : ℕ) (k : Fin (2^n)) : MeasurableSet (dyadicCell n k) :=
  (measurable_dyadicCode n) (measurableSet_singleton _)

lemma dyadic_cell_inter (n : ℕ) (k : Fin (2^n)) :
    dyadicCell n k ∩ Ico 0 1=Ico ((k:ℝ)/(2:ℝ)^n) (((k:ℝ)+1)/(2:ℝ)^n) := by
  have hp : (0:ℝ)<2^n := by positivity
  have hk : (k:ℝ)+1≤(2:ℝ)^n := by exact_mod_cast k.isLt
  ext x
  constructor
  · rintro ⟨hc,hx⟩
    change dyadicCode n x=(k.val:ℤ) at hc
    rw [dyadic_code_on_unit_interval n x hx] at hc
    have hh := Int.floor_eq_iff.mp hc
    change (k.val:ℝ)≤(2:ℝ)^n*x ∧ (2:ℝ)^n*x<(k.val:ℝ)+1 at hh
    exact ⟨(div_le_iff₀ hp).mpr (by nlinarith [hh.1]),
      (lt_div_iff₀ hp).mpr (by nlinarith [hh.2])⟩
  · intro hx
    have hx0 : 0≤x := le_trans (by positivity) hx.1
    have hx1 : x<1 := lt_of_lt_of_le hx.2 ((div_le_one hp).mpr hk)
    refine ⟨?_,hx0,hx1⟩
    change dyadicCode n x=(k.val:ℤ)
    rw [dyadic_code_on_unit_interval n x ⟨hx0,hx1⟩]
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor
    · nlinarith [(div_le_iff₀ hp).mp hx.1]
    · nlinarith [(lt_div_iff₀ hp).mp hx.2]

theorem dyadic_cell_mass (n : ℕ) (k : Fin (2^n)) :
    unitIntervalLaw (dyadicCell n k)=ENNReal.ofReal ((2:ℝ)^n)⁻¹ := by
  rw [unitIntervalLaw_eq,Measure.restrict_apply (measurable_dyadicCell n k),dyadic_cell_inter,
    Real.volume_Ico]
  congr 1
  ring

lemma dyadic_cells_disjoint (n : ℕ) : Pairwise (Disjoint on dyadicCell n) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  apply hij
  apply Fin.ext
  change dyadicCode n x=(i.val:ℤ) at hi
  change dyadicCode n x=(j.val:ℤ) at hj
  exact_mod_cast hi.symm.trans hj

lemma dyadic_cells_cover (n : ℕ) : ⋃ k,dyadicCell n k=univ := by
  ext x
  simp only [mem_iUnion,mem_univ,iff_true]
  have hb := dyadic_code_bounds n x
  refine ⟨⟨(dyadicCode n x).toNat,?_⟩,?_⟩
  · have hh : dyadicCode n x < ((2^n:ℕ):ℤ) := by exact_mod_cast hb.2
    omega
  · change dyadicCode n x=Int.ofNat (dyadicCode n x).toNat
    exact (Int.toNat_of_nonneg hb.1).symm

lemma dyadic_cells_mass_sum (n : ℕ) : ∑ k,unitIntervalLaw (dyadicCell n k)=1 := by
  have h := measure_iUnion (μ := unitIntervalLaw) (dyadic_cells_disjoint n) (measurable_dyadicCell n)
  simpa only [dyadic_cells_cover,measure_univ,tsum_fintype] using h.symm

theorem dyadic_cell_L2_dimension (n : ℕ) :
    Module.finrank ℝ (lpMeas ℝ ℝ (⨆ k,MeasurableSpace.comap
      ((dyadicCell n k).indicator (fun _ => (1:ℝ))) inferInstance) 2 unitIntervalLaw)=2^n := by
  simpa using finite_cell_L2_dimension unitIntervalLaw (dyadicCell n)
    (measurable_dyadicCell n) (dyadic_cells_disjoint n) (dyadic_cells_mass_sum n)
    (fun k => by rw [dyadic_cell_mass]; positivity)

end Asakura.Chapter1Complete

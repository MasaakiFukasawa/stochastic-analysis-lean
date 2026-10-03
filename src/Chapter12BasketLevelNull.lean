import Chapter12MonotoneFiber
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- A positive exponential basket has Lebesgue-null level sets, by isolating
one coordinate and applying Fubini to its strictly increasing fibers. -/
theorem exponential_basket_level_null (d : ℕ) (c : Fin (d+1) → ℝ)
    (hc : 0<c 0) (K : ℝ) :
    volume {y : Fin (d+1) → ℝ | (∑ i,c i*Real.exp (y i))=K}=0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0
  let A := fun z : (Fin d → ℝ) × ℝ => ∑ i,c i*Real.exp (e.symm (z.2,z.1) i)
  have hA : Measurable A := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul (Real.measurable_exp.comp ((measurable_pi_apply i).comp
      (e.symm.measurable.comp (measurable_snd.prodMk measurable_fst))))
  have hmono (b : Fin d → ℝ) : StrictMono (fun z => A (b,z)) := by
    intro z v hzv
    change (∑ i,c i*Real.exp (@Fin.insertNth d (fun _ => ℝ) 0 z b i)) <
      (∑ i,c i*Real.exp (@Fin.insertNth d (fun _ => ℝ) 0 v b i))
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.insertNth_apply_same,←Fin.succAbove_zero,Fin.insertNth_apply_succAbove]
    have hh := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hzv) hc
    linarith
  have hz := monotone_fiber_no_atoms (volume : Measure (Fin d → ℝ)) volume A hA hmono K
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0)
  have hs := Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin d → ℝ)))
  have hpush := hs.comp he
  have hm : MeasurableSet {z | A z=K} := hA (measurableSet_singleton K)
  have hnull := hpush.measure_preimage hm.nullMeasurableSet
  rw [hz] at hnull
  convert hnull using 1
  congr 1
  ext y
  simp only [Set.mem_setOf_eq,Set.mem_preimage,Function.comp_def,A,e,Prod.swap]
  simp

end Asakura.Chapter12

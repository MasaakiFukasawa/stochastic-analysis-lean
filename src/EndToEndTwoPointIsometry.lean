import Chapter1TwoPointProjection
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory Set
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
namespace Asakura.EndToEnd
open Chapter1Complete

private theorem atom_pos (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (i : Fin 2) :
    0 < twoPointLaw p {i} := by
  fin_cases i <;> simp [twoPointLaw, hp, sub_pos.mpr hp1]

private theorem all_of_ae (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    {Q : Fin 2 → Prop} (h : ∀ᵐ i ∂twoPointLaw p, Q i) : ∀ i, Q i := by
  intro i
  by_contra hi
  have hzero : twoPointLaw p {i} = 0 := measure_mono_null
    (by intro j hj; simpa only [mem_singleton_iff.mp hj, mem_ofPred_eq] using hi) (ae_iff.mp h)
  exact (ne_of_gt (atom_pos p hp hp1 i)) hzero

noncomputable def twoPointCoordinates (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Lp ℝ 2 (twoPointLaw p) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun f := WithLp.toLp 2 (fun i => f i * Real.sqrt (if i = 0 then p else 1-p))
  map_add' f g := by
    ext i
    change (f+g) i * _ = f i * _ + g i * _
    rw [all_of_ae p hp hp1 (Lp.coeFn_add f g) i]
    simp [Pi.add_apply, add_mul]
  map_smul' c f := by
    ext i
    change (c • f) i * _ = c * (f i * _)
    rw [all_of_ae p hp hp1 (Lp.coeFn_smul c f) i]
    simp [mul_assoc]

private theorem coordinate_inner (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (f g : Lp ℝ 2 (twoPointLaw p)) :
    inner ℝ (twoPointCoordinates p hp hp1 f) (twoPointCoordinates p hp hp1 g) =
      inner ℝ f g := by
  rw [L2.inner_def]
  simpa [PiLp.inner_apply, Fin.sum_univ_two, twoPointCoordinates, real_inner_comm] using
    two_point_inner_product p hp.le hp1.le g f

noncomputable def twoPointIsometry (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Lp ℝ 2 (twoPointLaw p) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (twoPointCoordinates p hp hp1).isometryOfInner (coordinate_inner p hp hp1)

private theorem finite_law (p : ℝ) : IsFiniteMeasure (twoPointLaw p) := by
  constructor
  simp [twoPointLaw, ENNReal.add_lt_top]

private theorem raw_memLp (p : ℝ) (f : Fin 2 → ℝ) : MemLp f 2 (twoPointLaw p) := by
  letI := finite_law p
  apply MemLp.of_bound (by fun_prop) (|f 0| + |f 1|)
  filter_upwards [] with i
  fin_cases i
  · change |f 0| ≤ |f 0| + |f 1|
    exact le_add_of_nonneg_right (abs_nonneg _)
  · change |f 1| ≤ |f 0| + |f 1|
    exact le_add_of_nonneg_left (abs_nonneg _)

noncomputable def twoPointEquiv (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Lp ℝ 2 (twoPointLaw p) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearIsometryEquiv.ofSurjective (twoPointIsometry p hp hp1) (by
    intro v
    let f : Fin 2 → ℝ := fun i => v i / Real.sqrt (if i = 0 then p else 1-p)
    refine ⟨(raw_memLp p f).toLp f, ?_⟩
    ext i
    change ((raw_memLp p f).toLp f) i * Real.sqrt (if i = 0 then p else 1-p) = v i
    rw [all_of_ae p hp hp1 (MemLp.coeFn_toLp (raw_memLp p f)) i]
    have hs : Real.sqrt (if i = 0 then p else 1-p) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.2
      split_ifs <;> linarith
    exact div_mul_cancel₀ (v i) hs)

#print axioms twoPointEquiv
end Asakura.EndToEnd

import Chapter1DyadicConditional
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Asakura.Chapter1Complete
set_option maxHeartbeats 3000000

noncomputable def binaryBit (i : ℕ) (x : ℝ) : Fin 2 :=
  ⟨(dyadicDigit i x).toNat,by have h := dyadic_digit_bounds i x; omega⟩
noncomputable def binaryPrefix (n : ℕ) (x : ℝ) : Fin n → Fin 2 := fun i => binaryBit i x

lemma binaryBit_int (i : ℕ) (x : ℝ) : ((binaryBit i x).val:ℤ)=dyadicDigit i x :=
  Int.toNat_of_nonneg (dyadic_digit_bounds i x).1

lemma binary_prefix_fiber (n : ℕ) (x y : ℝ) :
    binaryPrefix n x=binaryPrefix n y ↔ dyadicCode n x=dyadicCode n y := by
  rw [← dyadic_prefix_fibers]
  constructor
  · intro h i hi
    have hh := congrArg (fun b : Fin 2 => (b.val:ℤ)) (congrFun h ⟨i,hi⟩)
    simpa [binaryPrefix,binaryBit_int] using hh
  · intro h
    funext i
    apply Fin.ext
    change (dyadicDigit i x).toNat=(dyadicDigit i y).toNat
    rw [h i i.isLt]

lemma measurable_binaryBit (i : ℕ) : Measurable (binaryBit i) := by
  have he : binaryBit i=fun x => Fin.ofNat 2 (dyadicDigit i x).toNat := by
    funext x
    apply Fin.ext
    have hb := dyadic_digit_bounds i x
    simp only [binaryBit,Fin.val_ofNat]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  rw [he]
  exact (measurable_of_countable (f := fun z : ℤ => Fin.ofNat 2 (z%2).toNat)).comp
    ((measurable_const.mul measurable_id).floor)

lemma measurable_binaryPrefix (n : ℕ) : Measurable (binaryPrefix n) :=
  measurable_pi_iff.mpr fun i => measurable_binaryBit i

noncomputable def dyadicMidpoint (n : ℕ) (k : Fin (2^n)) : ℝ := ((k:ℝ)+1/2)/(2:ℝ)^n

lemma dyadic_midpoint_cell (n : ℕ) (k : Fin (2^n)) :
    dyadicMidpoint n k∈dyadicCell n k := by
  have hp : (0:ℝ)<2^n := by positivity
  have h : dyadicMidpoint n k∈Ico ((k:ℝ)/(2:ℝ)^n) (((k:ℝ)+1)/(2:ℝ)^n) := by
    constructor <;> dsimp [dyadicMidpoint]
    · exact (div_le_div_iff_of_pos_right hp).mpr (by linarith)
    · exact (div_lt_div_iff_of_pos_right hp).mpr (by linarith)
  rw [← dyadic_cell_inter] at h
  exact h.1

lemma binary_midpoints_bijective (n : ℕ) :
    Bijective (fun k : Fin (2^n) => binaryPrefix n (dyadicMidpoint n k)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro i j h
    have hc := (binary_prefix_fiber n _ _).mp h
    have hi := dyadic_midpoint_cell n i
    have hj := dyadic_midpoint_cell n j
    change dyadicCode n (dyadicMidpoint n i)=(i.val:ℤ) at hi
    change dyadicCode n (dyadicMidpoint n j)=(j.val:ℤ) at hj
    apply Fin.ext
    exact_mod_cast hi.symm.trans (hc.trans hj)
  · simp

noncomputable def fairBitLaw : Measure (Fin 2) := (PMF.uniformOfFintype (Fin 2)).toMeasure
instance : IsProbabilityMeasure fairBitLaw := by unfold fairBitLaw; infer_instance

theorem binary_prefix_law (n : ℕ) :
    unitIntervalLaw.map (binaryPrefix n)=Measure.pi (fun _ : Fin n => fairBitLaw) := by
  apply Measure.ext_of_singleton
  intro b
  obtain ⟨k,rfl⟩ := (binary_midpoints_bijective n).2 b
  rw [Measure.map_apply (measurable_binaryPrefix n) (measurableSet_singleton _)]
  have he : binaryPrefix n ⁻¹' {binaryPrefix n (dyadicMidpoint n k)}=dyadicCell n k := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,binary_prefix_fiber]
    exact Iff.of_eq (congrArg (fun z => dyadicCode n x=z) (dyadic_midpoint_cell n k))
  rw [he,dyadic_cell_mass,Measure.pi_singleton]
  simp only [fairBitLaw,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply,Fintype.card_fin,Finset.prod_const,Finset.card_univ]
  rw [ENNReal.ofReal_inv_of_pos (by positivity),ENNReal.ofReal_pow (by positivity)]
  norm_num [ENNReal.inv_pow]

theorem binary_prefix_independent (n : ℕ) :
    iIndepFun (fun i : Fin n => binaryBit i) unitIntervalLaw := by
  have hm i : unitIntervalLaw.map (binaryBit (i:Fin n))=fairBitLaw := by
    have h := (measurePreserving_eval (fun _ : Fin n => fairBitLaw) i).map_eq
    rw [← binary_prefix_law,Measure.map_map (measurable_pi_apply i) (measurable_binaryPrefix n)] at h
    exact h
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i : Fin n => (measurable_binaryBit i).aemeasurable)).mpr
  change unitIntervalLaw.map (binaryPrefix n)=_
  rw [binary_prefix_law]
  congr 1
  funext i
  exact (hm i).symm

theorem binary_bits_independent : iIndepFun binaryBit unitIntervalLaw := by
  apply iIndepFun_iff_finset.mpr
  intro s
  let n := s.sup id+1
  let f : s → Fin n := fun i => ⟨i.val,by have h := Finset.le_sup (f := id) i.property; dsimp only [id] at h; dsimp [n]; omega⟩
  have hf : Injective f := fun i j h => Subtype.ext (congrArg Fin.val h)
  exact (binary_prefix_independent n).precomp (g := f) hf

/-- The integer-valued digits of the manuscript form an independent sequence. -/
theorem dyadic_digits_independent : iIndepFun dyadicDigit unitIntervalLaw := by
  have h := binary_bits_independent.comp (fun _ (b : Fin 2) => (b.val:ℤ))
    (fun _ => measurable_of_finite _)
  simpa only [Function.comp_def,binaryBit_int] using h

end Asakura.Chapter1Complete

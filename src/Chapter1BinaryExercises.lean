import Chapter1DyadicOriginalSpace

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Asakura.Chapter1Complete
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Measure.Subtype.measureSpace

theorem binary_original_prefix_law (n : ℕ) :
    (volume : Measure BinarySpace).map (fun x : BinarySpace => binaryPrefix n x)=
      Measure.pi (fun _ : Fin n => fairBitLaw) := by
  rw [show (fun x : BinarySpace => binaryPrefix n x)=binaryPrefix n ∘ Subtype.val from rfl,
    ← Measure.map_map (measurable_binaryPrefix n) measurable_subtype_coe,binary_space_map,
    binary_prefix_law]

theorem binary_original_prefix_independent (n : ℕ) :
    iIndepFun (fun i : Fin n => fun x : BinarySpace => binaryBit i x) volume := by
  have hm (i : Fin n) : (volume : Measure BinarySpace).map (fun x : BinarySpace => binaryBit i x)=fairBitLaw := by
    have h := (measurePreserving_eval (fun _ : Fin n => fairBitLaw) i).map_eq
    rw [← binary_original_prefix_law,Measure.map_map (measurable_pi_apply i)
      (show Measurable (fun x : BinarySpace => binaryPrefix n x) from
        (measurable_binaryPrefix n).comp measurable_subtype_coe)] at h
    exact h
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i : Fin n => ((measurable_binaryBit i).comp measurable_subtype_coe).aemeasurable)).mpr
  change (volume : Measure BinarySpace).map (fun x : BinarySpace => binaryPrefix n x)=_
  rw [binary_original_prefix_law]
  congr 1
  funext i
  exact (hm i).symm

theorem binary_original_digits_independent :
    iIndepFun (fun i => fun x : BinarySpace => dyadicDigit i x) volume := by
  have hb : iIndepFun (fun i => fun x : BinarySpace => binaryBit i x) volume := by
    apply iIndepFun_iff_finset.mpr
    intro s
    let n := s.sup id+1
    let f : s → Fin n := fun i => ⟨i.val,by
      have h := Finset.le_sup (f := id) i.property
      dsimp only [id] at h
      dsimp [n]
      omega⟩
    have hf : Injective f := fun i j h => Subtype.ext (congrArg Fin.val h)
    exact (binary_original_prefix_independent n).precomp (g := f) hf
  have h := hb.comp (fun _ (b : Fin 2) => (b.val:ℤ)) (fun _ => measurable_of_finite _)
  simpa only [Function.comp_def,binaryBit_int] using h

/-- Every integrable random variable on the exact sample space admits the
displayed interval-average formula. Extending it off that space is only
notation for Lebesgue integration and imposes no additional hypothesis. -/
theorem binary_original_arbitrary_X (n : ℕ) (X : BinarySpace → ℝ) (hX : Integrable X volume) :
    ∃ Xbar : ℝ → ℝ,(∀ x : BinarySpace,Xbar x=X x) ∧
      (volume : Measure BinarySpace)[X |
        MeasurableSpace.comap (fun x : BinarySpace => dyadicPrefix n x) inferInstance] =ᵐ[volume]
      fun x : BinarySpace => (2:ℝ)^n * ∫ y in Ico
        (∑ i∈Finset.range n,(dyadicDigit i x:ℝ)/(2:ℝ)^(i+1))
        ((∑ i∈Finset.range n,(dyadicDigit i x:ℝ)/(2:ℝ)^(i+1))+(2:ℝ)⁻¹^n),Xbar y := by
  let Xbar := Function.extend Subtype.val X (fun _ => (0:ℝ))
  have he (x : BinarySpace) : Xbar x=X x := Subtype.val_injective.extend_apply X _ x
  refine ⟨Xbar,he,?_⟩
  have h := binary_original_conditional n Xbar (by simpa only [he] using hX)
  simp only [he] at h
  apply h.trans
  apply ae_of_all
  intro x
  simp only [dyadic_weighted_digits]
  have hend : ((dyadicCode n x:ℝ)+1)/(2:ℝ)^n=
      (dyadicCode n x:ℝ)/(2:ℝ)^n+(2:ℝ)⁻¹^n := by rw [inv_pow]; ring
  rw [hend]

end Asakura.Chapter1Complete

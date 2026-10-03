import Chapter1DyadicIndependence

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Asakura.Chapter1Complete
set_option maxHeartbeats 2000000

attribute [local instance] Measure.Subtype.measureSpace

abbrev BinarySpace := Ioc (0:ℝ) 1

lemma binary_space_map : (volume : Measure BinarySpace).map Subtype.val=unitIntervalLaw :=
  map_comap_subtype_coe measurableSet_Ioc volume

instance : IsProbabilityMeasure (volume : Measure BinarySpace) := by
  constructor
  change volume.comap (Subtype.val : BinarySpace → ℝ) univ=1
  rw [comap_subtype_coe_apply measurableSet_Ioc,image_univ,Subtype.range_coe]
  norm_num

lemma binary_space_cell_mass (n : ℕ) (k : Fin (2^n)) :
    (volume : Measure BinarySpace) (Subtype.val ⁻¹' dyadicCell n k)=unitIntervalLaw (dyadicCell n k) := by
  rw [← binary_space_map,Measure.map_apply measurable_subtype_coe (measurable_dyadicCell n k)]

lemma binary_space_cell_sigma (n : ℕ) :
    (⨆ k,MeasurableSpace.comap ((Subtype.val ⁻¹' dyadicCell n k).indicator
      (fun _ : BinarySpace => (1:ℝ))) inferInstance)=
      MeasurableSpace.comap (fun x : BinarySpace => dyadicPrefix n x) inferInstance := by
  have h := congrArg (fun G : MeasurableSpace ℝ => G.comap (Subtype.val : BinarySpace → ℝ))
    (dyadic_cells_sigma n)
  classical
  simp only [MeasurableSpace.comap_iSup,MeasurableSpace.comap_comp] at h
  apply Eq.trans _ h
  congr 1

theorem binary_original_L2_dimension (n : ℕ) :
    Module.finrank ℝ (lpMeas ℝ ℝ
      (MeasurableSpace.comap (fun x : BinarySpace => dyadicPrefix n x) inferInstance)
      2 (volume : Measure BinarySpace))=2^n := by
  have h := finite_cell_L2_dimension (volume : Measure BinarySpace)
    (fun k => Subtype.val ⁻¹' dyadicCell n k)
    (fun k => (measurable_dyadicCell n k).preimage measurable_subtype_coe)
    (fun i j hij => (dyadic_cells_disjoint n hij).preimage Subtype.val)
    (by simpa only [binary_space_cell_mass] using dyadic_cells_mass_sum n)
    (fun k => by rw [binary_space_cell_mass,dyadic_cell_mass]; positivity)
  rw [binary_space_cell_sigma] at h
  simpa using h

lemma binary_space_cell_integral (n : ℕ) (k : Fin (2^n)) (X : ℝ → ℝ) :
    (∫ x in Subtype.val ⁻¹' dyadicCell n k,X x ∂(volume : Measure BinarySpace))=
      ∫ x in Ico ((k:ℝ)/(2:ℝ)^n) (((k:ℝ)+1)/(2:ℝ)^n),X x := by
  rw [← integral_indicator ((measurable_dyadicCell n k).preimage measurable_subtype_coe)]
  have he : (fun x : BinarySpace => (Subtype.val ⁻¹' dyadicCell n k).indicator (fun x => X x) x)=
      fun x : BinarySpace => (dyadicCell n k).indicator X x := by
    funext x
    by_cases hx : (x:ℝ)∈dyadicCell n k <;> simp [hx]
  rw [he,integral_subtype measurableSet_Ioc]
  rw [show (∫ x in Ioc 0 1,(dyadicCell n k).indicator X x)=
      ∫ x,(dyadicCell n k).indicator X x ∂unitIntervalLaw from rfl,
    integral_indicator (measurable_dyadicCell n k),dyadic_cell_integral]

/-- The conditional average on the literal sample space (0,1]. A function
on that space can be extended arbitrarily outside it, without affecting the integral. -/
theorem binary_original_conditional (n : ℕ) (X : ℝ → ℝ)
    (hX : Integrable (fun x : BinarySpace => X x) volume) :
    (volume : Measure BinarySpace)[(fun x : BinarySpace => X x) |
      MeasurableSpace.comap (fun x : BinarySpace => dyadicPrefix n x) inferInstance] =ᵐ[volume]
      fun x : BinarySpace => (2:ℝ)^n * ∫ y in Ico
        ((dyadicCode n x:ℝ)/(2:ℝ)^n)
        (((dyadicCode n x:ℝ)+1)/(2:ℝ)^n),X y := by
  classical
  have h := Asakura.FullAudit.finite_cells_condExp (volume : Measure BinarySpace)
    (fun k => Subtype.val ⁻¹' dyadicCell n k)
    (fun k => (measurable_dyadicCell n k).preimage measurable_subtype_coe)
    (fun i j hij => (dyadic_cells_disjoint n hij).preimage Subtype.val)
    (by simpa only [binary_space_cell_mass] using dyadic_cells_mass_sum n) hX
  rw [binary_space_cell_sigma] at h
  filter_upwards [h] with x hx
  rw [← hx]
  have hc : (x:ℝ)∈⋃ k,dyadicCell n k := by rw [dyadic_cells_cover]; trivial
  obtain ⟨k,hk⟩ := mem_iUnion.mp hc
  rw [Finset.sum_eq_single k]
  · rw [Set.indicator_of_mem (show x∈Subtype.val ⁻¹' dyadicCell n k from hk),binary_space_cell_integral]
    have hm : (volume : Measure BinarySpace).real (Subtype.val ⁻¹' dyadicCell n k)=((2:ℝ)^n)⁻¹ := by
      rw [measureReal_def,binary_space_cell_mass,dyadic_cell_mass,ENNReal.toReal_ofReal (by positivity)]
    have he : (dyadicCode n x:ℝ)=(k:ℝ) := by exact_mod_cast hk
    rw [hm,inv_inv,he]
  · intro j _ hj
    apply Set.indicator_of_notMem
    exact fun hxj => Set.disjoint_left.mp (dyadic_cells_disjoint n hj) hxj hk
  · simp

end Asakura.Chapter1Complete

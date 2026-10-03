import Chapter1DyadicCells

open MeasureTheory Set Function
open scoped ENNReal BigOperators
namespace Asakura.Chapter1Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

noncomputable def dyadicPrefix (n : ℕ) (x : ℝ) : Fin n → ℤ := fun i => dyadicDigit i x

lemma dyadic_prefix_sigma (n : ℕ) :
    MeasurableSpace.comap (dyadicPrefix n) inferInstance=
      MeasurableSpace.comap (dyadicCode n) inferInstance := by
  rw [← Asakura.FullAudit.fiber_sigma_eq_comap,← Asakura.FullAudit.fiber_sigma_eq_comap]
  have he (x y : ℝ) : dyadicPrefix n x=dyadicPrefix n y ↔ dyadicCode n x=dyadicCode n y := by
    rw [← dyadic_prefix_fibers]
    exact ⟨fun h i hi => congrFun h ⟨i,hi⟩,fun h => funext fun i => h i i.isLt⟩
  apply le_antisymm <;> intro A hA x y hxy
  · exact hA x y ((he x y).mpr hxy)
  · exact hA x y ((he x y).mp hxy)

lemma dyadic_cells_sigma (n : ℕ) :
    (⨆ k,MeasurableSpace.comap ((dyadicCell n k).indicator (fun _ => (1:ℝ))) inferInstance)=
      MeasurableSpace.comap (dyadicPrefix n) inferInstance := by
  rw [Asakura.FullAudit.indicator_generated_sigma,dyadic_prefix_sigma]
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro A ⟨k,rfl⟩
    exact ⟨{(k.val:ℤ)},measurableSet_singleton _,rfl⟩
  · rintro A ⟨B,hB,rfl⟩
    have he : dyadicCode n ⁻¹' B=⋃ k : Fin (2^n),⋃ (_ : (k.val:ℤ)∈B),dyadicCell n k := by
      ext x
      simp only [mem_preimage,mem_iUnion]
      constructor
      · intro hx
        have hc : x∈⋃ k,dyadicCell n k := by rw [dyadic_cells_cover]; trivial
        obtain ⟨k,hk⟩ := mem_iUnion.mp hc
        exact ⟨k,by simpa only [dyadicCell,mem_setOf_eq] using (show (k.val:ℤ)∈B from hk ▸ hx),hk⟩
      · rintro ⟨k,hk,hx⟩
        exact hx ▸ hk
    rw [he]
    exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
      MeasurableSpace.measurableSet_generateFrom (mem_range_self k)

/-- The exercise's actual binary information has 2^n independent L² coordinates. -/
theorem binary_information_dimension (n : ℕ) :
    Module.finrank ℝ (lpMeas ℝ ℝ (MeasurableSpace.comap (dyadicPrefix n) inferInstance)
      2 unitIntervalLaw)=2^n := by
  rw [← dyadic_cells_sigma]
  exact dyadic_cell_L2_dimension n

lemma dyadic_cell_integral (n : ℕ) (k : Fin (2^n)) (X : ℝ → ℝ) :
    (∫ x in dyadicCell n k,X x ∂unitIntervalLaw)=
      ∫ x in Ico ((k:ℝ)/(2:ℝ)^n) (((k:ℝ)+1)/(2:ℝ)^n),X x := by
  rw [unitIntervalLaw_eq,Measure.restrict_restrict (measurable_dyadicCell n k),dyadic_cell_inter]

/-- Conditional expectation is the average on the cell selected by the
weighted digits, with no assumption that x avoids binary endpoints. -/
theorem binary_conditional_expectation (n : ℕ) {X : ℝ → ℝ}
    (hX : Integrable X unitIntervalLaw) :
    unitIntervalLaw[X | MeasurableSpace.comap (dyadicPrefix n) inferInstance] =ᵐ[unitIntervalLaw]
      fun x => (2:ℝ)^n * ∫ y in Ico
        (∑ i∈Finset.range n,(dyadicDigit i x:ℝ)/(2:ℝ)^(i+1))
        ((∑ i∈Finset.range n,(dyadicDigit i x:ℝ)/(2:ℝ)^(i+1))+(2:ℝ)⁻¹^n),X y := by
  classical
  have h := Asakura.FullAudit.finite_cells_condExp unitIntervalLaw (dyadicCell n)
    (measurable_dyadicCell n) (dyadic_cells_disjoint n) (dyadic_cells_mass_sum n) hX
  rw [dyadic_cells_sigma] at h
  filter_upwards [h] with x hx
  rw [← hx,dyadic_weighted_digits]
  have hc : x∈⋃ k,dyadicCell n k := by rw [dyadic_cells_cover]; trivial
  obtain ⟨k,hk⟩ := mem_iUnion.mp hc
  rw [Finset.sum_eq_single k]
  · rw [Set.indicator_of_mem hk,dyadic_cell_integral]
    have hm : unitIntervalLaw.real (dyadicCell n k)=((2:ℝ)^n)⁻¹ := by
      rw [measureReal_def,dyadic_cell_mass,ENNReal.toReal_ofReal (by positivity)]
    rw [hm,inv_inv]
    have he : (dyadicCode n x:ℝ)=(k:ℝ) := by exact_mod_cast hk
    rw [he]
    congr 2
    rw [inv_pow]
    ring
  · intro j _ hj
    apply Set.indicator_of_notMem
    exact fun hxj => Set.disjoint_left.mp (dyadic_cells_disjoint n hj) hxj hk
  · simp

end Asakura.Chapter1Complete

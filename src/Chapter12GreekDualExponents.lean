import Chapter12FiniteGreekExponents

open scoped ENNReal NNReal
namespace Asakura.Chapter12
instance greekFact16 : Fact (1 ≤ (16:ℝ≥0∞)) := ⟨by norm_num⟩
instance greekDualFact4 : Fact (1 ≤ (4/3:ℝ≥0∞)) := ⟨by
  have h : (1:ℝ≥0) ≤ 4/3 := by rw [←NNReal.coe_le_coe]; norm_num
  have hh := ENNReal.coe_le_coe.mpr h
  simpa only [ENNReal.coe_one,ENNReal.coe_div (by norm_num : (3:ℝ≥0) ≠ 0),ENNReal.coe_ofNat] using hh⟩
instance greekDualFact8 : Fact (1 ≤ (8/7:ℝ≥0∞)) := ⟨by
  have h : (1:ℝ≥0) ≤ 8/7 := by rw [←NNReal.coe_le_coe]; norm_num
  have hh := ENNReal.coe_le_coe.mpr h
  simpa only [ENNReal.coe_one,ENNReal.coe_div (by norm_num : (7:ℝ≥0) ≠ 0),ENNReal.coe_ofNat] using hh⟩
instance greekDualFact16 : Fact (1 ≤ (16/15:ℝ≥0∞)) := ⟨by
  have h : (1:ℝ≥0) ≤ 16/15 := by rw [←NNReal.coe_le_coe]; norm_num
  have hh := ENNReal.coe_le_coe.mpr h
  simpa only [ENNReal.coe_one,ENNReal.coe_div (by norm_num : (15:ℝ≥0) ≠ 0),ENNReal.coe_ofNat] using hh⟩
instance greekConjugate4 : ENNReal.HolderConjugate 4 (4/3) := by
  constructor
  have h : (4:ℝ≥0)⁻¹+(4/3:ℝ≥0)⁻¹ = 1 := by apply NNReal.eq; norm_num
  have hh := congrArg (fun x : ℝ≥0 => (x:ℝ≥0∞)) h
  simpa only [ENNReal.coe_add,ENNReal.coe_inv (by norm_num : (4:ℝ≥0) ≠ 0),
    ENNReal.coe_inv (by positivity : (4/3:ℝ≥0) ≠ 0),ENNReal.coe_div (by norm_num : (3:ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat,ENNReal.coe_one,inv_one] using hh
instance greekConjugate8 : ENNReal.HolderConjugate 8 (8/7) := by
  constructor
  have h : (8:ℝ≥0)⁻¹+(8/7:ℝ≥0)⁻¹ = 1 := by apply NNReal.eq; norm_num
  have hh := congrArg (fun x : ℝ≥0 => (x:ℝ≥0∞)) h
  simpa only [ENNReal.coe_add,ENNReal.coe_inv (by norm_num : (8:ℝ≥0) ≠ 0),
    ENNReal.coe_inv (by positivity : (8/7:ℝ≥0) ≠ 0),ENNReal.coe_div (by norm_num : (7:ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat,ENNReal.coe_one,inv_one] using hh
instance greekConjugate16 : ENNReal.HolderConjugate 16 (16/15) := by
  constructor
  have h : (16:ℝ≥0)⁻¹+(16/15:ℝ≥0)⁻¹ = 1 := by apply NNReal.eq; norm_num
  have hh := congrArg (fun x : ℝ≥0 => (x:ℝ≥0∞)) h
  simpa only [ENNReal.coe_add,ENNReal.coe_inv (by norm_num : (16:ℝ≥0) ≠ 0),
    ENNReal.coe_inv (by positivity : (16/15:ℝ≥0) ≠ 0),ENNReal.coe_div (by norm_num : (15:ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat,ENNReal.coe_one,inv_one] using hh
end Asakura.Chapter12

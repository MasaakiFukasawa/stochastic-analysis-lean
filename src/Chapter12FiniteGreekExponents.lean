import Chapter12IBPTestMoments

open scoped ENNReal
namespace Asakura.Chapter12
instance greekFact4 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
instance greekFact8 : Fact (1 ≤ (8 : ℝ≥0∞)) := ⟨by norm_num⟩
instance greekHolder4 : ENNReal.HolderTriple 4 4 2 := by
  convert holder_double_exponent 2 using 1 <;> norm_num
instance greekHolder8 : ENNReal.HolderTriple 8 8 4 := by
  convert holder_double_exponent 4 using 1 <;> norm_num
instance greekHolder16 : ENNReal.HolderTriple 16 16 8 := by
  convert holder_double_exponent 8 using 1 <;> norm_num
instance greekHolder32 : ENNReal.HolderTriple 32 32 16 := by
  convert holder_double_exponent 16 using 1 <;> norm_num
end Asakura.Chapter12

import Chapter12WienerNontrivial

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- A finite interval of positive length supplies a nonzero deterministic
Wiener direction; degenerate horizon zero is not used in this chapter. -/
theorem finite_horizon_L2_nontrivial (T : ℝ) (hT : 0 < T) :
    Nontrivial (Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) := by
  let μ := (volume.restrict (Ioi (0:ℝ))).restrict (Iic T)
  have hm : μ (Ioc 0 T) = ENNReal.ofReal T := by
    rw [Measure.restrict_apply measurableSet_Ioc]
    rw [inter_eq_left.mpr (show Ioc 0 T ⊆ Iic T from fun _ h => h.2)]
    rw [Measure.restrict_apply measurableSet_Ioc]
    rw [inter_eq_left.mpr (show Ioc 0 T ⊆ Ioi 0 from fun _ h => h.1)]
    rw [Real.volume_Ioc,sub_zero]
  let f : Lp ℝ 2 μ := indicatorConstLp 2 measurableSet_Ioc (by rw [hm]; simp) (1:ℝ)
  apply nontrivial_of_ne f 0
  intro he
  have hn : 0 < ‖f‖ := by
    dsimp only [f]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [norm_one,one_mul,Measure.real,hm,ENNReal.toReal_ofReal hT.le]
    exact Real.rpow_pos_of_pos hT _
  rw [he,norm_zero] at hn
  exact lt_irrefl _ hn

end Asakura.Chapter12

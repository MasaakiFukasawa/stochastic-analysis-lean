import Chapter10DensityProductFormula

open MeasureTheory Set
namespace Asakura.Chapter10
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The product-formula martingale has an L1 bound made only from the squared
path bound. This is the uniform-integrability step in the covariance equation. -/
theorem product_residual_bound (X Y G H : ℝ → ℝ)
    (b r K C q c : ℝ) (hb : 0≤b) (hr : r∈Icc 0 b)
    (hK : 0≤K) (hC : 0≤C) (hc : ‖c‖≤q)
    (hX : ∀ s∈Icc 0 b,‖X s‖≤K) (hY : ∀ s∈Icc 0 b,‖Y s‖≤K)
    (hG : ∀ s∈Icc 0 b,‖G s‖≤C*K) (hH : ∀ s∈Icc 0 b,‖H s‖≤C*K) :
    ‖X r*Y r-X 0*Y 0-(∫ s in 0..r,Y s*G s)-(∫ s in 0..r,X s*H s)-c‖≤
      2*K^2+2*b*C*K^2+q := by
  have hp s (hs : s∈Icc 0 b) : ‖X s*Y s‖≤K^2 := by
    rw [norm_mul,pow_two]
    exact mul_le_mul (hX s hs) (hY s hs) (norm_nonneg _) hK
  have hI : ‖∫ s in 0..r,Y s*G s‖≤b*C*K^2 := by
    have hh : ‖∫ s in 0..r,Y s*G s‖≤C*K^2*|r-0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => by
        have hs' : s∈Icc 0 b := by
          rw [uIoc_of_le hr.1] at hs
          exact ⟨hs.1.le,hs.2.trans hr.2⟩
        rw [norm_mul]
        have h := mul_le_mul (hY s hs') (hG s hs') (norm_nonneg _) hK
        nlinarith)
    rw [sub_zero,abs_of_nonneg hr.1] at hh
    have hkr : C*K^2*r≤C*K^2*b := mul_le_mul_of_nonneg_left hr.2 (by positivity)
    nlinarith
  have hJ : ‖∫ s in 0..r,X s*H s‖≤b*C*K^2 := by
    have hh : ‖∫ s in 0..r,X s*H s‖≤C*K^2*|r-0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => by
        have hs' : s∈Icc 0 b := by
          rw [uIoc_of_le hr.1] at hs
          exact ⟨hs.1.le,hs.2.trans hr.2⟩
        rw [norm_mul]
        have h := mul_le_mul (hX s hs') (hH s hs') (norm_nonneg _) hK
        nlinarith)
    rw [sub_zero,abs_of_nonneg hr.1] at hh
    have hkr : C*K^2*r≤C*K^2*b := mul_le_mul_of_nonneg_left hr.2 (by positivity)
    nlinarith
  calc
    _ ≤ ‖X r*Y r-X 0*Y 0-(∫ s in 0..r,Y s*G s)-(∫ s in 0..r,X s*H s)‖+‖c‖ := norm_sub_le _ _
    _ ≤ (‖X r*Y r-X 0*Y 0-(∫ s in 0..r,Y s*G s)‖+‖∫ s in 0..r,X s*H s‖)+‖c‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ((‖X r*Y r-X 0*Y 0‖+‖∫ s in 0..r,Y s*G s‖)+‖∫ s in 0..r,X s*H s‖)+‖c‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ (((‖X r*Y r‖+‖X 0*Y 0‖)+‖∫ s in 0..r,Y s*G s‖)+‖∫ s in 0..r,X s*H s‖)+‖c‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ 2*K^2+2*b*C*K^2+q := by linarith [hp r hr,hp 0 ⟨le_rfl,hb⟩]

end Asakura.Chapter10

import Chapter12ScalarVectorPolynomialStability

namespace Asakura.Chapter12
set_option maxHeartbeats 2000000

theorem scalar_vector_value_stability {H:Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f g:ℝ) (U V:H) (K R δ:ℝ) (a:ℕ) (hK:0≤K) (hR:0≤R) (hδ:0≤δ)
    (hB:∀x:ℝ×H,‖iteratedFDeriv ℝ 1 (fun y:ℝ×H => y.1 • y.2) x‖≤K*(1+‖x‖)^a)
    (hz:1+‖f‖+‖g‖+‖U‖+‖V‖≤R) (hzd:‖f-g‖+‖U-V‖≤δ) :
    ‖f • U-g • V‖≤K*R^a*δ := by
  have hm := polynomial_derivative_difference (fun y:ℝ×H => y.1 • y.2)
    (scalar_vector_map_smooth H) 0 a K hK hB (f,U) (g,V)
  simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,←map_sub,LinearIsometryEquiv.norm_map] at hm
  have h1 : ‖(f,U)‖≤‖f‖+‖U‖ := max_le (by linarith [norm_nonneg U]) (by linarith [norm_nonneg f])
  have h2 : ‖(g,V)‖≤‖g‖+‖V‖ := max_le (by linarith [norm_nonneg V]) (by linarith [norm_nonneg g])
  have h3 : ‖(f,U)-(g,V)‖≤δ := by
    change max ‖f-g‖ ‖U-V‖≤δ
    exact (max_le (by linarith [norm_nonneg (U-V)]) (by linarith [norm_nonneg (f-g)]) :
      max ‖f-g‖ ‖U-V‖≤‖f-g‖+‖U-V‖).trans hzd
  apply hm.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) a) hK)
    h3 (norm_nonneg _) (mul_nonneg hK (pow_nonneg hR a))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_vector_value_stability

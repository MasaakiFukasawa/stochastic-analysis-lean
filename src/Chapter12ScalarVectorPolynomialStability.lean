import Chapter12JointDerivativeArray
import Chapter12CompositionPolynomialStability
import Chapter12ScalarVectorMapGrowth

open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem scalar_vector_polynomial_stability {N G H:Type*} [Fintype N]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f g:G → ℝ) (U V:G → H) (hf:ContDiff ℝ ∞ f) (hg:ContDiff ℝ ∞ g)
    (hU:ContDiff ℝ ∞ U) (hV:ContDiff ℝ ∞ V)
    (k:ℕ) (hk:0<k) (z:G) (e:N → G) (K R δ:ℝ) (a:ℕ)
    (hK:0≤K) (hR:1≤R) (hδ:0≤δ)
    (hB:∀j,0<j → j≤k+1 → ∀x:ℝ×H,
      ‖iteratedFDeriv ℝ j (fun y:ℝ×H => y.1 • y.2) x‖≤K*(1+‖x‖)^a)
    (hz:1+‖f z‖+‖g z‖+‖U z‖+‖V z‖≤R)
    (hzd:‖f z-g z‖+‖U z-V z‖≤δ)
    (hj:∀j,0<j → j≤k →
      Real.sqrt (∑b:Fin j → N,‖iteratedFDeriv ℝ j f z (e ∘ b)‖^2)+
      Real.sqrt (∑b:Fin j → N,‖iteratedFDeriv ℝ j g z (e ∘ b)‖^2)+
      Real.sqrt (∑b:Fin j → N,‖iteratedFDeriv ℝ j U z (e ∘ b)‖^2)+
      Real.sqrt (∑b:Fin j → N,‖iteratedFDeriv ℝ j V z (e ∘ b)‖^2)≤R)
    (hjd:∀j,0<j → j≤k →
      Real.sqrt (∑b:Fin j → N,‖iteratedFDeriv ℝ j f z (e ∘ b)-iteratedFDeriv ℝ j g z (e ∘ b)‖^2)+
      Real.sqrt (∑b:Fin j → N,‖iteratedFDeriv ℝ j U z (e ∘ b)-iteratedFDeriv ℝ j V z (e ∘ b)‖^2)≤δ) :
    Real.sqrt (∑b:Fin k → N,‖iteratedFDeriv ℝ k (fun x => f x • U x) z (e ∘ b)-
      iteratedFDeriv ℝ k (fun x => g x • V x) z (e ∘ b)‖^2)≤
      ((Fintype.card (OrderedFinpartition k):ℝ)*K*(k+1))*R^(a+k)*δ := by
  apply composition_polynomial_stability (fun x => (f x,U x)) (fun x => (g x,V x))
    (fun y:ℝ×H => y.1 • y.2) (hf.prodMk hU) (hg.prodMk hV) (scalar_vector_map_smooth H)
    k hk z e K R δ a hK hR hδ hB
  · have hh1 : ‖(f z,U z)‖≤‖f z‖+‖U z‖ := max_le (by linarith [norm_nonneg (U z)]) (by linarith [norm_nonneg (f z)])
    have hh2 : ‖(g z,V z)‖≤‖g z‖+‖V z‖ := max_le (by linarith [norm_nonneg (V z)]) (by linarith [norm_nonneg (g z)])
    linarith
  · have hh : ‖(f z,U z)-(g z,V z)‖≤‖f z-g z‖+‖U z-V z‖ := by
      change max ‖f z-g z‖ ‖U z-V z‖≤_
      exact max_le (by linarith [norm_nonneg (U z-V z)]) (by linarith [norm_nonneg (f z-g z)])
    exact hh.trans hzd
  · intro j hpos hjk
    apply (joint_derivative_array_bound f U hf hU j z e).trans
    have hh := hj j hpos hjk
    linarith [Real.sqrt_nonneg (∑b:Fin j → N,‖iteratedFDeriv ℝ j g z (e ∘ b)‖^2),
      Real.sqrt_nonneg (∑b:Fin j → N,‖iteratedFDeriv ℝ j V z (e ∘ b)‖^2)]
  · intro j hpos hjk
    apply (joint_derivative_array_bound g V hg hV j z e).trans
    have hh := hj j hpos hjk
    linarith [Real.sqrt_nonneg (∑b:Fin j → N,‖iteratedFDeriv ℝ j f z (e ∘ b)‖^2),
      Real.sqrt_nonneg (∑b:Fin j → N,‖iteratedFDeriv ℝ j U z (e ∘ b)‖^2)]
  · intro j hpos hjk
    exact (joint_derivative_array_difference_bound f g U V hf hg hU hV j z e).trans (hjd j hpos hjk)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_vector_polynomial_stability

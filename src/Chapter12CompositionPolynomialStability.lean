import Chapter12PartitionPolynomialBound
import Chapter12PolynomialDerivativeDifference

open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem composition_polynomial_stability {N G E F : Type*} [Fintype N]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f g : G → E) (b : E → F)
    (hsf : ContDiff ℝ ∞ f) (hsg : ContDiff ℝ ∞ g) (hsb : ContDiff ℝ ∞ b)
    (k : ℕ) (hk : 0<k) (z : G) (e : N → G)
    (K R δ : ℝ) (a : ℕ) (hK : 0≤K) (hR : 1≤R) (hδ : 0≤δ)
    (hb : ∀j:ℕ,0<j → j≤k+1 → ∀x,‖iteratedFDeriv ℝ j b x‖≤K*(1+‖x‖)^a)
    (hfg0 : 1+‖f z‖+‖g z‖≤R) (hδ0 : ‖f z-g z‖≤δ)
    (hf : ∀j:ℕ,0<j → j≤k → Real.sqrt (∑u : Fin j → N,‖iteratedFDeriv ℝ j f z (e ∘ u)‖^2)≤R)
    (hg : ∀j:ℕ,0<j → j≤k → Real.sqrt (∑u : Fin j → N,‖iteratedFDeriv ℝ j g z (e ∘ u)‖^2)≤R)
    (hfg : ∀j:ℕ,0<j → j≤k → Real.sqrt (∑u : Fin j → N,
      ‖iteratedFDeriv ℝ j f z (e ∘ u)-iteratedFDeriv ℝ j g z (e ∘ u)‖^2)≤δ) :
    Real.sqrt (∑u : Fin k → N,
      ‖iteratedFDeriv ℝ k (b ∘ f) z (e ∘ u)-iteratedFDeriv ℝ k (b ∘ g) z (e ∘ u)‖^2)≤
      ((Fintype.card (OrderedFinpartition k):ℝ)*K*(k+1))*R^(a+k)*δ := by
  have hR0 : 0≤R := zero_le_one.trans hR
  have hB : 0≤K*R^a := mul_nonneg hK (pow_nonneg hR0 _)
  have hbg j (hj : 0<j) (hjk : j≤k) : ‖iteratedFDeriv ℝ j b (g z)‖≤K*R^a := by
    apply (hb j hj (by omega) (g z)).trans
    apply mul_le_mul_of_nonneg_left _ hK
    exact pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg (f z)]) a
  have hbd j (hj : 0<j) (hjk : j≤k) :
      ‖iteratedFDeriv ℝ j b (f z)-iteratedFDeriv ℝ j b (g z)‖≤(K*R^a)*δ := by
    have hh := polynomial_derivative_difference b hsb j a K hK (hb (j+1) (by omega) (by omega)) (f z) (g z)
    apply hh.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hfg0 a) hK)
      hδ0 (norm_nonneg _) hB
  have hc := composition_hilbert_stability f g b hsf hsg hsb k hk z e
    (fun _ => K*R^a) (fun _ => K*R^a) (fun _ => R) (fun _ => 1)
    (fun _ => hB) (fun _ => hB) (fun _ => hR0) (fun _ => zero_le_one) δ hδ
    hbg hbd hf hg (fun j hj hjk => by simpa only [one_mul] using hfg j hj hjk)
  apply hc.trans
  apply (mul_le_mul_of_nonneg_left (partition_polynomial_bound k R (K*R^a) hR hB) hδ).trans_eq
  rw [pow_add]
  ring
end Asakura.Chapter12
#print axioms Asakura.Chapter12.composition_polynomial_stability

import Chapter8ActualTimeAverageAlmostSure
import Chapter8ActualSynchronousContraction

open MeasureTheory Set Filter
open scoped NNReal BigOperators Topology RealInnerProductSpace
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's time-average theorem for actual Langevin SDEs:
L2 error for every Lipschitz observable, and almost-sure convergence for
bounded observables, both stationary and from every deterministic start. -/
theorem langevin_time_average_manuscript {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E)
    (g : (Fin d → ℝ) → (Fin d → ℝ)) (hg : Continuous g) (σ : Fin d → Fin n → ℝ)
    (L : ℝ) (hL : 0≤L)
    (hLip : ∀ x y,(∑ i,(g x i-g y i)^2)≤L*∑ i,(x i-y i)^2)
    (κ : ℝ) (hκ : 0<κ)
    (hmono : ∀ x y,κ*‖e x-e y‖^2≤⟪e x-e y,e (g x)-e (g y)⟫)
    (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π]
    (hπ : MemLp (fun x : Fin d → ℝ => x) 2 π)
    (ξ : Ω → Fin d → ℝ) (hξ : MemLp ξ 2 P) (hξlaw : P.map ξ=π)
    (X : HalfClosedTime → Ω → Fin d → ℝ)
    (hX : VectorSDESolution P B.F B.W (fun i x => -(g x i)) (fun i j _ => σ i j) ξ X)
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W (fun i x => -(g x i)) (fun i j _ => σ i j) (fun _ => x) (Z x))
    (hinv : ∀ t : ℝ,0≤t → ∀ f : (Fin d → ℝ) → ℝ,
      ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      (∫ x,(∫ w,f (Z x (realTimeClamp t) w) ∂P) ∂π)=∫ x,f x ∂π)
    (f : E → ℝ) (Lf : ℝ≥0) (hf : LipschitzWith Lf f) :
    (∀ T : ℝ,0<T →
      (∫ w,(timeAverage (fun t => f (e (X (realTimeClamp (max 0 t)) w))) T-
        (∫ x,f (e x) ∂π))^2 ∂P)≤2*(Lf:ℝ)^2*(∫ x,‖e x‖^2 ∂π)/(κ*T)) ∧
    (∀ K : ℝ,(∀ x,‖f x‖≤K) →
      (∀ᵐ w ∂P,Tendsto (timeAverage (fun t => f (e (X (realTimeClamp (max 0 t)) w))))
        atTop (nhds (∫ x,f (e x) ∂π))) ∧
      ∀ x : Fin d → ℝ,∀ Y : HalfClosedTime → Ω → Fin d → ℝ,
        VectorSDESolution P B.F B.W (fun i z => -(g z i)) (fun i j _ => σ i j) (fun _ => x) Y →
        ∀ᵐ w ∂P,Tendsto (timeAverage (fun t => f (e (Y (realTimeClamp (max 0 t)) w))))
          atTop (nhds (∫ z,f (e z) ∂π))) := by
  let b := fun i x => -(g x i)
  let a := fun i j (_ : Fin d → ℝ) => σ i j
  have hLp x y : (∑ i,(b i x-b i y)^2)+(∑ i,∑ j,(a i j x-a i j y)^2)≤L*∑ i,(x i-y i)^2 := by
    simpa only [b,a,neg_sub_neg,sub_self,zero_pow (by norm_num : (2:ℕ)≠0),
      Finset.sum_const_zero,add_zero,sub_sq_comm] using hLip x y
  have hCon t (ht : 0≤t) x y : ∀ᵐ w ∂P,
      ‖e (Z x (realTimeClamp t) w)-e (Z y (realTimeClamp t) w)‖≤Real.exp (-κ*t)*‖e x-e y‖ := by
    filter_upwards [actual_synchronous_contraction P B e g hg σ κ hmono
      (fun _ => x) (fun _ => y) (Z x) (Z y) (hZ x) (hZ y)] with w hw
    exact hw t ht
  constructor
  · intro T hT
    exact actual_stationary_time_average P B e L hL b a hLp π hπ ξ hξ hξlaw X hX Z hZ hinv
      κ T hκ hT hCon f Lf hf
  · intro K hK
    have hstat := actual_stationary_time_average_ae P B e L hL b a hLp π hπ ξ hξ hξlaw
      X hX Z hZ hinv κ hκ hCon f Lf hf K hK
    refine ⟨hstat,?_⟩
    intro x Y hY
    have hcX := (sde_real_path_data P B L hL b a hLp ξ hξ X hX).1
    have hcY := (sde_real_path_data P B L hL b a hLp (fun _ => x) (memLp_const _) Y hY).1
    filter_upwards [hstat,actual_synchronous_contraction P B e g hg σ κ hmono
      (fun _ => x) ξ Y X hY hX] with w hstatw hw
    apply time_average_coupling_transfer
      (fun t => f (e (Y (realTimeClamp (max 0 t)) w)))
      (fun t => f (e (X (realTimeClamp (max 0 t)) w)))
      (hf.continuous.comp (e.continuous.comp (hcY w)))
      (hf.continuous.comp (e.continuous.comp (hcX w)))
      ((Lf:ℝ)*‖e x-e (ξ w)‖) κ (∫ z,f (e z) ∂π) (by positivity) hκ _ hstatw
    intro t ht
    have h := hf.norm_sub_le (e (Y (realTimeClamp t) w)) (e (X (realTimeClamp t) w))
    rw [Real.norm_eq_abs] at h
    have hh := h.trans (mul_le_mul_of_nonneg_left (hw t ht) Lf.coe_nonneg)
    simpa only [max_eq_right ht,mul_comm,mul_left_comm,mul_assoc] using hh

end Asakura.Chapter8

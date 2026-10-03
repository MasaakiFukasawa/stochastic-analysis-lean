import Chapter12ForcingVariationalOperator
import Chapter8ForcedPathStability
import Mathlib.Analysis.Calculus.MeanValue

open Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Finite forcing parameters produce differentiable solution maps with
uniformly bounded first derivatives; both the solution and derivative are
constructed from the drift assumptions. -/
theorem finite_forcing_flow_first_derivative {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : E → E) (D : E → E →L[ℝ] E) (hD : ∀ z,HasFDerivAt b (D z) z)
    (K L : ℝ≥0) (hK : LipschitzWith K D) (hL : 0<L) (hDb : ∀ z,‖D z‖≤(L:ℝ))
    (W : ℝ → E) (hcW : Continuous W) (R : ℝ → F →L[ℝ] E) (hcR : Continuous R)
    (x₀ : E) (T : ℝ) (hT : 0≤T) :
    ∃ (X : F → ℝ → E) (C : ℝ),0≤C ∧
      (∀ z,Continuous (X z)) ∧
      (∀ z t,t∈Icc 0 T → X z t=x₀+(∫ s in 0..t,b (X z s))+W t+R t z) ∧
      (∀ z y t,t∈Icc 0 T → ‖X z t-X y t‖≤C*‖z-y‖) ∧
      ∀ z,∃ J : ℝ → F →L[ℝ] E,Continuous J ∧
        (∀ t,t∈Icc 0 T → ∀ h,J t h=R t h+∫ s in 0..t,D (X z s) (J s h)) ∧
        (∀ t,t∈Icc 0 T → HasFDerivAt (fun y => X y t) (J t) z) ∧
        ∀ t,t∈Icc 0 T → ‖J t‖≤C := by
  have hLb : LipschitzWith L b := by
    apply lipschitzWith_of_nnnorm_fderiv_le (fun z => (hD z).differentiableAt)
    intro z
    rw [(hD z).fderiv]
    exact_mod_cast hDb z
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).exists_bound_of_continuousOn hcR.continuousOn
  have hM0 : 0≤M := (norm_nonneg _).trans (hM 0 ⟨le_rfl,hT⟩)
  have hex (z : F) := Asakura.Chapter8.forced_integral_equation_exists T hT L
    (fun _ y => b y) (hLb.continuous.comp continuous_snd) (fun _ => hLb)
    (fun t => x₀+W t+R t z) ((continuous_const.add hcW).add (hcR.clm_apply continuous_const))
  choose X hcX hXe using hex
  have hX z t (ht : t∈Icc 0 T) : X z t=x₀+(∫ s in 0..t,b (X z s))+W t+R t z := by
    rw [hXe z t ht]
    abel
  let C := Real.exp (((L:ℝ)+1)*T)*M
  have hC : 0≤C := mul_nonneg (Real.exp_pos _).le hM0
  have hLip z y t (ht : t∈Icc 0 T) : ‖X z t-X y t‖≤C*‖z-y‖ := by
    have he := Asakura.Chapter8.forced_path_stability b L hLb (X z) (X y)
      (fun s => W s+R s z) (fun s => W s+R s y) (hcX z) (hcX y)
      x₀ x₀ T (M*‖z-y‖) hT (mul_nonneg hM0 (norm_nonneg _))
      (fun s hs => ?_) (fun s hs => by rw [hX z s hs]; abel)
      (fun s hs => by rw [hX y s hs]; abel) t ht
    · simpa only [sub_self,norm_zero,zero_add,C,mul_assoc] using he
    · have heq : (W s+R s z)-(W s+R s y)=R s (z-y) := by rw [map_sub]; abel
      rw [heq]
      exact ((R s).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hM s hs) (norm_nonneg _))
  refine ⟨X,C,hC,hcX,hX,hLip,?_⟩
  intro z
  obtain ⟨J,hcJ,hJ,hdJ⟩ := forcing_parameter_derivative_constructed b D hD K L hK hL hDb
    X W R hcR x₀ hcX z T C hT hC hX
    (fun h s hs => by simpa only [add_sub_cancel_left] using hLip (z+h) z s hs)
  refine ⟨J,hcJ,hJ,hdJ,?_⟩
  intro t ht
  apply (hdJ t ht).le_of_lipschitz (C := ⟨C,hC⟩)
  apply LipschitzWith.of_dist_le_mul
  intro y v
  change dist (X y t) (X v t)≤C*dist y v
  simpa only [dist_eq_norm] using hLip y v t ht

end Asakura.Chapter12

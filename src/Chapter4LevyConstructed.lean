import Chapter4HarmonicConditional
import Chapter4LevyCalculus
import Chapter4ConditionalTrig

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

lemma conditional_remove_nonzero_weight {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G : MeasurableSpace Ω) (f g : Ω → ℝ) (a b : ℝ) (ha : a≠0)
    (h : P[(fun w => a*f w) | G] =ᵐ[P] fun w => b*g w) :
    P[f | G] =ᵐ[P] fun w => b/a*g w := by
  have hc := condExp_smul (μ := P) a f G
  simp only [Pi.smul_def,smul_eq_mul] at hc
  filter_upwards [h,hc] with w hw hc
  have he : a*P[f | G] w=b*g w := hc.symm.trans hw
  apply (mul_left_cancel₀ ha)
  rw [he]
  field_simp

/-- The missing Ito-to-characteristic-function connection in the
Brownian characterization exercise, on any finite preterminal interval. -/
theorem levy_conditional_characteristic_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (s : ℝ) (hs : s∈Icc 0 R) (u : ℝ) :
    P[(fun w => Complex.exp ((u:ℂ)*((W (realTimeClamp R) w-W (realTimeClamp s) w):ℂ)*Complex.I)) |
      F (realTimeClamp s)] =ᵐ[P] fun _ => Complex.exp (-((R-s:ℝ):ℂ)*(u:ℂ)^2/2) := by
  let K := Real.exp (u^2*R/2)
  have hcos := harmonic_conditional_from_ito P hT F hF hle hnull W A hW hA hclock R hR hRT
    (levyCos u) (levyCos_smooth u) (fun r _ x => levyCos_harmonic u r x)
    K (|u| * K) (by dsimp [K]; positivity) (fun r hr x => levyCos_bound u R r x hr.2)
    (by intro r hr x; rw [levyCos_fderiv_space,abs_mul,abs_neg];
        exact mul_le_mul_of_nonneg_left (levySin_bound u R r x hr.2) (abs_nonneg u)) s hs
  have hsin := harmonic_conditional_from_ito P hT F hF hle hnull W A hW hA hclock R hR hRT
    (levySin u) (levySin_smooth u) (fun r _ x => levySin_harmonic u r x)
    K (|u| * K) (by dsimp [K]; positivity) (fun r hr x => levySin_bound u R r x hr.2)
    (by intro r hr x; rw [levySin_fderiv_space,abs_mul];
        exact mul_le_mul_of_nonneg_left (levyCos_bound u R r x hr.2) (abs_nonneg u)) s hs
  simp only [levyCos,levySin,Matrix.cons_val_zero,Matrix.cons_val_one] at hcos hsin
  have hc := conditional_remove_nonzero_weight P (F (realTimeClamp s))
    (fun w => Real.cos (u*W (realTimeClamp R) w)) (fun w => Real.cos (u*W (realTimeClamp s) w))
    K (Real.exp (u^2*s/2)) (Real.exp_ne_zero _) hcos
  have hi := conditional_remove_nonzero_weight P (F (realTimeClamp s))
    (fun w => Real.sin (u*W (realTimeClamp R) w)) (fun w => Real.sin (u*W (realTimeClamp s) w))
    K (Real.exp (u^2*s/2)) (Real.exp_ne_zero _) hsin
  have hRt : realTimeClamp (T := T) R<⊤ := by
    change (realTimeClamp R:EReal)<T
    rw [real_time_clamp_eq R hR hRT.le]; exact hRT
  have hst : realTimeClamp (T := T) s<⊤ := (real_time_clamp_mono hs.2).trans_lt hRt
  have hXm := (hW.adapted P F _ hst).const_mul u
  have hYm := ((hW.adapted P F _ hRt).mono (hle _) le_rfl).const_mul u
  have ht := conditional_trig_increment P (F (realTimeClamp s)) (hle _)
    (fun w => u*W (realTimeClamp s) w) (fun w => u*W (realTimeClamp R) w)
    hXm hYm (Real.exp (u^2*s/2)/K) hc hi
  have hz := conditional_characteristic_from_trig P (F (realTimeClamp s))
    (fun w => u*W (realTimeClamp R) w-u*W (realTimeClamp s) w)
    (hYm.sub (hXm.mono (hle _) le_rfl)) (Real.exp (u^2*s/2)/K) ht.1 ht.2
  have hq : Real.exp (u^2*s/2)/K=Real.exp (-(R-s)*u^2/2) := by
    dsimp [K]
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hq] at hz
  convert hz using 1
  · congr 1
    funext w
    congr 1
    push_cast
    ring
  · funext w
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring

theorem levy_gaussian_increment_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (s : ℝ) (hs : s∈Icc 0 R) :
    HasLaw (fun w => W (realTimeClamp R) w-W (realTimeClamp s) w)
      (gaussianReal 0 ⟨R-s,sub_nonneg.mpr hs.2⟩) P ∧
    Indep (MeasurableSpace.comap (fun w => W (realTimeClamp R) w-W (realTimeClamp s) w) inferInstance)
      (F (realTimeClamp s)) P := by
  have hRt : realTimeClamp (T := T) R<⊤ := by
    change (realTimeClamp R:EReal)<T
    rw [real_time_clamp_eq R hR hRT.le]; exact hRT
  have hst : realTimeClamp (T := T) s<⊤ := (real_time_clamp_mono hs.2).trans_lt hRt
  apply gaussian_independent_of_conditional_characteristic P (F (realTimeClamp s)) (hle _)
    _ (((hW.adapted P F _ hRt).mono (hle _) le_rfl).sub ((hW.adapted P F _ hst).mono (hle _) le_rfl))
    ⟨R-s,sub_nonneg.mpr hs.2⟩
  intro u
  convert levy_conditional_characteristic_constructed P hT F hF hle hnull W A hW hA hclock R hR hRT s hs u using 1
  all_goals simp only [Pi.sub_apply,Complex.ofReal_sub]
  funext w
  congr 2
  norm_cast


end Asakura.Chapter4

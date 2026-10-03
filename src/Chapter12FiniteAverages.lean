import Chapter12TensorContraction
import Chapter12HigherChainPartitions

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

noncomputable def finiteAverage {N : ℕ} (f : Fin (N+1) → ℝ) : ℝ :=
  (∑ i,f i)/(N+1)

theorem finiteAverage_nonneg {N : ℕ} (f : Fin (N+1) → ℝ) (h : ∀ i,0≤f i) :
    0≤finiteAverage f := div_nonneg (Finset.sum_nonneg (fun i _ => h i)) (by positivity)

theorem finiteAverage_mono {N : ℕ} (f g : Fin (N+1) → ℝ) (h : ∀ i,f i≤g i) :
    finiteAverage f≤finiteAverage g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => h i)) (by positivity)

@[simp] theorem finiteAverage_const {N : ℕ} (c : ℝ) : finiteAverage (fun _ : Fin (N+1) => c)=c := by
  simp [finiteAverage,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  field_simp

theorem finiteAverage_add {N : ℕ} (f g : Fin (N+1) → ℝ) :
    finiteAverage (fun i => f i+g i)=finiteAverage f+finiteAverage g := by
  simp [finiteAverage,Finset.sum_add_distrib,add_div]

theorem finiteAverage_mul_const {N : ℕ} (f : Fin (N+1) → ℝ) (c : ℝ) :
    finiteAverage (fun i => f i*c)=finiteAverage f*c := by
  simp only [finiteAverage,← Finset.sum_mul]
  ring

theorem finiteAverage_const_mul {N : ℕ} (f : Fin (N+1) → ℝ) (c : ℝ) :
    finiteAverage (fun i => c*f i)=c*finiteAverage f := by
  simp only [finiteAverage,← Finset.mul_sum]
  ring

theorem finiteAverage_cauchy_schwarz {N : ℕ} (f g : Fin (N+1) → ℝ) :
    finiteAverage (fun i => f i*g i)≤
      Real.sqrt (finiteAverage (fun i => f i^2))*Real.sqrt (finiteAverage (fun i => g i^2)) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hs : (finiteAverage (fun i => f i*g i))^2≤
      finiteAverage (fun i => f i^2)*finiteAverage (fun i => g i^2) := by
    unfold finiteAverage
    calc
      _=(∑ i,f i*g i)^2/((N+1:ℝ)^2) := by rw [div_pow]
      _≤((∑ i,f i^2)*(∑ i,g i^2))/((N+1:ℝ)^2) := div_le_div_of_nonneg_right h (by positivity)
      _=_ := by rw [div_mul_div_comm,pow_two]
  have hf := finiteAverage_nonneg (fun i => f i^2) (fun i => sq_nonneg _)
  have hg := finiteAverage_nonneg (fun i => g i^2) (fun i => sq_nonneg _)
  have hsq : (Real.sqrt (finiteAverage (fun i => f i^2))*Real.sqrt (finiteAverage (fun i => g i^2)))^2=
      finiteAverage (fun i => f i^2)*finiteAverage (fun i => g i^2) := by
    rw [mul_pow,Real.sq_sqrt hf,Real.sq_sqrt hg]
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rwa [hsq]

noncomputable def cubeAverage (N : ℕ) : (e : ℕ) → ((Fin e → Fin (N+1)) → ℝ) → ℝ
  | 0,f => f Fin.elim0
  | e+1,f => cubeAverage N e (fun a => finiteAverage (fun i => f (Fin.snoc a i)))

theorem cubeAverage_nonneg (N e : ℕ) (f : (Fin e → Fin (N+1)) → ℝ) (hf : ∀ a,0≤f a) :
    0≤cubeAverage N e f := by
  induction e with
  | zero => exact hf _
  | succ e ih => exact ih _ (fun a => finiteAverage_nonneg _ (fun i => hf _))

theorem cubeAverage_mono (N e : ℕ) (f g : (Fin e → Fin (N+1)) → ℝ) (h : ∀ a,f a≤g a) :
    cubeAverage N e f≤cubeAverage N e g := by
  induction e with
  | zero => exact h _
  | succ e ih => exact ih _ _ (fun a => finiteAverage_mono _ _ (fun i => h _))

@[simp] theorem cubeAverage_const (N e : ℕ) (c : ℝ) : cubeAverage N e (fun _ => c)=c := by
  induction e with
  | zero => rfl
  | succ e ih => simpa only [cubeAverage,finiteAverage_const] using ih

end Asakura.Chapter12

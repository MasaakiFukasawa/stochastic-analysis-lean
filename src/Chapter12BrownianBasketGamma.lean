import Chapter12BrownianBasketGreeks
open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem brownian_basket_gamma {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : BrownianSystem P (d+1)) (T : ℝ) (hT : 0<T)
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (hA : A.det≠0) (x b : Fin (d+1) → ℝ)
    (i j : Fin (d+1)) (hxi : 0<x i) (hxj : 0<x j)
    (h : (Fin (d+1) → ℝ) → ℝ) (hm : Measurable h)
    (C : ℝ) (n : ℕ) (hb : ∀ s,|h s|≤C*(1+‖s‖^n)) :
    let Z := fun w a => B.W a (realTimeClamp T) w/Real.sqrt T
    HasDerivAt
      (fun u : ℝ => (∫ z,h (fun k => (if k=j then u else x k)*Real.exp (b k+∑ a,A k a*Z z a))*
        (∑ a,(A⁻¹) a i*Z z a) ∂P)/(if i=j then u else x i))
      (∫ z,h (fun k => x k*Real.exp (b k+∑ a,A k a*Z z a))*
        (((∑ a,(A⁻¹) a i*Z z a)*(∑ a,(A⁻¹) a j*Z z a)-(∑ a,(A⁻¹) a i*(A⁻¹) a j)-
          (if i=j then ∑ a,(A⁻¹) a i*Z z a else 0))/(x i*x j))
        ∂P) (x j) := by
  classical
  dsimp only
  let μ := Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)
  let Z := fun w a => B.W a (realTimeClamp T) w/Real.sqrt T
  have hZ := actual_brownian_normalized_terminal_law P B T hT
  have he (u : ℝ) :
      (∫ w,h (fun k => (if k=j then u else x k)*Real.exp (b k+∑ a,A k a*Z w a))*
        (∑ a,(A⁻¹) a i*Z w a) ∂P)=
      ∫ z,h (fun k => (if k=j then u else x k)*Real.exp (b k+∑ a,A k a*z a))*
        (∑ a,(A⁻¹) a i*z a) ∂μ :=
    hZ.integral_comp (f := fun z => h (fun k => (if k=j then u else x k)*Real.exp (b k+∑ a,A k a*z a))*
        (∑ a,(A⁻¹) a i*z a)) ((hm.comp (by fun_prop)).mul (by (try split_ifs) <;> fun_prop)).aestronglyMeasurable
  have hg :
      (∫ w,h (fun k => x k*Real.exp (b k+∑ a,A k a*Z w a))*
        (((∑ a,(A⁻¹) a i*Z w a)*(∑ a,(A⁻¹) a j*Z w a)-(∑ a,(A⁻¹) a i*(A⁻¹) a j)-
          (if i=j then ∑ a,(A⁻¹) a i*Z w a else 0))/(x i*x j)) ∂P)=
      ∫ z,h (fun k => x k*Real.exp (b k+∑ a,A k a*z a))*
        (((∑ a,(A⁻¹) a i*z a)*(∑ a,(A⁻¹) a j*z a)-(∑ a,(A⁻¹) a i*(A⁻¹) a j)-
          (if i=j then ∑ a,(A⁻¹) a i*z a else 0))/(x i*x j)) ∂μ :=
    hZ.integral_comp (f := fun z => h (fun k => x k*Real.exp (b k+∑ a,A k a*z a))*
        (((∑ a,(A⁻¹) a i*z a)*(∑ a,(A⁻¹) a j*z a)-(∑ a,(A⁻¹) a i*(A⁻¹) a j)-
          (if i=j then ∑ a,(A⁻¹) a i*z a else 0))/(x i*x j)))
      ((hm.comp (by fun_prop)).mul (by (try split_ifs) <;> fun_prop)).aestronglyMeasurable
  convert basket_measurable_gamma A hA x b i j hxi hxj h hm C n hb using 1
  · funext u
    rw [he]

end Asakura.Chapter12

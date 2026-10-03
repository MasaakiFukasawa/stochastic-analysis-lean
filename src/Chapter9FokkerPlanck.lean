import Chapter9DirectionalJets
import Chapter9MixtureJets

open Set Finset MeasureTheory
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

theorem ou_kernel_forward_pde {d : ℕ} (x y : Fin d → ℝ) (t : ℝ) (ht : 0<t) :
    let k := fun q => Real.exp (ouExponent x q)
    iteratedFDeriv ℝ 1 k (t,y) (fun _ => (1,0)) =
      (∑ i,iteratedFDeriv ℝ 2 k (t,y) (fun _ => (0,Pi.single i 1)))+
      (d:ℝ)*k (t,y)+
      ∑ i,y i*iteratedFDeriv ℝ 1 k (t,y) (fun _ => (0,Pi.single i 1)) := by
  dsimp only
  let a := Real.exp (-t)
  let v := 1-Real.exp (-2*t)
  let k := gaussianKernel a v x y
  have h1 (i : Fin d) : iteratedFDeriv ℝ 1 (fun q => Real.exp (ouExponent x q)) (t,y)
      (fun _ => (0,Pi.single i 1)) = (-(y i-a*x i)/v)*k := by
    simpa [a,v,k,Pi.single_apply,mul_ite,ite_mul] using ou_kernel_spatial_first_jet x y (Pi.single i 1) t ht
  have h2 (i : Fin d) : iteratedFDeriv ℝ 2 (fun q => Real.exp (ouExponent x q)) (t,y)
      (fun _ => (0,Pi.single i 1)) = ((y i-a*x i)^2/v^2-1/v)*k := by
    simpa [a,v,k,Pi.single_apply,mul_ite,ite_mul] using ou_kernel_spatial_second_jet x y (Pi.single i 1) t ht
  simp_rw [h1,h2]
  rw [ou_kernel_time_jet x y t ht]
  have hav : a^2+v=1 := by
    dsimp [a,v]
    rw [pow_two,←Real.exp_add,show -t + -t = -2*t by ring]
    ring
  change (a^2*((∑ i,(y i-a*x i)^2)/v^2-(d:ℝ)/v)-
      a*(∑ i,x i*(y i-a*x i))/v)*k = _
  rw [gaussian_forward_backward_algebra a v k (ou_variance_positive t ht).ne' hav x y]
  change (((∑ i,(y i-a*x i)^2)/v^2-(d:ℝ)/v)+(d:ℝ)-
      (∑ i,y i*(y i-a*x i))/v)*k =
      (∑ i,((y i-a*x i)^2/v^2-1/v)*k)+(d:ℝ)*k+∑ i,y i*((-(y i-a*x i)/v)*k)
  have hs : (∑ i,((y i-a*x i)^2/v^2-1/v)*k)=
      ((∑ i,(y i-a*x i)^2)/v^2-(d:ℝ)/v)*k := by
    rw [←sum_mul,sum_sub_distrib,←sum_div,sum_const]
    simp only [card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hb : (∑ i,y i*((-(y i-a*x i)/v)*k))= -(∑ i,y i*(y i-a*x i))/v*k := by
    calc
      _ = ∑ i,(-(y i*(y i-a*x i))/v)*k := by
        apply sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [←sum_mul,←sum_div,←sum_neg_distrib]
  rw [hs,hb]
  ring

/-- The Fokker--Planck equation for the actual OU mixture density. The
first jet in the time direction is its time derivative; the sum of second
spatial jets is its Laplacian, and the last two terms are div(y p). -/
theorem ou_mixture_fokker_planck {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    (t : ℝ) (ht : 0<t) (y : Fin d → ℝ) :
    let p := fun q => ∫ x,Real.exp (ouExponent x q) ∂μ
    iteratedFDeriv ℝ 1 p (t,y) (fun _ => (1,0)) =
      (∑ i,iteratedFDeriv ℝ 2 p (t,y) (fun _ => (0,Pi.single i 1)))+
      (d:ℝ)*p (t,y)+
      ∑ i,y i*iteratedFDeriv ℝ 1 p (t,y) (fun _ => (0,Pi.single i 1)) := by
  dsimp only
  simp_rw [ou_mixture_jet_apply μ _ (t,y) ht]
  let k := fun (x : Fin d → ℝ) (q : ℝ × (Fin d → ℝ)) => Real.exp (ouExponent x q)
  have hi n h := ou_kernel_jet_apply_integrable μ n (t,y) ht h
  have h0 : Integrable (fun x => k x (t,y)) μ := by
    simpa only [iteratedFDeriv_zero_apply] using hi 0 (fun i => Fin.elim0 i)
  have h2 : Integrable (fun x => ∑ i : Fin d,iteratedFDeriv ℝ 2 (k x) (t,y)
      (fun _ => (0,Pi.single i 1))) μ := integrable_finsetSum _ (fun i _ => hi 2 _)
  have h1 : Integrable (fun x => ∑ i : Fin d,y i*iteratedFDeriv ℝ 1 (k x) (t,y)
      (fun _ => (0,Pi.single i 1))) μ := integrable_finsetSum _ (fun i _ => (hi 1 _).const_mul (y i))
  calc
    _ = ∫ x,((∑ i : Fin d,iteratedFDeriv ℝ 2 (k x) (t,y) (fun _ => (0,Pi.single i 1)))+
        (d:ℝ)*k x (t,y)+∑ i : Fin d,y i*iteratedFDeriv ℝ 1 (k x) (t,y)
        (fun _ => (0,Pi.single i 1))) ∂μ := integral_congr_ae (ae_of_all _ (fun x => ou_kernel_forward_pde x y t ht))
    _ = _ := by
      have hsplit := integral_add (h2.add (h0.const_mul (d:ℝ))) h1
      dsimp only [Pi.add_apply] at hsplit
      rw [hsplit,integral_add h2 (h0.const_mul (d:ℝ))]
      rw [integral_finsetSum _ (fun i _ => hi 2 _),integral_const_mul,
        integral_finsetSum _ (fun i _ => (hi 1 _).const_mul (y i))]
      simp_rw [integral_const_mul]
      rfl
end Asakura.Chapter9

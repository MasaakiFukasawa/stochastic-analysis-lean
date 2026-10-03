import Chapter4SmallMassStochastic
import Chapter4SmallMassMatrix
import Chapter4MatrixFlowConvolution
import Chapter4LinearSDEConstructed

open MeasureTheory Matrix Set Filter
open scoped Topology ENNReal BigOperators Matrix.Norms.Operator
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 4600000
set_option backward.isDefEq.respectTransparency false

/-- Mean-square mass-zero convergence of the original matrix-exponential
solution. The auxiliary convolutions are identified with that solution
by uniqueness of actual Ito integrals. -/
theorem langevin_matrix_solution_small_mass
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤mΩ)
    (hnull : ∀ t B,MeasurableSet[mΩ] B → P B=0 → MeasurableSet[F t] B)
    (W C : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hC : LocalCovarianceWitness P F W W C)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → C (realTimeClamp r) w=r)
    (κ γ σ R y v : ℝ) (hκ : 0<κ) (hγ : 0<γ) (hR : 0<R) (hRT : (R:EReal)<T)
    (N : ℝ → Fin 2 → ClosedTime T → Ω → ℝ)
    (hN : ∀ m j,LocalMProcessWitness P F (N m j))
    (hNI : ∀ m j,ItoCovarianceFormula P F W
      (fun z => NormedSpace.exp ((-z.2) • (!![0,1;-κ/m,-γ/m] : Matrix (Fin 2) (Fin 2) ℝ)) j 1*(σ/m)) (N m j)) :
    ∃ Z : ClosedTime T → Ω → ℝ,LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F W (fun z => σ/γ*Real.exp (-κ/γ*(R-z.2))) Z ∧
      Tendsto (fun m => ∫ w,((∑ j,NormedSpace.exp (R • (!![0,1;-κ/m,-γ/m] : Matrix (Fin 2) (Fin 2) ℝ)) 0 j*
        (![y,v] j+N m j (realTimeClamp R) w))-
        (Real.exp (-κ/γ*R)*y+Z (realTimeClamp R) w))^2 ∂P)
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
  classical
  let A : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun m => !![0,1;-κ/m,-γ/m]
  let J : ℝ → ClosedTime T → Ω → ℝ := fun m t w => ∑ j,NormedSpace.exp (R • A m) 0 j*N m j t w
  have hJI m := matrix_flow_stochastic_convolution P hT F hF hle hnull W hW (A m)
    (![0,σ/m]) (N m) (hN m) (fun j => by
      simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,mul_zero,zero_add] using hNI m j) R 0
  have hJI' m : ItoCovarianceFormula P F W
      (fun z => NormedSpace.exp ((R-z.2) • A m) 0 1*(σ/m)) (J m) := by
    simpa only [J,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,mul_zero,zero_add] using (hJI m).2
  obtain ⟨K,Z,hK,hZ,hKI,hZI,hlim⟩ := langevin_small_mass_stochastic_limit P hT F hF hle hnull
    W C hW hC hclock κ γ σ R y v hκ hγ hR hRT
  refine ⟨Z,hZ,hZI,?_⟩
  have hD : ∀ᶠ m in 𝓝[>] (0:ℝ),0<γ^2-4*κ*m := by
    have hc : Continuous (fun m : ℝ => γ^2-4*κ*m) := by fun_prop
    have hh := hc.continuousAt (x:=0) |>.eventually (Ioi_mem_nhds (by nlinarith : (0:ℝ)<γ^2-4*κ*0))
    exact hh.filter_mono nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [hD,self_mem_nhdsWithin] with m hDm hm
  have hInt : ItoCovarianceFormula P F W (fun z => langevinKernel κ γ σ m (R-z.2)) (J m) :=
    (hJI' m).congr_on_time_domain P F W (J m) _ _ (fun w r _ _ =>
      (langevin_small_mass_matrix_formula κ γ σ m (R-r) y v hγ hm hDm).2)
  have he := ItoCovarianceFormula.unique P hT F hF hle hnull W (J m) (K m)
    (fun z => langevinKernel κ γ σ m (R-z.2)) hW (hJI m).1 (hK m) hInt (hKI m)
  apply integral_congr_ae
  filter_upwards [he] with w hw
  have hh := hw _ (real_time_below R hR.le hRT)
  have hinit := (langevin_small_mass_matrix_formula κ γ σ m R y v hγ hm hDm).1
  change NormedSpace.exp (R • A m) 0 0*y+NormedSpace.exp (R • A m) 0 1*v=
    langevinInitial κ γ m R y v at hinit
  dsimp only [J] at hh
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] at hh ⊢
  rw [← hh,← hinit]
  ring

end Asakura.Chapter4

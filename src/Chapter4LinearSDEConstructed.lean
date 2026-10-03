import Chapter4LinearFlowAssembly
import Chapter4DeterministicItoProduct

open MeasureTheory Set Filter Matrix
open scoped Topology ENNReal BigOperators Matrix.Norms.Operator
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- The actual stochastic convolution for a constant matrix linear SDE,
including the integral equation at every finite time on one event. -/
theorem linear_sde_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t B,MeasurableSet[m] B → P B=0 → MeasurableSet[F t] B)
    {dim noise : ℕ} (W : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ k,LocalMProcessWitness P F (W k))
    (C : ClosedTime T → Ω → ℝ) (hCa : ∀ t,t<⊤ → Measurable[F t] (C t))
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → C (realTimeClamp r) w=r)
    (A : Matrix (Fin dim) (Fin dim) ℝ) (S : Matrix (Fin dim) (Fin noise) ℝ)
    (y : Fin dim → ℝ) :
    ∃ N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ,
      (∀ j k,LocalMProcessWitness P F (N j k)) ∧
      (∀ j k,ItoCovarianceFormula P F (W k)
        (fun z => (NormedSpace.exp ((-z.2) • A)*S) j k) (N j k)) ∧
      ∀ᵐ w ∂P,∀ d : ℝ,0≤d → (d:EReal)<T → ∀ i,
        (∑ j,NormedSpace.exp (d • A) i j*(y j+∑ k,N j k (realTimeClamp d) w))=y i+
          (∫ r in 0..d,∑ l,A i l*(∑ j,NormedSpace.exp (r • A) l j*
            (y j+∑ k,N j k (realTimeClamp r) w)))+∑ k,S i k*W k (realTimeClamp d) w := by
  classical
  let E : ℝ → Matrix (Fin dim) (Fin dim) ℝ := fun r => NormedSpace.exp (r • A)
  let g : Fin dim → Fin noise → ℝ → ℝ := fun j k r => (E (-r)*S) j k
  have hEc i j : ContDiff ℝ 1 (fun r => E r i j) :=
    (matrix_exp_entry_smooth A i j).of_le (by norm_num)
  have hgc j k : Continuous (g j k) := by
    change Continuous (fun r => ∑ l,E (-r) j l*S l k)
    exact continuous_finset_sum Finset.univ (fun l _ =>
      ((hEc j l).continuous.comp continuous_neg).mul continuous_const)
  have hNIex j k := continuous_adapted_ito_exists P hT F hF hle hnull (W k) (hW k)
    (fun z => g j k z.2) (fun r _ _ => by
      change Measurable[F (realTimeClamp r)] (fun _ : Ω => g j k r)
      exact measurable_const) (fun _ _ _ _ => (hgc j k).continuousOn)
  choose N hN hNI using hNIex
  have hVex i j k := deterministic_ito_product P hT F hF hle hnull (W k) C (N j k)
    (hW k) (hN j k) hCa hclock (g j k) (fun r => E r i j) (hgc j k) (hEc i j) (hNI j k)
  choose V hV hVI hprod using hVex
  have hsumV i k : ∀ᵐ w ∂P,∀ t,t<⊤ → (∑ j,V i j k t w)=S i k*W k t w := by
    have hsumI := finite_ito_sum P hT F hF hle hnull (W k) (hW k) Finset.univ
      (fun j z => E z.2 i j*g j k z.2) (fun j => V i j k) (fun j _ => hVI i j k)
    have hfun : (fun z : Ω × ℝ => ∑ j,E z.2 i j*g j k z.2)=(fun _ => S i k) := by
      funext z
      change (E z.2*(E (-z.2)*S)) i k=S i k
      rw [← Matrix.mul_assoc,matrix_exp_inverse_product A z.2,Matrix.one_mul]
    simp only [hfun] at hsumI
    exact ItoCovarianceFormula.unique P hT F hF hle hnull (W k)
      (fun t w => ∑ j,V i j k t w) (fun t w => S i k*W k t w) (fun _ => S i k)
      (hW k) (local_martingale_finset_sum P hT F hF hle Finset.univ (fun j => V i j k)
        (fun j _ => hV i j k)) ((hW k).smul P F (S i k)) hsumI
      (constant_ito_integral P hT F hF hle hnull (W k) (hW k) (S i k))
  refine ⟨N,hN,hNI,?_⟩
  have hpall : ∀ᵐ w ∂P,∀ i j k,∀ d : ℝ,0≤d → (d:EReal)<T →
      E d i j*N j k (realTimeClamp d) w=V i j k (realTimeClamp d) w+
        ∫ r in 0..d,deriv (fun s => E s i j) r*N j k (realTimeClamp r) w := by
    exact ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => hprod i j k
  have hvall : ∀ᵐ w ∂P,∀ i k,∀ t,t<⊤ → (∑ j,V i j k t w)=S i k*W k t w :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun k => hsumV i k
  filter_upwards [hpall,hvall] with w hp hv
  intro d hd hdT i
  apply linear_flow_integral_assembly A S E hEc (fun r j k => matrix_exp_entry_derivative A r j k)
    (by simp [E]) y d hd (fun j k r => N j k (realTimeClamp r) w)
    (fun k => W k (realTimeClamp d) w) (fun a j k => V a j k (realTimeClamp d) w)
    (fun j k => (open_process_real_regularity F (N j k) ((hN j k).adapted P F)
      ((hN j k).path P F)).2 d hd hdT w) _ (fun a k => hv a k _ (real_time_below d hd hdT)) i
  intro a j k
  have hh := hp a j k d hd hdT
  have hder r : deriv (fun s => E s a j) r=(A*E r) a j :=
    (matrix_exp_entry_derivative A r a j).deriv
  simpa only [hder] using hh

end Asakura.Chapter4

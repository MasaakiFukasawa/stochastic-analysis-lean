import Chapter12ArrayLinearBound
import Chapter12VolterraNormBound

open MeasureTheory Set
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem array_volterra_bound {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (U Q R : ℝ → I → E) (A : ℝ → E →L[ℝ] E)
    (hU : ∀i,Continuous (fun t => U t i)) (hR : ∀i,Continuous (fun t => R t i))
    (hA : Continuous A) (T L B C : ℝ) (hT : 0≤T) (hL : 0≤L) (hB : 0≤B) (hC : 0≤C)
    (hAb : ∀t,t∈Icc 0 T → ‖A t‖≤L)
    (hQb : ∀t,t∈Icc 0 T → Real.sqrt (∑i,‖Q t i‖^2)≤B)
    (hRb : ∀t,t∈Icc 0 T → Real.sqrt (∑i,‖R t i‖^2)≤C)
    (heq : ∀t,t∈Icc 0 T → ∀i,U t i=Q t i+∫s in 0..t,A s (U s i)+R s i) :
    ∀t,t∈Icc 0 T → Real.sqrt (∑i,‖U t i‖^2)≤(B+T*C)*Real.exp ((L+1)*T) := by
  let u : ℝ → PiLp 2 (fun _ : I => E) := fun t => WithLp.toLp 2 (U t)
  let q : ℝ → PiLp 2 (fun _ : I => E) := fun t => WithLp.toLp 2 (Q t)
  let g : ℝ → PiLp 2 (fun _ : I => E) := fun t => WithLp.toLp 2 (fun i => A t (U t i)+R t i)
  have hcu : Continuous u := (PiLp.continuous_toLp 2 (fun _ : I => E)).comp (continuous_pi hU)
  have hcg : Continuous g := (PiLp.continuous_toLp 2 (fun _ : I => E)).comp
    (continuous_pi (fun i => (hA.clm_apply (hU i)).add (hR i)))
  have hg t (ht : t∈Icc 0 T) : ‖g t‖≤L*‖u t‖+C := by
    rw [banach_array_norm,banach_array_norm]
    exact (array_add_norm_bound (fun i => A t (U t i)) (R t)).trans
      (add_le_add ((array_linear_bound (A t) (U t)).trans
        (mul_le_mul_of_nonneg_right (hAb t ht) (Real.sqrt_nonneg _))) (hRb t ht))
  have he t (ht : t∈Icc 0 T) : u t=q t+∫s in 0..t,g s := by
    apply PiLp.ext
    intro i
    let ev : PiLp 2 (fun _ : I => E) →L[ℝ] E := PiLp.proj 2 (fun _ : I => E) i
    have hh := ev.intervalIntegral_comp_comm (hcg.intervalIntegrable (μ:=volume) 0 t)
    change (∫s in 0..t,A s (U s i)+R s i)=ev (∫s in 0..t,g s) at hh
    change U t i=Q t i+ev (∫s in 0..t,g s)
    rw [←hh]
    exact heq t ht i
  have hh := volterra_norm_bound u q g hcu T L B C hT hL hB hC (fun t ht => by simpa only [q,banach_array_norm] using hQb t ht) hg he
  intro t ht
  simpa only [u,banach_array_norm] using hh t ht
end Asakura.Chapter12
#print axioms Asakura.Chapter12.array_volterra_bound

import Chapter8LinearVariationConstants

open MeasureTheory Set
namespace Asakura.Chapter8
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Subtract the constructed linear stochastic convolution; the remaining
integral equation has a classical integrating factor on each sample path. -/
theorem forced_linear_integral_solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E)
    (V N W f : ℝ → E) (v : E) (T : ℝ) (hT : 0≤T)
    (hV : Continuous V) (hN : Continuous N) (hf : Continuous f)
    (hVi : ∀ t∈Icc 0 T,V t=v+(∫ s in 0..t,A (V s)+f s)+W t)
    (hNi : ∀ t∈Icc 0 T,N t=(∫ s in 0..t,A (N s))+W t) :
    V T=NormedSpace.exp (T • A) v+
      (∫ s in 0..T,NormedSpace.exp ((T-s) • A) (f s))+N T := by
  have hc : Continuous (fun t => A (V t)+f t) := (A.continuous.comp hV).add hf
  have hnc : Continuous (fun t => A (N t)) := A.continuous.comp hN
  have hNi' t (ht : t∈Icc 0 T) : N t=0+(∫ s in 0..t,A (N s))+W t := by
    simpa only [zero_add] using hNi t ht
  have hd t (ht : t∈Ioo 0 T) : HasDerivAt (fun s => V s-N s) (A (V t-N t)+f t) t := by
    have hh := common_noise_integral_difference V N W (fun s => A (V s)+f s) (fun s => A (N s))
      v 0 T hc hnc hVi hNi' t ht
    convert hh using 1
    rw [map_sub]
    abel
  have he := linear_variation_constants A (fun s => V s-N s) f T hT
    (hV.sub hN).continuousOn hf hd
  have h0 : V 0-N 0=v := by
    rw [hVi 0 ⟨le_rfl,hT⟩,hNi 0 ⟨le_rfl,hT⟩]
    simp
  rw [h0] at he
  exact sub_eq_iff_eq_add.mp he
end Asakura.Chapter8

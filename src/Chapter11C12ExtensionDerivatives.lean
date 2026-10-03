import Chapter11C12RectangleExtension

open Set Filter
open scoped Topology
namespace Asakura.Chapter11

/-- Equality near a space-time point preserves the spatial derivatives
 used by Ito, including the second derivative. -/
theorem local_c12_extension_derivatives (g v : ℝ → ℝ → ℝ) (t x : ℝ)
    (he : (fun z : ℝ × ℝ => g z.1 z.2)=ᶠ[𝓝 (t,x)] (fun z => v z.1 z.2)) :
    g t x=v t x ∧ deriv (g t) x=deriv (v t) x ∧
      deriv (deriv (g t)) x=deriv (deriv (v t)) x := by
  have hx : g t=ᶠ[𝓝 x] v t := he.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  exact ⟨hx.eq_of_nhds,hx.deriv_eq,hx.deriv.deriv_eq⟩

end Asakura.Chapter11

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Norm bounds for the complex Gamma function

Norm (absolute-value) bounds for `Complex.Gamma`, built on the Euler integral representation.
This is the first ingredient of the Hadamard order-`≤ 1` input for the completed Riemann zeta
function (`C7_order`; see `SIDELvConservation.CouplingsAtPhi`): the Γ factor is the one piece
absent from Mathlib at this pin, and everything here is classical and of general use — a norm
estimate on `Complex.Gamma` in terms of the real Gamma function.

## Main results

* `Complex.norm_Gamma_le_Gamma_re`: for `0 < re z`, `‖Γ z‖ ≤ Γ (re z)`. The complex Gamma is
  dominated in norm by the real Gamma of the real part, directly from the Euler integral and the
  triangle inequality under the integral.

## Implementation notes

Written to Mathlib conventions (naming, granularity, docstrings, `Complex` namespace) so the file
can be upstreamed as a copy rather than a rewrite. The proof pushes the norm through the integral
with `norm_integral_le_integral_norm`, then rewrites the integrand pointwise on `Ioi 0` using
`Complex.norm_cpow_eq_rpow_re_of_pos`, recovering exactly `Real.Gamma_eq_integral`'s integrand.
-/

open Set MeasureTheory

namespace Complex

/-- For `0 < re z`, the complex Gamma function is bounded in norm by the real Gamma function of the
real part: `‖Γ z‖ ≤ Γ (re z)`.

Immediate from the Euler integral `Complex.Gamma_eq_integral` and the triangle inequality under the
integral: on `Ioi 0` the integrand satisfies `‖(-x).exp * (x : ℂ) ^ (z - 1)‖ = exp (-x) *
x ^ (re z - 1)` (via `norm_cpow_eq_rpow_re_of_pos`), which is exactly the integrand of
`Real.Gamma_eq_integral` at `re z`. -/
theorem norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  dsimp only [GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  rw [norm_mul, norm_real, norm_cpow_eq_rpow_re_of_pos hx0,
    Real.norm_of_nonneg (Real.exp_nonneg _), sub_re, one_re]

end Complex

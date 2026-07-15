import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Vertical-line norm bounds for the Hadamard input of the completed zeta

Norm (absolute-value) bounds for the factors of the completed Riemann zeta function on vertical
lines, feeding the Hadamard order-`≤ 1` input `C7_order` (see `SIDELvConservation.CouplingsAtPhi`).
The Γ factor is the one piece absent from Mathlib at this pin; everything here is classical and of
general use.

## Main results

* `Complex.norm_Gamma_le_Gamma_re`: for `0 < re z`, `‖Γ z‖ ≤ Γ (re z)`. The complex Gamma is
  dominated in norm by the real Gamma of the real part, directly from the Euler integral and the
  triangle inequality under the integral.
* `Complex.norm_riemannZeta_le_tsum`: for `1 < re s`, `‖ζ s‖ ≤ ∑' n, 1 / n ^ (re s)`, from the
  Dirichlet series and term-by-term norm bounding. On the edge `re s = 2` this reads `‖ζ s‖ ≤ ζ 2`.

## Implementation notes

Written to Mathlib conventions (naming, granularity, docstrings, `Complex` namespace) so the file
can be upstreamed as a copy rather than a rewrite. The Gamma bound pushes the norm through the
Euler integral with `norm_integral_le_integral_norm`, rewriting the integrand pointwise on `Ioi 0`
via `Complex.norm_cpow_eq_rpow_re_of_pos`. The zeta bound pushes the norm through the Dirichlet
series with `norm_tsum_le_tsum_norm`, using `Complex.norm_natCast_cpow_of_re_ne_zero` term-by-term.
-/

open Set MeasureTheory
open scoped Real

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

/-- Vertical-line norm bound for the Riemann zeta function from its Dirichlet series: for
`1 < re s`, `‖ζ s‖ ≤ ∑' n, 1 / n ^ (re s)`. The right-hand side is the real value `ζ (re s)`; on
the edge `re s = 2` it is `ζ 2 = π ^ 2 / 6`.

Proof: rewrite `ζ` as `∑' n, 1 / (n : ℂ) ^ s` (`zeta_eq_tsum_one_div_nat_cpow`), push the norm
through the sum (`norm_tsum_le_tsum_norm`), and bound term-by-term with
`‖1 / (n : ℂ) ^ s‖ = 1 / n ^ (re s)` (`norm_natCast_cpow_of_re_ne_zero`, which also handles
`n = 0`). Summability of the norms is `summable_one_div_nat_rpow`. -/
theorem norm_riemannZeta_le_tsum {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := by
  have hs0 : s.re ≠ 0 := ne_of_gt (by linarith)
  have key : ∀ n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ = 1 / (n : ℝ) ^ s.re := fun n => by
    rw [norm_div, norm_one, norm_natCast_cpow_of_re_ne_zero n hs0]
  have hsum : Summable fun n : ℕ => ‖(1 : ℂ) / (n : ℂ) ^ s‖ := by
    simp_rw [key]; exact (Real.summable_one_div_nat_rpow (p := s.re)).mpr hs
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  exact (norm_tsum_le_tsum_norm hsum).trans_eq (tsum_congr key)

/-- **Edge bound on the line `re s = 2`.** The completed Riemann zeta `Λ₀ = completedRiemannZeta₀`
satisfies the explicit bound `‖Λ₀ s‖ ≤ π⁻¹ · (∑' n, 1 / n ^ 2) + 3/2` there. Since
`∑' n, 1 / n ^ 2 = ζ 2 = π ^ 2 / 6`, the constant is `π/6 + 3/2 ≈ 2.02`.

This is the right-edge datum consumed by `PhragmenLindelof.vertical_strip`. On `re s = 2` each factor
of `Λ = π ^ (-s/2) · Γ(s/2) · ζ s` is controlled: `‖π ^ (-s/2)‖ = π⁻¹`, `‖Γ(s/2)‖ ≤ Γ 1 = 1`
(`norm_Gamma_le_Gamma_re`, `re (s/2) = 1`), and `‖ζ s‖ ≤ ∑' n, 1 / n ^ 2` (`norm_riemannZeta_le_tsum`).
The correction terms of `Λ₀ = Λ + 1/s + 1/(1-s)` bound as `‖1/s‖ ≤ 1/2` (`‖s‖ ≥ re s = 2`) and
`‖1/(1-s)‖ ≤ 1` (`‖1-s‖ ≥ |re (1-s)| = 1`). An explicit constant, not an existential, so the edge
hypothesis is independently checkable by arithmetic. -/
theorem norm_completedZeta₀_le_of_re_eq_two {s : ℂ} (hs : s.re = 2) :
    ‖completedRiemannZeta₀ s‖ ≤ Real.pi⁻¹ * (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) + 3 / 2 := by
  have hz1 : 1 < s.re := by rw [hs]; norm_num
  have hre2 : (s / 2).re = 1 := by
    rw [show (s / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) * s from by push_cast; ring, re_ofReal_mul, hs]
    norm_num
  have hreneg : (-s / 2).re = -1 := by
    rw [show (-s / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) * s from by push_cast; ring, re_ofReal_mul, hs]
    norm_num
  -- Λ₀ = Λ + 1/s + 1/(1-s)
  have hΛ₀ : completedRiemannZeta₀ s = completedRiemannZeta s + 1 / s + 1 / (1 - s) := by
    rw [completedRiemannZeta_eq]; ring
  -- Λ = π^(-s/2) · Γ(s/2) · ζ s
  have hΛ : completedRiemannZeta s = (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * riemannZeta s := by
    rw [completedZeta_eq_tsum_of_one_lt_re hz1, zeta_eq_tsum_one_div_nat_cpow hz1]
  -- the three factor bounds
  have hpi : ‖(π : ℂ) ^ (-s / 2)‖ = Real.pi⁻¹ := by
    rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos, hreneg, Real.rpow_neg_one]
  have hgam : ‖Gamma (s / 2)‖ ≤ 1 := by
    have h := norm_Gamma_le_Gamma_re (z := s / 2) (by rw [hre2]; norm_num)
    rwa [hre2, Real.Gamma_one] at h
  have hzeta : ‖riemannZeta s‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ) := by
    have h := norm_riemannZeta_le_tsum hz1; rwa [hs] at h
  have hΛnorm : ‖completedRiemannZeta s‖ ≤ Real.pi⁻¹ * (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) := by
    rw [hΛ, norm_mul, norm_mul, hpi]
    calc Real.pi⁻¹ * ‖Gamma (s / 2)‖ * ‖riemannZeta s‖
        ≤ Real.pi⁻¹ * 1 * (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) := by gcongr
      _ = Real.pi⁻¹ * (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) := by ring
  -- the two correction-term bounds
  have hnorm_s : ‖(1 : ℂ) / s‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]
    have hs2 : (2 : ℝ) ≤ ‖s‖ := by have h := abs_re_le_norm s; rw [hs] at h; simpa using h
    exact one_div_le_one_div_of_le (by norm_num) hs2
  have hnorm_1s : ‖(1 : ℂ) / (1 - s)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have h1 : (1 : ℝ) ≤ ‖1 - s‖ := by
      have h := abs_re_le_norm (1 - s); rw [sub_re, one_re, hs] at h
      rwa [show |(1 : ℝ) - 2| = 1 from by norm_num] at h
    exact (one_div_le_one_div_of_le one_pos h1).trans_eq (by norm_num)
  -- assemble
  rw [hΛ₀]
  calc ‖completedRiemannZeta s + 1 / s + 1 / (1 - s)‖
      ≤ ‖completedRiemannZeta s + 1 / s‖ + ‖(1 : ℂ) / (1 - s)‖ := norm_add_le _ _
    _ ≤ ‖completedRiemannZeta s‖ + ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (1 - s)‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ Real.pi⁻¹ * (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) + 1 / 2 + 1 := by gcongr
    _ = Real.pi⁻¹ * (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)) + 3 / 2 := by ring

end Complex

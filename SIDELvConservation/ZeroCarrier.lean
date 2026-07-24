import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# W-ORD-P1-FINSET — chunk (a): the entire carrier for the nontrivial ζ-zeros

Prerequisite construction for discharging the finite-set conjunct of
`PartialPositivity.ExplicitFormulaDecomp`.  Mathlib's `completedRiemannZeta₀` (Λ₀) is entire but
its zeros are **not** the nontrivial ζ-zeros (`Λ = Λ₀ − 1/s − 1/(1−s)`, so ζ-zeros are Λ-zeros,
not Λ₀-zeros).  This file builds an **entire** function `xiCarrier` whose zeros **in the open
critical strip** coincide exactly with the nontrivial ζ-zeros, so that the later isolated-zeros /
compactness argument (chunk b) can run on a compact box that touches the pole points `s = 0, 1`.

Closed form (survey-scope correction to the work-order's rough `−(2s−1)`):
`xiCarrier s = s·(s−1)·Λ₀(s) + 1`, which agrees with `s·(s−1)·Λ(s)` off `{0, 1}` and hence with
`s·(s−1)·Gammaℝ(s)·ζ(s)` on the strip.  Grade: DERIVES (all ingredients Mathlib-present at pin
5e932f97); no `sorry`.
-/

namespace SIDELvConservation
namespace PartialPositivity

open Complex

/-- **Entire carrier for the nontrivial ζ-zeros.**  `xiCarrier s = s·(s−1)·Λ₀(s) + 1`.
Manifestly entire (`differentiable_completedZeta₀` + polynomial parts); agrees with
`s·(s−1)·Λ(s)` off `{0,1}` (see `xiCarrier_eq_mul_completed`). -/
noncomputable def xiCarrier (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1

/-- `xiCarrier` is entire. -/
lemma differentiable_xiCarrier : Differentiable ℂ xiCarrier := by
  show Differentiable ℂ (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1)
  exact ((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1

/-- Off the pole points `{0,1}`, the carrier equals `s·(s−1)·Λ(s)`.
Uses `completedRiemannZeta_eq : Λ = Λ₀ − 1/s − 1/(1−s)`; the `1/s`, `1/(1−s)` terms contribute
exactly the additive `+1`. -/
lemma xiCarrier_eq_mul_completed {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    s * (s - 1) * completedRiemannZeta s = xiCarrier s := by
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [completedRiemannZeta_eq, xiCarrier]
  field_simp
  ring

/-- Strip form: on `{s ≠ 0, s ≠ 1}` with `Gammaℝ s ≠ 0`, the carrier factors as
`s·(s−1)·Gammaℝ(s)·ζ(s)` — the shape that reads off the ζ-zeros. -/
lemma xiCarrier_zeta_form {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hG : Gammaℝ s ≠ 0) :
    xiCarrier s = s * (s - 1) * Gammaℝ s * riemannZeta s := by
  have hcomp : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    rw [riemannZeta_def_of_ne_zero h0]; field_simp
  rw [← xiCarrier_eq_mul_completed h0 h1, hcomp]; ring

/-- **Strip zero-equivalence.**  On the open critical strip `0 < Re s < 1`, the carrier vanishes
exactly at the nontrivial ζ-zeros. -/
lemma xiCarrier_eq_zero_iff_riemannZeta {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    xiCarrier s = 0 ↔ riemannZeta s = 0 := by
  have hne0 : s ≠ 0 := by rintro rfl; simp at h0
  have hne1 : s ≠ 1 := by rintro rfl; norm_num at h1
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hne1
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  rw [xiCarrier_zeta_form hne0 hne1 hG, mul_eq_zero, mul_eq_zero, mul_eq_zero]
  constructor
  · rintro (((h | h) | h) | h)
    · exact absurd h hne0
    · exact absurd h hsub
    · exact absurd h hG
    · exact h
  · intro h; exact Or.inr h

/-- **Non-vanishing witness** excluding `analyticOrderAt = ⊤` on connected ℂ (chunk b input).
For `Re s > 1` the carrier is nonzero, via `riemannZeta_ne_zero_of_one_lt_re` pushed through the
strip form. -/
lemma xiCarrier_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : xiCarrier s ≠ 0 := by
  have h0 : (0 : ℝ) < s.re := by linarith
  have hne0 : s ≠ 0 := by rintro rfl; simp at h0
  have hne1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hne1
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  rw [xiCarrier_zeta_form hne0 hne1 hG]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hne0 hsub) hG) hz

end PartialPositivity
end SIDELvConservation

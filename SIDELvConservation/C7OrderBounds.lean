import SIDELvConservation.T1_MellinFactorization

/-!
# W-8: exponential domination of the theta remainder `Φ`

For the C₇-order route, `Φ t = (evenKernel 0 t - 1)/2` must be dominated by an exponential envelope on
`[1, ∞)`. Mathlib's `isBigO_atTop_evenKernel_sub` gives the envelope at `∞`; continuity of the even
kernel (`continuousOn_evenKernel`) closes the compact seam `[1, T₀]`. The result is stated
**existentially** in the decay rate `p` (rather than the explicit `π` of the geometric route, which
was priced and passed over when its `evenKernel ↔ F_nat` symmetrization bridge met a tsum-API fight),
so the representation and assembly consume `p` with no retrofit.
-/

open scoped Real
open Complex Set MeasureTheory HurwitzZeta Filter Topology

namespace SIDELvConservation

/-- **Exponential domination of `Φ`** (bricks 1–2, big-O + seam route). There exist `p > 0` and `C`
with `‖Φ t‖ ≤ C · e^{-p t}` for every `t ≥ 1`. The rate `p` is Mathlib's `isBigO_atTop` decay
constant for the even kernel; `C` absorbs the compact seam `[1, T₀]` via continuity.

Screen: `Φ` genuinely decays exponentially at `∞`; the statement asserts a truth of the witness. -/
theorem exists_norm_Phi_le :
    ∃ p C : ℝ, 0 < p ∧ ∀ t : ℝ, 1 ≤ t → ‖Phi t‖ ≤ C * Real.exp (-p * t) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_evenKernel_sub 0
  simp only [reduceIte] at hO
  obtain ⟨c, hc⟩ := hO.bound
  rw [eventually_atTop] at hc
  obtain ⟨T₀, hT₀⟩ := hc
  set T := max T₀ 1 with hTdef
  have hT1 : (1 : ℝ) ≤ T := le_max_right _ _
  have hsub : Icc 1 T ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le one_pos ht.1
  -- the seam function k t = |evenKernel 0 t - 1| * e^{p t}, continuous on the compact [1, T]
  have hcont : ContinuousOn (fun t => |evenKernel 0 t - 1| * Real.exp (p * t)) (Icc 1 T) :=
    ((((continuousOn_evenKernel 0).mono hsub).sub continuousOn_const).abs).mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
  obtain ⟨x, hx, hxmax⟩ := (isCompact_Icc).exists_isMaxOn (nonempty_Icc.2 hT1) hcont
  set M := |evenKernel 0 x - 1| * Real.exp (p * x) with hMdef
  refine ⟨p, max c M / 2, hp, fun t ht => ?_⟩
  -- ‖Φ t‖ = |evenKernel 0 t - 1| / 2
  have hPhi : ‖Phi t‖ = |evenKernel 0 t - 1| / 2 := by
    rw [Phi, show ((evenKernel 0 t : ℂ) - 1) = ((evenKernel 0 t - 1 : ℝ) : ℂ) by push_cast; ring,
      norm_div, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  rw [hPhi]
  -- key: |evenKernel 0 t - 1| ≤ max c M * e^{-p t}
  have hkey : |evenKernel 0 t - 1| ≤ max c M * Real.exp (-p * t) := by
    rcases le_or_gt T t with hTt | htT
    · -- t ≥ T ≥ T₀ : big-O bound
      have hle := hT₀ t (le_trans (le_max_left _ _) hTt)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hle
      exact hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    · -- 1 ≤ t < T : seam bound M
      have htmem : t ∈ Icc 1 T := ⟨ht, htT.le⟩
      have hbound : |evenKernel 0 t - 1| * Real.exp (p * t) ≤ M := hxmax htmem
      have hrw : |evenKernel 0 t - 1|
          = (|evenKernel 0 t - 1| * Real.exp (p * t)) * Real.exp (-p * t) := by
        rw [mul_assoc, ← Real.exp_add, show p * t + -p * t = 0 by ring, Real.exp_zero, mul_one]
      rw [hrw]
      calc (|evenKernel 0 t - 1| * Real.exp (p * t)) * Real.exp (-p * t)
          ≤ M * Real.exp (-p * t) := mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
        _ ≤ max c M * Real.exp (-p * t) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  calc |evenKernel 0 t - 1| / 2 ≤ (max c M * Real.exp (-p * t)) / 2 := by
        apply div_le_div_of_nonneg_right hkey; norm_num
    _ = max c M / 2 * Real.exp (-p * t) := by ring

/-- **Reduction (brick 3 foundation).** `completedRiemannZeta₀ s = ½ · mellin f_modif (s/2)`, where
`f_modif` is `(hurwitzEvenFEPair 0).f_modif` — the `Ioi 1`/`Ioo 0 1` split kernel. Definitional:
`completedRiemannZeta₀ = completedHurwitzZetaEven₀ 0`, `= (hurwitzEvenFEPair 0).Λ₀ (s/2) / 2`, and
`WeakFEPair.Λ₀ = mellin f_modif`. This is the entire-function representation Mathlib already carries;
the growth bound consumes it without re-deriving Riemann's continuation or proving entirety. -/
theorem completedRiemannZeta₀_eq_half_mellin (s : ℂ) :
    completedRiemannZeta₀ s = mellin (hurwitzEvenFEPair 0).f_modif (s / 2) / 2 := rfl

/-- **Norm-Mellin bound (brick 3, step 2).** `‖Λ₀ s‖ ≤ ½ · ∫₀^∞ t^{re(s/2)−1}·‖f_modif t‖ dt`,
pushing the norm through the Mellin integral (`norm_integral_le_integral_norm`) and the pointwise
`‖(t:ℂ)^{s/2−1} • f_modif t‖ = t^{re(s/2)−1}·‖f_modif t‖` on `Ioi 0`. The `½` is the Hurwitz
normalization; it washes into the existential `C` at assembly. -/
theorem norm_completedRiemannZeta₀_le (s : ℂ) :
    ‖completedRiemannZeta₀ s‖
      ≤ (∫ t in Ioi (0 : ℝ), t ^ ((s / 2).re - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) / 2 := by
  rw [completedRiemannZeta₀_eq_half_mellin, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  gcongr
  rw [mellin]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [Set.mem_Ioi] at ht
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]

end SIDELvConservation

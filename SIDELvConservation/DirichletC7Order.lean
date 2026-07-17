import SIDELvConservation.C7OrderBounds
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# The Dirichlet splice — C₇-order growth for character-twisted completed L-functions

Work-order (e), PLACE-papers OPEN_TRAILS. The goal is the character generalization of the C₇-order
bound `exists_norm_completedRiemannZeta₀_le_exp` to the completed Dirichlet L-function
`completedLFunction χ` (primitive / non-principal `χ`), of the same order-≤1 maximal-type shape
`‖Λ(s,χ)‖ ≤ C · exp(A · ‖s‖ · log(‖s‖ + 2))`.

**Route (uniform, Hurwitz-FE-pair level).** For even `χ`, `completedLFunction χ` is a finite ZMod-sum
of even Hurwitz completed zetas `completedHurwitzZetaEven₀ a` (poles cancelling for `χ ≠ 1`), each an
FE-pair `Λ₀ = mellin f_modif` — the same representation the zeta proof (`C7OrderBounds`) consumes.
The a-independent assembly (`Gamma_le_exp`, `exp_arg_bound`, `reflect_arith`, `integrableOn_rpow_…`)
transports verbatim; only the domination and `f_modif`-norm bricks need parameterizing over `a`, and
for `a ≠ 0` the FE-pair is not self-dual (it couples `evenKernel a` with `cosKernel a`).

**This module (sitting one of the proof):** the a-general exponential-domination bricks — the
foundation of the per-`a` bound. Both `evenKernel a` and `cosKernel a` decay exponentially at `∞`
(Mathlib's `isBigO_atTop_*_sub`) and are continuous on `Ioi 0`, so the big-O tail + compact seam gives
a clean envelope `≤ C · e^{-p t}` on `[1, ∞)` for each.
-/

open scoped Real
open Complex Set MeasureTheory HurwitzZeta Filter Topology

namespace SIDELvConservation

/-- **General exponential-domination brick.** If `k t - L` is big-O of `e^{-p t}` at `∞` (for some
`p > 0`) and `k` is continuous on `Ioi 0`, then `|k t - L| ≤ C · e^{-p t}` for all `t ≥ 1`, with `C`
absorbing the compact seam `[1, T₀]` via continuity. This is `exists_norm_Phi_le`'s structure, freed
of the `a = 0` / `Φ` specifics so both kernels reuse it. -/
theorem exists_exp_domination
    {k : ℝ → ℝ} {L : ℝ}
    (hO : ∃ p : ℝ, 0 < p ∧ (fun t => k t - L) =O[atTop] (fun t => Real.exp (-p * t)))
    (hcont : ContinuousOn k (Ioi 0)) :
    ∃ p C : ℝ, 0 < p ∧ ∀ t : ℝ, 1 ≤ t → |k t - L| ≤ C * Real.exp (-p * t) := by
  obtain ⟨p, hp, hO⟩ := hO
  obtain ⟨c, hc⟩ := hO.bound
  rw [eventually_atTop] at hc
  obtain ⟨T₀, hT₀⟩ := hc
  set T := max T₀ 1 with hTdef
  have hT1 : (1 : ℝ) ≤ T := le_max_right _ _
  have hsub : Icc 1 T ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le one_pos ht.1
  have hcont' : ContinuousOn (fun t => |k t - L| * Real.exp (p * t)) (Icc 1 T) :=
    (((hcont.mono hsub).sub continuousOn_const).abs).mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
  obtain ⟨x, hx, hxmax⟩ := (isCompact_Icc).exists_isMaxOn (nonempty_Icc.2 hT1) hcont'
  set M := |k x - L| * Real.exp (p * x) with hMdef
  refine ⟨p, max c M, hp, fun t ht => ?_⟩
  rcases le_or_gt T t with hTt | htT
  · -- t ≥ T ≥ T₀ : big-O bound
    have hle := hT₀ t (le_trans (le_max_left _ _) hTt)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hle
    exact hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · -- 1 ≤ t < T : seam maximum M
    have htmem : t ∈ Icc 1 T := ⟨ht, htT.le⟩
    have hbound : |k t - L| * Real.exp (p * t) ≤ M := hxmax htmem
    have hrw : |k t - L| = (|k t - L| * Real.exp (p * t)) * Real.exp (-p * t) := by
      rw [mul_assoc, ← Real.exp_add, show p * t + -p * t = 0 by ring, Real.exp_zero, mul_one]
    rw [hrw]
    calc (|k t - L| * Real.exp (p * t)) * Real.exp (-p * t)
        ≤ M * Real.exp (-p * t) := mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
      _ ≤ max c M * Real.exp (-p * t) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- **Even-kernel domination at general `a`.** `|evenKernel a t − L_a| ≤ C · e^{-p t}` for `t ≥ 1`,
where `L_a = 1` if `a = 0` and `0` otherwise. The `Ioi 1` growth-carrying brick for the per-`a`
Hurwitz bound (generalizes `exists_norm_Phi_le`, which is `a = 0`). -/
theorem exists_norm_evenKernel_sub_le (a : UnitAddCircle) :
    ∃ p C : ℝ, 0 < p ∧ ∀ t : ℝ, 1 ≤ t →
      |evenKernel a t - (if a = 0 then 1 else 0)| ≤ C * Real.exp (-p * t) :=
  exists_exp_domination (isBigO_atTop_evenKernel_sub a) (continuousOn_evenKernel a)

/-- **Cos-kernel domination at general `a`.** `|cosKernel a t − 1| ≤ C · e^{-p t}` for `t ≥ 1`. The
second domination brick — needed because for `a ≠ 0` the `hurwitzEvenFEPair a` is not self-dual, so
the `Ioo 0 1` piece of `f_modif` folds through `cosKernel a` (via the functional equation) rather than
back through `evenKernel a`. -/
theorem exists_norm_cosKernel_sub_le (a : UnitAddCircle) :
    ∃ p C : ℝ, 0 < p ∧ ∀ t : ℝ, 1 ≤ t →
      |cosKernel a t - 1| ≤ C * Real.exp (-p * t) :=
  exists_exp_domination (isBigO_atTop_cosKernel_sub a) (continuousOn_cosKernel a)

/-! ## The `f_modif` norm at general `a` (WATCH 1: the non-self-dual fold) -/

/-- **`Ioi 1` piece, general `a`.** `‖f_modif t‖ = |evenKernel a t − L_a|`, `L_a = f₀ = if a=0 then 1
else 0`. The growth-carrying tail; bounded by `exists_norm_evenKernel_sub_le`. -/
theorem norm_f_modif_a_of_one_lt (a : UnitAddCircle) {t : ℝ} (ht : 1 < t) :
    ‖(hurwitzEvenFEPair a).f_modif t‖ = |evenKernel a t - (if a = 0 then 1 else 0)| := by
  have hnotIoo : t ∉ Set.Ioo (0 : ℝ) 1 := fun h => absurd h.2 (not_lt.mpr ht.le)
  simp only [WeakFEPair.f_modif, hurwitzEvenFEPair, Function.comp_apply, Pi.add_apply,
    Set.indicator_of_mem (Set.mem_Ioi.mpr ht), Set.indicator_of_notMem hnotIoo, add_zero]
  rw [show ((evenKernel a t : ℂ) - (if a = 0 then (1 : ℂ) else 0))
        = (((evenKernel a t - (if a = 0 then (1 : ℝ) else 0)) : ℝ) : ℂ) by
      by_cases h : a = 0 <;> simp [h],
    Complex.norm_real, Real.norm_eq_abs]

/-- **`Ioo 0 1` piece, general `a`.** The non-self-dual fold: `f_modif t = evenKernel a t − t^{−1/2}`
(since `ε = 1`, `k = 1/2`, `g₀ = 1`), and the functional equation `evenKernel a t = t^{−1/2}·cosKernel
a (1/t)` gives `‖f_modif t‖ = t^{−1/2}·|cosKernel a (1/t) − 1|`. Bounded by `exists_norm_cosKernel_sub_le`
at `1/t ≥ 1`. Uses the library FE for general `a`, not the `a = 0` `evenKernel = cosKernel`. -/
theorem norm_f_modif_a_of_mem_Ioo (a : UnitAddCircle) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ‖(hurwitzEvenFEPair a).f_modif t‖
      = t ^ (-(1 / 2) : ℝ) * |cosKernel a (1 / t) - 1| := by
  have ht0 : 0 < t := ht.1
  have hnotIoi : t ∉ Set.Ioi (1 : ℝ) := fun h => absurd h (not_lt.mpr ht.2.le)
  have hfe : evenKernel a t = t ^ (-(1 / 2) : ℝ) * cosKernel a (1 / t) := by
    rw [evenKernel_functional_equation, one_div (t ^ _), ← Real.rpow_neg ht0.le]
  simp only [WeakFEPair.f_modif, hurwitzEvenFEPair, Function.comp_apply, Pi.add_apply,
    Set.indicator_of_notMem hnotIoi, Set.indicator_of_mem ht, zero_add, one_mul, smul_eq_mul,
    mul_one]
  rw [show ((evenKernel a t : ℝ) : ℂ) - ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)
      = (((evenKernel a t - t ^ (-(1 / 2) : ℝ)) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, hfe]
  rw [show t ^ (-(1 / 2) : ℝ) * cosKernel a (1 / t) - t ^ (-(1 / 2) : ℝ)
      = t ^ (-(1 / 2) : ℝ) * (cosKernel a (1 / t) - 1) by ring, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ht0.le _)]

/-- **Half-Mellin representation, general `a`.** `completedHurwitzZetaEven₀ a s = ½·mellin f_modif (s/2)`
— definitional (`= (hurwitzEvenFEPair a).Λ₀ (s/2) / 2`, `WeakFEPair.Λ₀ = mellin f_modif`). The
entire-function representation the growth bound consumes. -/
theorem completedHurwitzZetaEven₀_eq_half_mellin (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven₀ a s = mellin (hurwitzEvenFEPair a).f_modif (s / 2) / 2 := rfl

end SIDELvConservation

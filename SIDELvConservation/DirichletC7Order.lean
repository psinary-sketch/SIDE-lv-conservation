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

/-! ## Per-`a` even Hurwitz C₇-order bound (assembly; a-independent bricks reused from `C7OrderBounds`) -/

/-- **Norm-Mellin bound, general `a`.** `‖Λ₀(a,s)‖ ≤ ½·∫₀^∞ t^{re(s/2)−1}·‖f_modif t‖`. -/
theorem norm_completedHurwitzZetaEven₀_le (a : UnitAddCircle) (s : ℂ) :
    ‖completedHurwitzZetaEven₀ a s‖
      ≤ (∫ t in Ioi (0 : ℝ), t ^ ((s / 2).re - 1) * ‖(hurwitzEvenFEPair a).f_modif t‖) / 2 := by
  rw [completedHurwitzZetaEven₀_eq_half_mellin, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  gcongr
  rw [mellin]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [Set.mem_Ioi] at ht
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]

/-- **`Ioi 1` Γ-bound, general `a`.** Growth-carrying tail, via `norm_f_modif_a_of_one_lt` +
`evenKernel a` domination. -/
theorem norm_f_modif_a_ioi_one_integral_le (a : UnitAddCircle) {p Cd x : ℝ} (hp : 0 < p) (hCd : 0 ≤ Cd)
    (hdom : ∀ t : ℝ, 1 ≤ t → |evenKernel a t - (if a = 0 then 1 else 0)| ≤ Cd * Real.exp (-(p * t)))
    (hint : MeasureTheory.IntegrableOn
      (fun t => t ^ (x - 1) * ‖(hurwitzEvenFEPair a).f_modif t‖) (Ioi 1)) :
    (∫ t in Ioi (1 : ℝ), t ^ (x - 1) * ‖(hurwitzEvenFEPair a).f_modif t‖)
      ≤ Cd * (1 / p) ^ (max x 1) * Real.Gamma (max x 1) := by
  set y := max x 1 with hy
  have hy1 : (1 : ℝ) ≤ y := le_max_right _ _
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
  have hR0 : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (y - 1) * Real.exp (-(p * t))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_Ioi hy0 hp
  have hRint : MeasureTheory.IntegrableOn
      (fun t : ℝ => Cd * (t ^ (y - 1) * Real.exp (-(p * t)))) (Ioi 1) :=
    (hR0.mono_set (Set.Ioi_subset_Ioi zero_le_one)).const_mul Cd
  calc (∫ t in Ioi (1 : ℝ), t ^ (x - 1) * ‖(hurwitzEvenFEPair a).f_modif t‖)
      ≤ ∫ t in Ioi (1 : ℝ), Cd * (t ^ (y - 1) * Real.exp (-(p * t))) := by
        refine MeasureTheory.setIntegral_mono_on hint hRint measurableSet_Ioi (fun t ht => ?_)
        rw [Set.mem_Ioi] at ht
        rw [norm_f_modif_a_of_one_lt a ht]
        have h1 := hdom t ht.le
        have h2 : t ^ (x - 1) ≤ t ^ (y - 1) :=
          Real.rpow_le_rpow_of_exponent_le ht.le (by linarith [le_max_left x 1])
        calc t ^ (x - 1) * |evenKernel a t - (if a = 0 then 1 else 0)|
            ≤ t ^ (y - 1) * (Cd * Real.exp (-(p * t))) :=
              mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
          _ = Cd * (t ^ (y - 1) * Real.exp (-(p * t))) := by ring
    _ = Cd * ∫ t in Ioi (1 : ℝ), t ^ (y - 1) * Real.exp (-(p * t)) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ Cd * ∫ t in Ioi (0 : ℝ), t ^ (y - 1) * Real.exp (-(p * t)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCd
        refine MeasureTheory.setIntegral_mono_set hR0 ?_ ?_
        · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
          rw [Set.mem_Ioi] at ht; positivity
        · exact (HasSubset.Subset.eventuallyLE (Set.Ioi_subset_Ioi zero_le_one))
    _ = Cd * ((1 / p) ^ y * Real.Gamma y) := by rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hy0 hp]
    _ = Cd * (1 / p) ^ y * Real.Gamma y := by ring

/-- **`Ioo 0 1` bound by a fixed majorant, general `a`.** For `re s ≥ ½` (so `x ≥ ¼`). Uses only
hasMellin integrability, not the `cosKernel` decay. -/
theorem norm_f_modif_a_ioo_integral_le (a : UnitAddCircle) {x : ℝ} (hx : (1 : ℝ) / 4 ≤ x)
    (hint : MeasureTheory.IntegrableOn
      (fun t => t ^ (x - 1) * ‖(hurwitzEvenFEPair a).f_modif t‖) (Ioo 0 1))
    (hmaj : MeasureTheory.IntegrableOn
      (fun t => t ^ (-(3 : ℝ) / 4) * ‖(hurwitzEvenFEPair a).f_modif t‖) (Ioo 0 1)) :
    (∫ t in Ioo (0 : ℝ) 1, t ^ (x - 1) * ‖(hurwitzEvenFEPair a).f_modif t‖)
      ≤ ∫ t in Ioo (0 : ℝ) 1, t ^ (-(3 : ℝ) / 4) * ‖(hurwitzEvenFEPair a).f_modif t‖ := by
  refine MeasureTheory.setIntegral_mono_on hint hmaj measurableSet_Ioo (fun t ht => ?_)
  have h : t ^ (x - 1) ≤ t ^ (-(3 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2.le (by linarith)
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

/-- **Per-`a` even Hurwitz C₇-order growth on `re s ≥ ½`.** The direct analog of
`exists_norm_completedRiemannZeta₀_le_exp_half`, generalized over `a` via the sitting-1/2 bricks; the
a-independent assembly (`exp_arg_bound`, `Gamma_le_exp`, `integrableOn_rpow_mul_exp_Ioi`) transports. -/
theorem exists_norm_completedHurwitzZetaEven₀_le_exp_half (a : UnitAddCircle) :
    ∃ A C : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖completedHurwitzZetaEven₀ a s‖ ≤ C * Real.exp (A * (‖s‖ * Real.log (‖s‖ + 2))) := by
  obtain ⟨p, Cd, hp, hdom0⟩ := exists_norm_evenKernel_sub_le a
  have hdom : ∀ t : ℝ, 1 ≤ t →
      |evenKernel a t - (if a = 0 then 1 else 0)| ≤ Cd * Real.exp (-(p * t)) := by
    intro t ht; have := hdom0 t ht; rwa [show -(p * t) = -p * t by ring]
  obtain ⟨A₀, B₀, hA₀0, hA₀⟩ := exp_arg_bound (show (0 : ℝ) ≤ |Real.log (1 / p)| from abs_nonneg _)
  have hCd : 0 ≤ Cd := by
    by_contra hc; push_neg at hc
    have h := (hdom 1 le_rfl).trans' (abs_nonneg _)
    linarith [mul_neg_of_neg_of_pos hc (Real.exp_pos (-(p * 1)))]
  have hintg : ∀ w : ℂ, MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (w.re - 1) * ‖(hurwitzEvenFEPair a).f_modif t‖) (Ioi 0) := fun w => by
    have h : MeasureTheory.IntegrableOn
        (fun t : ℝ => ‖(t : ℂ) ^ (w - 1) • (hurwitzEvenFEPair a).f_modif t‖) (Ioi 0) :=
      (((hurwitzEvenFEPair a).toStrongFEPair.hasMellin w).1).norm
    refine MeasureTheory.IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
    rw [Set.mem_Ioi] at ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  have hmajint : MeasureTheory.IntegrableOn
      (fun t => t ^ (-(3 : ℝ) / 4) * ‖(hurwitzEvenFEPair a).f_modif t‖) (Ioo 0 1) := by
    refine MeasureTheory.IntegrableOn.congr_fun ((hintg (1 / 4 : ℂ)).mono_set Set.Ioo_subset_Ioi_self)
      (fun t _ => ?_) measurableSet_Ioo
    norm_num
  set M₀ := ∫ t in Ioo (0 : ℝ) 1, t ^ (-(3 : ℝ) / 4) * ‖(hurwitzEvenFEPair a).f_modif t‖ with hM₀
  have hM₀0 : 0 ≤ M₀ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => by have := ht.1; positivity)
  refine ⟨A₀, 2⁻¹ * M₀ + Cd * Real.exp B₀, hA₀0, fun s hs => ?_⟩
  set x := (s / 2).re with hxdef
  have hx14 : 1 / 4 ≤ x := by rw [hxdef, Complex.div_ofNat_re]; linarith
  set y := max x 1 with hy
  have hy1 : (1 : ℝ) ≤ y := le_max_right _ _
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy1
  have hxs : x ≤ ‖s‖ / 2 := by
    rw [hxdef, Complex.div_ofNat_re]; have := Complex.re_le_norm s; linarith
  have hys : y ≤ ‖s‖ / 2 + 1 := by
    rw [hy]; rcases le_total x 1 with h | h
    · rw [max_eq_right h]; linarith [norm_nonneg s]
    · rw [max_eq_left h]; linarith [hxs]
  have hsplit : (∫ t in Ioi (0 : ℝ), t ^ (x - 1) * ‖(hurwitzEvenFEPair a).f_modif t‖)
      = (∫ t in Ioo (0 : ℝ) 1, t ^ (x - 1) * ‖(hurwitzEvenFEPair a).f_modif t‖)
        + ∫ t in Ioi (1 : ℝ), t ^ (x - 1) * ‖(hurwitzEvenFEPair a).f_modif t‖ := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one),
      MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        ((hintg (s / 2)).mono_set Set.Ioc_subset_Ioi_self)
        ((hintg (s / 2)).mono_set (Set.Ioi_subset_Ioi zero_le_one)),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hIoo : (∫ t in Ioo (0 : ℝ) 1, t ^ (x - 1) * ‖(hurwitzEvenFEPair a).f_modif t‖) ≤ M₀ :=
    norm_f_modif_a_ioo_integral_le a hx14 ((hintg (s / 2)).mono_set Set.Ioo_subset_Ioi_self) hmajint
  have hIoi : (∫ t in Ioi (1 : ℝ), t ^ (x - 1) * ‖(hurwitzEvenFEPair a).f_modif t‖)
      ≤ Cd * (1 / p) ^ y * Real.Gamma y :=
    norm_f_modif_a_ioi_one_integral_le a hp hCd hdom
      ((hintg (s / 2)).mono_set (Set.Ioi_subset_Ioi zero_le_one))
  have hgexp : (1 / p) ^ y * Real.Gamma y
      ≤ Real.exp (|Real.log (1 / p)| * y + 2 * y * Real.log (y + 2)) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.exp_add]
    refine mul_le_mul ?_ (Gamma_le_exp hy1) (Real.Gamma_nonneg_of_nonneg hy0.le) (Real.exp_pos _).le
    rw [Real.exp_le_exp]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hy0.le
  calc ‖completedHurwitzZetaEven₀ a s‖
      ≤ (∫ t in Ioi (0 : ℝ), t ^ (x - 1) * ‖(hurwitzEvenFEPair a).f_modif t‖) / 2 :=
        norm_completedHurwitzZetaEven₀_le a s
    _ ≤ (M₀ + Cd * (1 / p) ^ y * Real.Gamma y) / 2 := by rw [hsplit]; gcongr
    _ = 2⁻¹ * M₀ + 2⁻¹ * (Cd * ((1 / p) ^ y * Real.Gamma y)) := by ring
    _ ≤ (2⁻¹ * M₀ + Cd * Real.exp B₀) * Real.exp (A₀ * (‖s‖ * Real.log (‖s‖ + 2))) := by
        have hexp1 : (1 : ℝ) ≤ Real.exp (A₀ * (‖s‖ * Real.log (‖s‖ + 2))) :=
          Real.one_le_exp (by
            have : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg s]); positivity)
        have hmain : (1 / p) ^ y * Real.Gamma y
            ≤ Real.exp B₀ * Real.exp (A₀ * (‖s‖ * Real.log (‖s‖ + 2))) := by
          refine hgexp.trans ?_
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by have := hA₀ ‖s‖ y (norm_nonneg s) hy1 hys; nlinarith [this])
        have hXnn : (0 : ℝ) ≤ Cd * ((1 / p) ^ y * Real.Gamma y) :=
          mul_nonneg hCd (mul_nonneg (Real.rpow_nonneg (by positivity) y)
            (Real.Gamma_nonneg_of_nonneg hy0.le))
        rw [add_mul]
        refine add_le_add (le_mul_of_one_le_right (by positivity) hexp1) ?_
        calc 2⁻¹ * (Cd * ((1 / p) ^ y * Real.Gamma y))
            ≤ Cd * ((1 / p) ^ y * Real.Gamma y) := by linarith
          _ ≤ Cd * (Real.exp B₀ * Real.exp (A₀ * (‖s‖ * Real.log (‖s‖ + 2)))) :=
              mul_le_mul_of_nonneg_left hmain hCd
          _ = Cd * Real.exp B₀ * Real.exp (A₀ * (‖s‖ * Real.log (‖s‖ + 2))) := by ring

/-! ## The reduction to the completed Dirichlet L-function (even case) -/

/-- **Reduction identity (WATCH 2, term-by-term).** For even `Φ : ZMod N → ℂ` with `Φ 0 = 0` and
`∑ Φ = 0`, `completedLFunction Φ` is the conductor-scaled χ-weighted sum of the *entire* even Hurwitz
completed zetas — the two pole-correction terms of `completedHurwitzZetaEven_eq` vanish under exactly
these two conditions (`Φ 0 = 0` kills the `s = 0` term, `∑ Φ = 0` the `s = 1` term). -/
theorem completedLFunction_eq_sum_even₀ {N : ℕ} [NeZero N] {Φ : ZMod N → ℂ}
    (hΦe : Φ.Even) (hΦ0 : Φ 0 = 0) (hΦs : ∑ j, Φ j = 0) (s : ℂ) :
    ZMod.completedLFunction Φ s
      = (N : ℂ) ^ (-s) * ∑ j, Φ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s := by
  rw [ZMod.completedLFunction_def_even hΦe]
  congr 1
  have h1 : ∑ j : ZMod N, Φ j * ((if ZMod.toAddCircle j = 0 then (1 : ℂ) else 0) / s) = 0 := by
    have hstep : ∑ j : ZMod N, Φ j * (if ZMod.toAddCircle j = 0 then (1 : ℂ) else 0) = Φ 0 := by
      have hpt : ∀ j : ZMod N, Φ j * (if ZMod.toAddCircle j = 0 then (1 : ℂ) else 0)
          = (if j = 0 then Φ j else 0) := by
        intro j
        by_cases h : j = 0
        · subst h; simp [ZMod.toAddCircle_eq_zero]
        · have hne : ZMod.toAddCircle j ≠ 0 := fun hc => h (ZMod.toAddCircle_eq_zero.mp hc)
          simp [hne, h]
      rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_ite_eq' Finset.univ (0 : ZMod N) Φ]
      simp
    calc ∑ j : ZMod N, Φ j * ((if ZMod.toAddCircle j = 0 then (1 : ℂ) else 0) / s)
        = (∑ j : ZMod N, Φ j * (if ZMod.toAddCircle j = 0 then (1 : ℂ) else 0)) / s := by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun j _ => by rw [mul_div_assoc])
      _ = Φ 0 / s := by rw [hstep]
      _ = 0 := by rw [hΦ0, zero_div]
  have h2 : ∑ j : ZMod N, Φ j * (1 / (1 - s)) = 0 := by
    rw [← Finset.sum_mul, hΦs, zero_mul]
  have expand : ∀ j ∈ Finset.univ, Φ j * completedHurwitzZetaEven (ZMod.toAddCircle j) s
      = Φ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s
        - Φ j * ((if ZMod.toAddCircle j = 0 then (1 : ℂ) else 0) / s)
        - Φ j * (1 / (1 - s)) := by
    intro j _; rw [completedHurwitzZetaEven_eq]; ring
  rw [Finset.sum_congr rfl expand, Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1, h2,
    sub_zero, sub_zero]

/-- **Conductor factor.** `‖(N : ℂ)^(−s)‖ ≤ exp(log N · ‖s‖)` — order-1 type, absorbed into `A`.
`N ≥ 1` (from `NeZero N`) gives `log N ≥ 0`; `−re s ≤ ‖s‖`. -/
theorem norm_natCast_cpow_neg_le {N : ℕ} [NeZero N] (s : ℂ) :
    ‖(N : ℂ) ^ (-s)‖ ≤ Real.exp (Real.log N * ‖s‖) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Complex.norm_natCast_cpow_of_pos hN, Complex.neg_re, Real.rpow_def_of_pos hN0, Real.exp_le_exp]
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hre : -s.re ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s; rw [abs_le] at this; linarith [this.1]
  exact mul_le_mul_of_nonneg_left hre hlogN

/-- **Even-Φ C₇-order bound on `re s ≥ ½`.** Combines the per-`a` half-bounds over the finite `ZMod N`
(via `choose` + `Finset.sup'`) with the reduction identity and the conductor lemma. Hypotheses:
`Φ` even, `Φ 0 = 0`, `∑ Φ = 0` (the conditions making the pole corrections vanish). -/
theorem exists_norm_completedLFunction_even_le_exp_half {N : ℕ} [NeZero N] {Φ : ZMod N → ℂ}
    (hΦe : Φ.Even) (hΦ0 : Φ 0 = 0) (hΦs : ∑ j, Φ j = 0) :
    ∃ A C : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖ZMod.completedLFunction Φ s‖ ≤ C * Real.exp (A * (‖s‖ * Real.log (‖s‖ + 2))) := by
  choose A C hA0 hb using fun j : ZMod N =>
    exists_norm_completedHurwitzZetaEven₀_le_exp_half (ZMod.toAddCircle j)
  have hC0 : ∀ j, 0 ≤ C j := by
    intro j
    have h := hb j 1 (by norm_num)
    nlinarith [norm_nonneg (completedHurwitzZetaEven₀ (ZMod.toAddCircle j) 1),
      Real.exp_pos (A j * (‖(1 : ℂ)‖ * Real.log (‖(1 : ℂ)‖ + 2)))]
  set Amax := Finset.univ.sup' Finset.univ_nonempty A with hAmax
  have hAmax_ge : ∀ j, A j ≤ Amax := fun j => Finset.le_sup' A (Finset.mem_univ j)
  have hAmax0 : 0 ≤ Amax := le_trans (hA0 _) (hAmax_ge (0 : ZMod N))
  set Ctot := ∑ j : ZMod N, ‖Φ j‖ * C j with hCtot
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  refine ⟨Real.log N / Real.log 2 + Amax, Ctot, by positivity, fun s hs => ?_⟩
  set L := ‖s‖ * Real.log (‖s‖ + 2) with hL
  have hlogs : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg s])
  have hLnn : 0 ≤ L := by rw [hL]; positivity
  rw [completedLFunction_eq_sum_even₀ hΦe hΦ0 hΦs, norm_mul]
  have hsum : ‖∑ j : ZMod N, Φ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖
      ≤ Ctot * Real.exp (Amax * L) := by
    calc ‖∑ j : ZMod N, Φ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖
        ≤ ∑ j : ZMod N, ‖Φ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j : ZMod N, ‖Φ j‖ * (C j * Real.exp (Amax * L)) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          calc ‖completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖
              ≤ C j * Real.exp (A j * L) := hb j s hs
            _ ≤ C j * Real.exp (Amax * L) :=
                mul_le_mul_of_nonneg_left
                  (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hAmax_ge j) hLnn)) (hC0 j)
      _ = Ctot * Real.exp (Amax * L) := by
          rw [hCtot, Finset.sum_mul]; exact Finset.sum_congr rfl (fun j _ => by ring)
  have hkey : Real.log N * ‖s‖ + Amax * L ≤ (Real.log N / Real.log 2 + Amax) * L := by
    have h1 : ‖s‖ * Real.log 2 ≤ L := by
      rw [hL]
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (by norm_num) (by linarith [norm_nonneg s])) (norm_nonneg s)
    have hsL : Real.log N * ‖s‖ ≤ Real.log N / Real.log 2 * L := by
      calc Real.log N * ‖s‖ = Real.log N / Real.log 2 * (‖s‖ * Real.log 2) := by field_simp
        _ ≤ Real.log N / Real.log 2 * L := mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [add_mul]; linarith [hsL]
  calc ‖(N : ℂ) ^ (-s)‖ * ‖∑ j : ZMod N, Φ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖
      ≤ Real.exp (Real.log N * ‖s‖) * (Ctot * Real.exp (Amax * L)) :=
        mul_le_mul (norm_natCast_cpow_neg_le s) hsum (norm_nonneg _) (Real.exp_pos _).le
    _ = Ctot * Real.exp (Real.log N * ‖s‖ + Amax * L) := by rw [Real.exp_add]; ring
    _ ≤ Ctot * Real.exp ((Real.log N / Real.log 2 + Amax) * L) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hkey) ?_
        rw [hCtot]; exact Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hC0 j))

/-- **Even-Φ C₇-order bound on the whole plane.** Extends the `re s ≥ ½` bound to all of `ℂ` via the
ZMod functional equation `completedLFunction Φ (1−s) = N^{s−1}·completedLFunction (𝓕 Φ) s`
(`completedLFunction_one_sub_even`), applied at `1−s`: `completedLFunction Φ s = N^{−s}·completedLFunction
(𝓕 Φ) (1−s)`. The three 𝓕 facts (`dft_even_iff`, `dft_apply_zero`, `dft_dft`) give the half-bound for
`𝓕 Φ` verbatim; `reflect_arith` and the conductor fold `‖1−s‖`/`N^{−s}` into the constants. -/
theorem exists_norm_completedLFunction_even_le_exp {N : ℕ} [NeZero N] {Φ : ZMod N → ℂ}
    (hΦe : Φ.Even) (hΦ0 : Φ 0 = 0) (hΦs : ∑ j, Φ j = 0) :
    ∃ A C : ℝ, ∀ s : ℂ,
      ‖ZMod.completedLFunction Φ s‖ ≤ C * Real.exp (A * (‖s‖ * Real.log (‖s‖ + 2))) := by
  obtain ⟨A, C, hA0, hbΦ⟩ := exists_norm_completedLFunction_even_le_exp_half hΦe hΦ0 hΦs
  have hFe : (ZMod.dft Φ).Even := ZMod.dft_even_iff.mpr hΦe
  have hF0 : ZMod.dft Φ 0 = 0 := by rw [ZMod.dft_apply_zero]; exact hΦs
  have hFs : ∑ j, ZMod.dft Φ j = 0 := by rw [← ZMod.dft_apply_zero, ZMod.dft_dft]; simp [hΦ0]
  obtain ⟨A', C', hA'0, hbF⟩ := exists_norm_completedLFunction_even_le_exp_half hFe hF0 hFs
  obtain ⟨Ar, Br, hAr0, hr⟩ := reflect_arith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hC0 : 0 ≤ C := by
    have := hbΦ 2 (by norm_num)
    nlinarith [norm_nonneg (ZMod.completedLFunction Φ 2),
      Real.exp_pos (A * (‖(2 : ℂ)‖ * Real.log (‖(2 : ℂ)‖ + 2)))]
  have hC'0 : 0 ≤ C' := by
    have := hbF 2 (by norm_num)
    nlinarith [norm_nonneg (ZMod.completedLFunction (ZMod.dft Φ) 2),
      Real.exp_pos (A' * (‖(2 : ℂ)‖ * Real.log (‖(2 : ℂ)‖ + 2)))]
  refine ⟨max A (Real.log N / Real.log 2 + A' * (Ar + 1)), C + C' * Real.exp (A' * Br), fun s => ?_⟩
  set L := ‖s‖ * Real.log (‖s‖ + 2) with hL
  have hlogs : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg s])
  have hLnn : 0 ≤ L := by rw [hL]; positivity
  set Afin := max A (Real.log N / Real.log 2 + A' * (Ar + 1)) with hAfin
  have hAfin_ge_A : A ≤ Afin := le_max_left _ _
  have hAfin_ge_R : Real.log N / Real.log 2 + A' * (Ar + 1) ≤ Afin := le_max_right _ _
  have hexpnn : 0 ≤ Real.exp (Afin * L) := (Real.exp_pos _).le
  have hCC : 0 ≤ C' * Real.exp (A' * Br) := mul_nonneg hC'0 (Real.exp_pos _).le
  rcases le_or_gt (1 / 2 : ℝ) s.re with hs | hs
  · calc ‖ZMod.completedLFunction Φ s‖ ≤ C * Real.exp (A * L) := hbΦ s hs
      _ ≤ (C + C' * Real.exp (A' * Br)) * Real.exp (Afin * L) := by
          have h1 : C * Real.exp (A * L) ≤ C * Real.exp (Afin * L) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hAfin_ge_A hLnn)) hC0
          nlinarith [h1, mul_nonneg hCC hexpnn]
  · have hrefl : ZMod.completedLFunction Φ s
        = (N : ℂ) ^ (-s) * ZMod.completedLFunction (ZMod.dft Φ) (1 - s) := by
      have hfe := ZMod.completedLFunction_one_sub_even hΦe (1 - s) (Or.inr hΦs) (Or.inr hΦ0)
      rw [sub_sub_cancel] at hfe
      rw [hfe]; congr 2; push_cast; ring
    have hre1s : (1 / 2 : ℝ) ≤ (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have hms : ‖1 - s‖ ≤ ‖s‖ + 1 := (norm_sub_le 1 s).trans (by rw [norm_one]; linarith)
    have hrarith : ‖1 - s‖ * Real.log (‖1 - s‖ + 2) ≤ Ar * L + Br := by
      have := hr ‖1 - s‖ ‖s‖ (norm_nonneg s) (norm_nonneg _) hms; rw [hL]; linarith [this]
    have hcond : Real.log N * ‖s‖ ≤ Real.log N / Real.log 2 * L := by
      have h1 : ‖s‖ * Real.log 2 ≤ L := by
        rw [hL]; exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (by norm_num) (by linarith [norm_nonneg s])) (norm_nonneg s)
      calc Real.log N * ‖s‖ = Real.log N / Real.log 2 * (‖s‖ * Real.log 2) := by field_simp
        _ ≤ Real.log N / Real.log 2 * L := mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [hrefl, norm_mul]
    calc ‖(N : ℂ) ^ (-s)‖ * ‖ZMod.completedLFunction (ZMod.dft Φ) (1 - s)‖
        ≤ Real.exp (Real.log N * ‖s‖)
            * (C' * Real.exp (A' * (‖1 - s‖ * Real.log (‖1 - s‖ + 2)))) :=
          mul_le_mul (norm_natCast_cpow_neg_le s) (hbF (1 - s) hre1s) (norm_nonneg _) (Real.exp_pos _).le
      _ = C' * Real.exp (Real.log N * ‖s‖ + A' * (‖1 - s‖ * Real.log (‖1 - s‖ + 2))) := by
          rw [Real.exp_add]; ring
      _ ≤ C' * Real.exp (A' * Br + Afin * L) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC'0
          have hfold : A' * (‖1 - s‖ * Real.log (‖1 - s‖ + 2)) ≤ A' * (Ar * L + Br) :=
            mul_le_mul_of_nonneg_left hrarith hA'0
          have hR : (Real.log N / Real.log 2 + A' * (Ar + 1)) * L ≤ Afin * L :=
            mul_le_mul_of_nonneg_right hAfin_ge_R hLnn
          nlinarith [hcond, hfold, hR, hLnn, hA'0, mul_nonneg hA'0 hLnn]
      _ = (C' * Real.exp (A' * Br)) * Real.exp (Afin * L) := by rw [Real.exp_add]; ring
      _ ≤ (C + C' * Real.exp (A' * Br)) * Real.exp (Afin * L) := by
          nlinarith [mul_nonneg hC0 hexpnn, mul_nonneg hCC hexpnn]

/-- **The even Dirichlet terminal.** For a non-trivial even Dirichlet character `χ`, the completed
Dirichlet L-function has C₇-order (order ≤ 1, maximal type) growth. Via the definitional bridge
`DirichletCharacter.completedLFunction = ZMod.completedLFunction`, with `Φ 0 = 0` from `N ≠ 1`
(derived from `χ ≠ 1`) and `∑ χ = 0` from `sum_eq_zero_of_ne_one`. Scope: `χ ≠ 1`, `χ.Even`. -/
theorem exists_norm_completedLFunction_even_le_exp_dirichlet {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχe : (χ : ZMod N → ℂ).Even) :
    ∃ A C : ℝ, ∀ s : ℂ,
      ‖DirichletCharacter.completedLFunction χ s‖
        ≤ C * Real.exp (A * (‖s‖ * Real.log (‖s‖ + 2))) := by
  have hN : N ≠ 1 := by rintro rfl; exact hχ (Subsingleton.elim _ _)
  have hχ0 : (χ : ZMod N → ℂ) 0 = 0 := χ.map_zero' hN
  have hχs : ∑ j, (χ : ZMod N → ℂ) j = 0 := χ.sum_eq_zero_of_ne_one hχ
  obtain ⟨A, C, hb⟩ := exists_norm_completedLFunction_even_le_exp hχe hχ0 hχs
  exact ⟨A, C, fun s => hb s⟩

end SIDELvConservation

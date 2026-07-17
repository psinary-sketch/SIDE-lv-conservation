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

end SIDELvConservation

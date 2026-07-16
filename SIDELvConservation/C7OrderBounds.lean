import SIDELvConservation.T1_MellinFactorization
import SIDELvConservation.GammaBounds

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

/-- On `Ioi 1`, `‖f_modif t‖ = |evenKernel 0 t − 1|` — the `Ioi 1` indicator piece. -/
theorem norm_f_modif_of_one_lt {t : ℝ} (ht : 1 < t) :
    ‖(hurwitzEvenFEPair 0).f_modif t‖ = |evenKernel 0 t - 1| := by
  have hnotIoo : t ∉ Set.Ioo (0 : ℝ) 1 := fun h => absurd h.2 (not_lt.mpr ht.le)
  simp only [WeakFEPair.f_modif, hurwitzEvenFEPair, Function.comp_apply, Pi.add_apply,
    Set.indicator_of_mem (Set.mem_Ioi.mpr ht), Set.indicator_of_notMem hnotIoo, add_zero,
    if_true]
  rw [show ((evenKernel 0 t : ℝ) : ℂ) - 1 = ((evenKernel 0 t - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]

/-- On `Ioo 0 1`, the theta functional equation folds `f_modif` back to the tail: `‖f_modif t‖ =
t^{−1/2}·|evenKernel 0 (1/t) − 1|`. Uses `evenKernel_functional_equation` + `evenKernel 0 = cosKernel 0`. -/
theorem norm_f_modif_of_mem_Ioo {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ‖(hurwitzEvenFEPair 0).f_modif t‖ = t ^ (-(1 / 2) : ℝ) * |evenKernel 0 (1 / t) - 1| := by
  have ht0 : 0 < t := ht.1
  have hnotIoi : t ∉ Set.Ioi (1 : ℝ) := fun h => absurd h (not_lt.mpr ht.2.le)
  have hfe : evenKernel 0 t = t ^ (-(1 / 2) : ℝ) * evenKernel 0 (1 / t) := by
    rw [evenKernel_functional_equation, evenKernel_eq_cosKernel_of_zero, one_div,
      ← Real.rpow_neg ht0.le, one_div]
  simp only [WeakFEPair.f_modif, hurwitzEvenFEPair, Function.comp_apply, Pi.add_apply,
    Set.indicator_of_notMem hnotIoi, Set.indicator_of_mem ht, zero_add, one_mul, smul_eq_mul,
    mul_one]
  rw [show ((evenKernel 0 t : ℝ) : ℂ) - ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)
      = ((evenKernel 0 t - t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, hfe]
  rw [show t ^ (-(1 / 2) : ℝ) * evenKernel 0 (1 / t) - t ^ (-(1 / 2) : ℝ)
      = t ^ (-(1 / 2) : ℝ) * (evenKernel 0 (1 / t) - 1) by ring, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ht0.le _)]

/-- **Scaled-Γ tail integrability.** For `0 < a`, `0 < p`, the integrand `t^{a−1}·e^{−pt}` is
integrable on `Ioi 0` — from `Real.GammaIntegral_convergent` via the `t ↦ p·t` scaling, proved
set-level (positive `t` only) so `Real.mul_rpow` applies and the `rpow`-of-negatives class never fires. -/
theorem integrableOn_rpow_mul_exp_Ioi {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(p * t))) (Set.Ioi 0) := by
  have key : MeasureTheory.IntegrableOn
      (fun x : ℝ => (p * x) ^ (a - 1) * Real.exp (-(p * x))) (Set.Ioi 0) := by
    have h := (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => u ^ (a - 1) * Real.exp (-u)) 0 hp).mpr
    rw [mul_zero] at h
    exact h (by simpa only [mul_comm] using Real.GammaIntegral_convergent ha)
  have hpne : (p : ℝ) ^ (a - 1) ≠ 0 := by positivity
  have heq : Set.EqOn (fun x : ℝ => (p ^ (a - 1))⁻¹ * ((p * x) ^ (a - 1) * Real.exp (-(p * x))))
      (fun t : ℝ => t ^ (a - 1) * Real.exp (-(p * t))) (Set.Ioi 0) := by
    intro t ht
    rw [Set.mem_Ioi] at ht
    dsimp only
    rw [Real.mul_rpow hp.le ht.le, mul_assoc, inv_mul_cancel_left₀ hpne]
  exact MeasureTheory.IntegrableOn.congr_fun (key.const_mul (p ^ (a - 1))⁻¹) heq measurableSet_Ioi

/-- **`Ioi 1` Γ-bound.** The growth-carrying tail: `∫_{Ioi 1} t^{x−1}·‖f_modif t‖ ≤ Cd·(1/p)^{x₊}·Γ x₊`
with `x₊ = max x 1`. On `Ioi 1`, `‖f_modif t‖ = |ek 0 t − 1| ≤ Cd·e^{−pt}` (domination) and
`t^{x−1} ≤ t^{x₊−1}` (t ≥ 1), then `∫_{Ioi 1} ≤ ∫_{Ioi 0} = (1/p)^{x₊}·Γ x₊`. The `x₊` keeps the Γ
argument `≥ 1` regardless of sign of `x`. -/
theorem norm_f_modif_ioi_one_integral_le {p Cd x : ℝ} (hp : 0 < p) (hCd : 0 ≤ Cd)
    (hdom : ∀ t : ℝ, 1 ≤ t → |evenKernel 0 t - 1| ≤ Cd * Real.exp (-(p * t)))
    (hint : MeasureTheory.IntegrableOn
      (fun t => t ^ (x - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) (Set.Ioi 1)) :
    (∫ t in Set.Ioi (1 : ℝ), t ^ (x - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
      ≤ Cd * (1 / p) ^ (max x 1) * Real.Gamma (max x 1) := by
  set y := max x 1 with hy
  have hy1 : (1 : ℝ) ≤ y := le_max_right _ _
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
  have hyx : x ≤ y := le_max_left _ _
  have hR0 : MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (y - 1) * Real.exp (-(p * t))) (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_Ioi hy0 hp
  have hRint : MeasureTheory.IntegrableOn
      (fun t : ℝ => Cd * (t ^ (y - 1) * Real.exp (-(p * t)))) (Set.Ioi 1) :=
    (hR0.mono_set (Set.Ioi_subset_Ioi zero_le_one)).const_mul Cd
  calc (∫ t in Set.Ioi (1 : ℝ), t ^ (x - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
      ≤ ∫ t in Set.Ioi (1 : ℝ), Cd * (t ^ (y - 1) * Real.exp (-(p * t))) := by
        refine MeasureTheory.setIntegral_mono_on hint hRint measurableSet_Ioi (fun t ht => ?_)
        rw [Set.mem_Ioi] at ht
        rw [norm_f_modif_of_one_lt ht]
        have h1 : |evenKernel 0 t - 1| ≤ Cd * Real.exp (-(p * t)) := hdom t ht.le
        have h2 : t ^ (x - 1) ≤ t ^ (y - 1) :=
          Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)
        calc t ^ (x - 1) * |evenKernel 0 t - 1|
            ≤ t ^ (y - 1) * (Cd * Real.exp (-(p * t))) :=
              mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
          _ = Cd * (t ^ (y - 1) * Real.exp (-(p * t))) := by ring
    _ = Cd * ∫ t in Set.Ioi (1 : ℝ), t ^ (y - 1) * Real.exp (-(p * t)) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ Cd * ∫ t in Set.Ioi (0 : ℝ), t ^ (y - 1) * Real.exp (-(p * t)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCd
        refine MeasureTheory.setIntegral_mono_set hR0 ?_ ?_
        · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
          rw [Set.mem_Ioi] at ht
          positivity
        · exact (HasSubset.Subset.eventuallyLE (Set.Ioi_subset_Ioi zero_le_one))
    _ = Cd * ((1 / p) ^ y * Real.Gamma y) := by rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hy0 hp]
    _ = Cd * (1 / p) ^ y * Real.Gamma y := by ring

/-- **`Ioo 0 1` bound by a fixed majorant.** For `re s ≥ ½` (so `x ≥ ¼`), the head integral is
uniformly `≤ M₀ := ∫_{Ioo 0 1} t^{−3/4}·‖f_modif t‖` — a constant independent of `s`. The sign-flip
`t^{x−1} ≤ t^{−3/4}` holds precisely because `t < 1` and `x−1 ≥ −3/4`. -/
theorem norm_f_modif_ioo_integral_le {x : ℝ} (hx : (1 : ℝ) / 4 ≤ x)
    (hint : MeasureTheory.IntegrableOn
      (fun t => t ^ (x - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) (Set.Ioo 0 1))
    (hmaj : MeasureTheory.IntegrableOn
      (fun t => t ^ (-(3 : ℝ) / 4) * ‖(hurwitzEvenFEPair 0).f_modif t‖) (Set.Ioo 0 1)) :
    (∫ t in Set.Ioo (0 : ℝ) 1, t ^ (x - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
      ≤ ∫ t in Set.Ioo (0 : ℝ) 1, t ^ (-(3 : ℝ) / 4) * ‖(hurwitzEvenFEPair 0).f_modif t‖ := by
  refine MeasureTheory.setIntegral_mono_on hint hmaj measurableSet_Ioo (fun t ht => ?_)
  have h : t ^ (x - 1) ≤ t ^ (-(3 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2.le (by linarith)
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

/-- **Γ→exp.** For `1 ≤ y`, `Γ y ≤ exp(2·y·log(y+2))` — feeding `Real.Gamma_le_two_mul_rpow` into
the corrected conjunct's `exp(A·…·log(…))` shape. The `y = 1` boundary (where the rpow base is `0`)
is case-split off before the log manipulation. -/
theorem Gamma_le_exp {y : ℝ} (hy : 1 ≤ y) :
    Real.Gamma y ≤ Real.exp (2 * y * Real.log (y + 2)) := by
  rcases eq_or_lt_of_le hy with rfl | hy1
  · rw [Real.Gamma_one]
    exact Real.one_le_exp_iff.mpr (by nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 1 + 2 by norm_num)])
  · have hy1' : (0 : ℝ) < y - 1 := by linarith
    refine (Real.Gamma_le_two_mul_rpow hy).trans ?_
    rw [← Real.exp_log (show (0 : ℝ) < 2 * (2 * (y - 1) / Real.exp 1) ^ (y - 1) by positivity)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by positivity),
      Real.log_div (by positivity) (Real.exp_ne_zero _), Real.log_exp,
      Real.log_mul (by norm_num) (by linarith)]
    have hl2 : Real.log 2 ≤ Real.log (y + 2) := Real.log_le_log (by norm_num) (by linarith)
    have hly : Real.log (y - 1) ≤ Real.log (y + 2) := Real.log_le_log (by linarith) (by linarith)
    have hlp : (0 : ℝ) ≤ Real.log (y + 2) := Real.log_nonneg (by linarith)
    have hy10 : (0 : ℝ) ≤ y - 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hl2 hy10, mul_le_mul_of_nonneg_left hly hy10, hlp, hy10]

/-- **Arithmetic glue (sub-lemma 5).** For `K ≥ 0`, `w·(K + 2·log(w+2))` with `1 ≤ w ≤ n/2+1` fits
inside `A·(n·log(n+2)) + B` — `n = ‖s‖`, `w = x₊`. The trick that defeats the `n≈0` case-behavior:
convert every linear term to a log term through the uniform `log(n+2) ≥ log 2 > 0`, so no case split
is needed. The residual log term is absorbed by `log(n+2) ≤ n+1` (`Real.log_le_sub_one_of_pos` —
the same `log u ≤ u−1` that killed complex Stirling). No `nlinarith`, no cases. -/
theorem exp_arg_bound {K : ℝ} (hK : 0 ≤ K) : ∃ A B : ℝ, 0 ≤ A ∧ ∀ n w : ℝ,
    0 ≤ n → 1 ≤ w → w ≤ n / 2 + 1 →
      w * (K + 2 * Real.log (w + 2)) ≤ A * (n * Real.log (n + 2)) + B := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2ne : Real.log 2 ≠ 0 := hlog2.ne'
  refine ⟨(K + 4) / Real.log 2 + 4, K + 4, by positivity, fun n w hn hw hwn => ?_⟩
  have hlp : 0 ≤ Real.log (n + 2) := Real.log_nonneg (by linarith)
  have hl2 : Real.log 2 ≤ Real.log (n + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hlwp : 0 ≤ Real.log (w + 2) := Real.log_nonneg (by linarith)
  have hlw : Real.log (w + 2) ≤ 2 * Real.log (n + 2) := by
    calc Real.log (w + 2) ≤ Real.log ((n + 2) ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log (n + 2) := by rw [Real.log_pow]; push_cast; ring
  have hlub : Real.log (n + 2) ≤ n + 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n + 2 by linarith); linarith
  have hn_conv : n * Real.log 2 ≤ n * Real.log (n + 2) := mul_le_mul_of_nonneg_left hl2 hn
  have hw1 : w ≤ n + 1 := by linarith
  have step1 : w * (K + 2 * Real.log (w + 2)) ≤ (n + 1) * (K + 4 * Real.log (n + 2)) :=
    mul_le_mul hw1 (by linarith) (by linarith) (by linarith)
  have hKn : K * n ≤ (K / Real.log 2) * (n * Real.log (n + 2)) := by
    calc K * n = (K / Real.log 2) * (n * Real.log 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hn_conv (by positivity)
  have h4n : (4 : ℝ) * n ≤ (4 / Real.log 2) * (n * Real.log (n + 2)) := by
    calc (4 : ℝ) * n = (4 / Real.log 2) * (n * Real.log 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hn_conv (by positivity)
  calc w * (K + 2 * Real.log (w + 2))
      ≤ (n + 1) * (K + 4 * Real.log (n + 2)) := step1
    _ = K * n + K + 4 * (n * Real.log (n + 2)) + 4 * Real.log (n + 2) := by ring
    _ ≤ (K / Real.log 2) * (n * Real.log (n + 2)) + K + 4 * (n * Real.log (n + 2))
          + ((4 / Real.log 2) * (n * Real.log (n + 2)) + 4) := by
        have h1 : 4 * Real.log (n + 2) ≤ 4 * (n + 1) := by linarith
        linarith [hKn, h4n, h1]
    _ = ((K + 4) / Real.log 2 + 4) * (n * Real.log (n + 2)) + (K + 4) := by field_simp; ring

/-- **Growth bound on the right half-plane** `re s ≥ ½`: `∃ A C, ‖Λ₀ s‖ ≤ C·exp(A·‖s‖·log(‖s‖+2))`.
Wires: framework integrability (`toStrongFEPair.hasMellin`), domination (`exists_norm_Phi_le`), the
`Ioi 0 = Ioc 0 1 ∪ Ioi 1` split, the two piece-bounds, `(1/p)^{x₊} = exp(log(1/p)·x₊)`, `Gamma_le_exp`,
and `exp_arg_bound`. -/
theorem exists_norm_completedRiemannZeta₀_le_exp_half :
    ∃ A C : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖completedRiemannZeta₀ s‖ ≤ C * Real.exp (A * (‖s‖ * Real.log (‖s‖ + 2))) := by
  obtain ⟨p, Cφ, hp, hφ⟩ := exists_norm_Phi_le
  obtain ⟨A₀, B₀, hA₀0, hA₀⟩ := exp_arg_bound (show (0 : ℝ) ≤ |Real.log (1 / p)| from abs_nonneg _)
  have hCφ : 0 ≤ Cφ := by
    by_contra hc; push_neg at hc
    have h := (hφ 1 le_rfl).trans' (norm_nonneg _)
    linarith [mul_neg_of_neg_of_pos hc (Real.exp_pos (-p * 1))]
  have hintg : ∀ w : ℂ, MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (w.re - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) (Set.Ioi 0) := fun w => by
    have h : MeasureTheory.IntegrableOn
        (fun t : ℝ => ‖(t : ℂ) ^ (w - 1) • (hurwitzEvenFEPair 0).f_modif t‖) (Set.Ioi 0) :=
      (((hurwitzEvenFEPair 0).toStrongFEPair.hasMellin w).1).norm
    refine MeasureTheory.IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
    rw [Set.mem_Ioi] at ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  have hdom : ∀ t : ℝ, 1 ≤ t → |evenKernel 0 t - 1| ≤ 2 * Cφ * Real.exp (-(p * t)) := fun t ht => by
    have h := hφ t ht
    have hPhi : ‖Phi t‖ = |evenKernel 0 t - 1| / 2 := by
      rw [Phi, show ((evenKernel 0 t : ℂ) - 1) = ((evenKernel 0 t - 1 : ℝ) : ℂ) by push_cast; ring,
        norm_div, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    rw [hPhi] at h
    rw [show -(p * t) = -p * t by ring]
    nlinarith [h, Real.exp_pos (-p * t)]
  have hmajint : MeasureTheory.IntegrableOn
      (fun t => t ^ (-(3 : ℝ) / 4) * ‖(hurwitzEvenFEPair 0).f_modif t‖) (Set.Ioo 0 1) := by
    refine MeasureTheory.IntegrableOn.congr_fun ((hintg (1 / 4 : ℂ)).mono_set Set.Ioo_subset_Ioi_self)
      (fun t _ => ?_) measurableSet_Ioo
    norm_num
  set M₀ := ∫ t in Set.Ioo (0 : ℝ) 1, t ^ (-(3 : ℝ) / 4) * ‖(hurwitzEvenFEPair 0).f_modif t‖ with hM₀
  have hM₀0 : 0 ≤ M₀ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => by have := ht.1; positivity)
  refine ⟨A₀, 2⁻¹ * M₀ + Cφ * Real.exp B₀, hA₀0, fun s hs => ?_⟩
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
  have hsplit : (∫ t in Set.Ioi (0 : ℝ), t ^ (x - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
      = (∫ t in Set.Ioo (0 : ℝ) 1, t ^ (x - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
        + ∫ t in Set.Ioi (1 : ℝ), t ^ (x - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖ := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one),
      MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        ((hintg (s / 2)).mono_set Set.Ioc_subset_Ioi_self)
        ((hintg (s / 2)).mono_set (Set.Ioi_subset_Ioi zero_le_one)),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hIoo : (∫ t in Set.Ioo (0 : ℝ) 1, t ^ (x - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) ≤ M₀ :=
    norm_f_modif_ioo_integral_le hx14 ((hintg (s / 2)).mono_set Set.Ioo_subset_Ioi_self) hmajint
  have hIoi : (∫ t in Set.Ioi (1 : ℝ), t ^ (x - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖)
      ≤ 2 * Cφ * (1 / p) ^ y * Real.Gamma y :=
    norm_f_modif_ioi_one_integral_le hp (by positivity) hdom
      ((hintg (s / 2)).mono_set (Set.Ioi_subset_Ioi zero_le_one))
  have hgexp : (1 / p) ^ y * Real.Gamma y
      ≤ Real.exp (|Real.log (1 / p)| * y + 2 * y * Real.log (y + 2)) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.exp_add]
    refine mul_le_mul ?_ (Gamma_le_exp hy1) (Real.Gamma_nonneg_of_nonneg hy0.le) (Real.exp_pos _).le
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hy0.le
  calc ‖completedRiemannZeta₀ s‖
      ≤ (∫ t in Set.Ioi (0 : ℝ), t ^ (x - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) / 2 :=
        norm_completedRiemannZeta₀_le s
    _ ≤ (M₀ + 2 * Cφ * (1 / p) ^ y * Real.Gamma y) / 2 := by rw [hsplit]; gcongr
    _ = 2⁻¹ * M₀ + Cφ * ((1 / p) ^ y * Real.Gamma y) := by ring
    _ ≤ (2⁻¹ * M₀ + Cφ * Real.exp B₀) * Real.exp (A₀ * (‖s‖ * Real.log (‖s‖ + 2))) := by
        have hexp1 : (1 : ℝ) ≤ Real.exp (A₀ * (‖s‖ * Real.log (‖s‖ + 2))) :=
          Real.one_le_exp (by
            have : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg s]); positivity)
        have hmain : (1 / p) ^ y * Real.Gamma y
            ≤ Real.exp B₀ * Real.exp (A₀ * (‖s‖ * Real.log (‖s‖ + 2))) := by
          refine hgexp.trans ?_
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by have := hA₀ ‖s‖ y (norm_nonneg s) hy1 hys; nlinarith [this])
        rw [add_mul]
        refine add_le_add (le_mul_of_one_le_right (by positivity) hexp1) ?_
        calc Cφ * ((1 / p) ^ y * Real.Gamma y)
            ≤ Cφ * (Real.exp B₀ * Real.exp (A₀ * (‖s‖ * Real.log (‖s‖ + 2)))) :=
              mul_le_mul_of_nonneg_left hmain hCφ
          _ = Cφ * Real.exp B₀ * Real.exp (A₀ * (‖s‖ * Real.log (‖s‖ + 2))) := by ring

/-- Reflection arithmetic: `m·log(m+2)` for `0 ≤ m ≤ z+1` fits inside `A·(z·log(z+2)) + B`. Same
staged linear-to-log conversion as `exp_arg_bound`; used to fold `‖1-s‖ ≤ ‖s‖+1` into the constants. -/
theorem reflect_arith : ∃ A B : ℝ, 0 ≤ A ∧ ∀ m z : ℝ,
    0 ≤ z → 0 ≤ m → m ≤ z + 1 → m * Real.log (m + 2) ≤ A * (z * Real.log (z + 2)) + B := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 + 2 / Real.log 2, 2, by positivity, fun m z hz hm hmz => ?_⟩
  have hlp : 0 ≤ Real.log (z + 2) := Real.log_nonneg (by linarith)
  have hl2 : Real.log 2 ≤ Real.log (z + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hlm : Real.log (m + 2) ≤ 2 * Real.log (z + 2) := by
    calc Real.log (m + 2) ≤ Real.log ((z + 2) ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log (z + 2) := by rw [Real.log_pow]; push_cast; ring
  have hlub : Real.log (z + 2) ≤ z + 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < z + 2 by linarith); linarith
  have hz_conv : z * Real.log 2 ≤ z * Real.log (z + 2) := mul_le_mul_of_nonneg_left hl2 hz
  have h2z : (2 : ℝ) * z ≤ (2 / Real.log 2) * (z * Real.log (z + 2)) := by
    calc (2 : ℝ) * z = (2 / Real.log 2) * (z * Real.log 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hz_conv (by positivity)
  calc m * Real.log (m + 2)
      ≤ (z + 1) * (2 * Real.log (z + 2)) :=
        mul_le_mul hmz hlm (Real.log_nonneg (by linarith)) (by linarith)
    _ = 2 * (z * Real.log (z + 2)) + 2 * Real.log (z + 2) := by ring
    _ ≤ 2 * (z * Real.log (z + 2)) + ((2 / Real.log 2) * (z * Real.log (z + 2)) + 2) := by
        have h1 : 2 * Real.log (z + 2) ≤ 2 * (z + 1) := by linarith
        linarith [h2z, h1]
    _ = (2 + 2 / Real.log 2) * (z * Real.log (z + 2)) + 2 := by field_simp; ring

/-- **C₇-order growth, all of `ℂ`.** `∃ A C, ∀ s, ‖Λ₀ s‖ ≤ C·exp(A·‖s‖·log(‖s‖+2))`. Extends the
`re s ≥ ½` bound to the whole plane by the functional equation `Λ₀(s) = Λ₀(1-s)`, folding
`‖1-s‖ ≤ ‖s‖+1` into `A, C` via `reflect_arith`. This is the corrected C₇-order growth conjunct. -/
theorem exists_norm_completedRiemannZeta₀_le_exp :
    ∃ A C : ℝ, ∀ s : ℂ, ‖completedRiemannZeta₀ s‖
      ≤ C * Real.exp (A * (‖s‖ * Real.log (‖s‖ + 2))) := by
  obtain ⟨A, C, hA0, hb⟩ := exists_norm_completedRiemannZeta₀_le_exp_half
  obtain ⟨A₁, B₁, hA₁0, hr⟩ := reflect_arith
  have hC0 : 0 ≤ C := by
    by_contra hc; push_neg at hc
    have h := (hb 1 (by norm_num)).trans' (norm_nonneg _)
    nlinarith [Real.exp_pos (A * (‖(1 : ℂ)‖ * Real.log (‖(1 : ℂ)‖ + 2)))]
  refine ⟨A * (A₁ + 1), C * (Real.exp (A * B₁) + 1), fun s => ?_⟩
  have hnn : 0 ≤ ‖s‖ := norm_nonneg _
  have hlogpos : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith)
  rcases le_or_gt (1 / 2) s.re with hs | hs
  · refine (hb s hs).trans ?_
    have h1 : Real.exp (A * (‖s‖ * Real.log (‖s‖ + 2)))
        ≤ Real.exp (A * (A₁ + 1) * (‖s‖ * Real.log (‖s‖ + 2))) :=
      Real.exp_le_exp.mpr (by
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hA0 hA₁0) hnn) hlogpos])
    calc C * Real.exp (A * (‖s‖ * Real.log (‖s‖ + 2)))
        ≤ C * Real.exp (A * (A₁ + 1) * (‖s‖ * Real.log (‖s‖ + 2))) :=
          mul_le_mul_of_nonneg_left h1 hC0
      _ ≤ C * (Real.exp (A * B₁) + 1) * Real.exp (A * (A₁ + 1) * (‖s‖ * Real.log (‖s‖ + 2))) :=
          mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right hC0 (by nlinarith [Real.exp_pos (A * B₁)]))
            (Real.exp_pos _).le
  · rw [← completedRiemannZeta₀_one_sub s]
    have h1s : (1 / 2 : ℝ) ≤ (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    refine (hb (1 - s) h1s).trans ?_
    have hms : ‖1 - s‖ ≤ ‖s‖ + 1 := (norm_sub_le 1 s).trans (by rw [norm_one]; linarith)
    have hkey : A * (‖1 - s‖ * Real.log (‖1 - s‖ + 2))
        ≤ A * B₁ + A * (A₁ + 1) * (‖s‖ * Real.log (‖s‖ + 2)) := by
      have := hr ‖1 - s‖ ‖s‖ hnn (norm_nonneg _) hms
      nlinarith [mul_le_mul_of_nonneg_left this hA0, hA0, hA₁0, mul_nonneg hnn hlogpos]
    calc C * Real.exp (A * (‖1 - s‖ * Real.log (‖1 - s‖ + 2)))
        ≤ C * Real.exp (A * B₁ + A * (A₁ + 1) * (‖s‖ * Real.log (‖s‖ + 2))) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hkey) hC0
      _ = C * Real.exp (A * B₁) * Real.exp (A * (A₁ + 1) * (‖s‖ * Real.log (‖s‖ + 2))) := by
          rw [Real.exp_add]; ring
      _ ≤ C * (Real.exp (A * B₁) + 1) * Real.exp (A * (A₁ + 1) * (‖s‖ * Real.log (‖s‖ + 2))) := by
          gcongr
          · nlinarith [Real.exp_pos (A * B₁)]

end SIDELvConservation

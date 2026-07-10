import Mathlib.Analysis.MellinTransform
import SIDELvConservation.T1_MellinFactorization

/-!
# T2 — s-darkness extension (no-other-channel)

The load-bearing content is not a new fact about `mellin`; it is a naming
of Mathlib's `mellin` definition as an *exhaustion statement*: the value
of `mellin Φ s` is a function of two inputs — the function `Φ` on `Ioi 0`
and the kernel `t ^ (s - 1)`.  No third input.  Consequences:

* **Congruence.**  `Φ₁ = Φ₂` on `Ioi 0` ⇒ `mellin Φ₁ s = mellin Φ₂ s` for
  every `s`.  This is the trivial half.
* **Exhaustion.**  Any predicate on `Φ` alone — in particular any
  constraint the product formula imposes on `Φ` — factors through `Φ`,
  hence is s-independent.  This is the substantive half.

Joined with T1: constraints on the pre-image `Phi` of the Mellin
factorization cannot select among values of `s`.  T3 will use exactly
this to reject the "combinations of classes could produce s-side effects"
alternative.
-/

namespace SIDELvConservation

open Complex Set MeasureTheory

/-- **T2a (congruence, trivial half).**  If two integrands agree on `Ioi 0`,
their Mellin transforms agree at every `s`. -/
theorem T2a_mellin_congr_on_Ioi
    (Φ₁ Φ₂ : ℝ → ℂ) (h : Set.EqOn Φ₁ Φ₂ (Ioi 0)) (s : ℂ) :
    mellin Φ₁ s = mellin Φ₂ s := by
  unfold mellin
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  simp only [h ht]

/-- **T2a′ (congruence, ambient form).**  If `Φ₁ = Φ₂` as functions, the
Mellin transforms agree at every `s`.  Kept alongside `T2a_mellin_congr_on_Ioi`
because the product formula constrains `Phi` as a genuine function of `t`,
not merely on `Ioi 0`. -/
theorem T2a'_mellin_congr
    (Φ₁ Φ₂ : ℝ → ℂ) (h : Φ₁ = Φ₂) (s : ℂ) :
    mellin Φ₁ s = mellin Φ₂ s := by
  subst h; rfl

/-- **T2b (exhaustion / no-other-channel).**  The Mellin transform value at
`s` is *literally* the `Ioi 0`-integral of `Φ` against the kernel
`t ^ (s - 1)`.  No further inputs enter.  Elevated from Mathlib's `mellin`
definition to a named theorem so the argument can cite it directly. -/
theorem T2b_mellin_exhaustion (Φ : ℝ → ℂ) (s : ℂ) :
    mellin Φ s = ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) • Φ t := rfl

/-- **T2c (s-darkness of `Φ`-side predicates).**  Any predicate `P` that
depends only on `Φ` (as a function) is s-independent when transported
across `mellin`.  Formally: if `P` holds for `Φ`, then any equality
`Φ₁ = Φ₂` (respecting `P` or not) forces `mellin Φ₁ s = mellin Φ₂ s`.

The proof is one line, but the *statement* is the mathematical content:
constraints on `Φ` cannot select among values of `s`, because the
information `s` carries never touches `Φ`. -/
theorem T2c_phi_side_predicates_are_s_dark
    (P : (ℝ → ℂ) → Prop) (Φ₁ Φ₂ : ℝ → ℂ) (hEq : Φ₁ = Φ₂)
    (_hP : P Φ₁) (s : ℂ) :
    mellin Φ₁ s = mellin Φ₂ s :=
  T2a'_mellin_congr Φ₁ Φ₂ hEq s

/-- The concrete factorization at a specific `s` in the convergence
half-plane.  This is T1's definitional chain, applied to a fixed `s`;
extracted so downstream targets (T2d, T3) can use it without invoking
`Classical.choose`. -/
theorem completedRiemannZeta_eq_mellinPhi
    (s : ℂ) (hs : 1 < s.re) :
    completedRiemannZeta s = mellin Phi (s / 2) := by
  have hRe : (1 : ℝ) / 2 < (s / 2).re := by
    have hE : (s / 2).re = s.re / 2 := by simp
    rw [hE]; linarith
  have hMel :=
    ((HurwitzZeta.hurwitzEvenFEPair 0).hasMellin (s := s / 2)
      (by exact_mod_cast hRe)).2
  have hMel' :
      mellin (fun t => ((HurwitzZeta.evenKernel 0 t : ℂ) - 1)) (s / 2)
        = (HurwitzZeta.hurwitzEvenFEPair 0).Λ (s / 2) := by
    have hFun :
        (fun t => ((HurwitzZeta.hurwitzEvenFEPair 0).f t
                  - (HurwitzZeta.hurwitzEvenFEPair 0).f₀))
          = (fun t => ((HurwitzZeta.evenKernel 0 t : ℂ) - 1)) := by
      funext t
      show ((Complex.ofReal ∘ HurwitzZeta.evenKernel 0) t
              - (if (0 : UnitAddCircle) = 0 then (1 : ℂ) else 0))
            = ((HurwitzZeta.evenKernel 0 t : ℂ) - 1)
      simp
    rw [← hFun]; exact hMel
  have hLHS : completedRiemannZeta s
      = ((HurwitzZeta.hurwitzEvenFEPair 0).Λ (s / 2)) / 2 := rfl
  have hDivConst :
      mellin (fun t => ((HurwitzZeta.evenKernel 0 t : ℂ) - 1) / 2) (s / 2)
        = mellin (fun t => (HurwitzZeta.evenKernel 0 t : ℂ) - 1) (s / 2) / 2 :=
    mellin_div_const _ _ _
  show completedRiemannZeta s = mellin Phi (s / 2)
  rw [hLHS, ← hMel', ← hDivConst]
  rfl

/-- **T2d (joint with T1).**  For `1 < re s`, the zero locations of
`completedRiemannZeta` coincide with the zero locations of the Mellin
transform of `Phi` at `s / 2`.  Packages T1 in the form T3 will consume:
the zero-set of `s ↦ completedRiemannZeta s` on the convergence
half-plane is a function of `Phi` alone through `mellin`. -/
theorem T2d_zero_iff_mellinPhi_zero
    (s : ℂ) (hs : 1 < s.re) :
    completedRiemannZeta s = 0 ↔ mellin Phi (s / 2) = 0 := by
  rw [completedRiemannZeta_eq_mellinPhi s hs]

end SIDELvConservation

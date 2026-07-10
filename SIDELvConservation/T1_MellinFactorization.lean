import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.MellinTransform

/-!
# T1 — Mellin factorization of the completed Riemann zeta

Statement (kernel-verified content):
There exists a fixed function `Φ : ℝ → ℂ`, defined without reference to `s`,
such that for every `s` with `1 < re s`,

  `completedRiemannZeta s = mellin Φ (s / 2)`.

This restates Mathlib's Mellin/theta construction of `completedRiemannZeta`
as an explicit factorization: `s` enters only through the Mellin kernel
`t ^ (s - 1)`.  All content in Mathlib names — no new mathematics required,
which is the point.
-/

namespace SIDELvConservation

open Complex HurwitzZeta Set MeasureTheory

/-- The (fixed) Mellin integrand whose Mellin transform at `s / 2` reproduces
`completedRiemannZeta s` on the convergence half-plane. -/
noncomputable def Phi : ℝ → ℂ := fun t => ((evenKernel 0 t : ℂ) - 1) / 2

/-- **T1 (Mellin factorization).**  The completed Riemann zeta function
factors through the Mellin transform of the fixed function `Phi` under the
half-argument shift.  For `1 < re s`,

  `completedRiemannZeta s = mellin Phi (s / 2)`.

The witness `Phi` is defined without reference to `s`; on the RHS `s` enters
only through the Mellin kernel `t ^ (s/2 - 1)`. -/
theorem T1_completedRiemannZeta_factors_through_mellin :
    ∃ Φ : ℝ → ℂ, ∀ s : ℂ, 1 < s.re →
      completedRiemannZeta s = mellin Φ (s / 2) := by
  refine ⟨Phi, fun s hs => ?_⟩
  -- Rewrite the LHS via Mathlib's definitional chain.
  --   completedRiemannZeta s
  -- = completedHurwitzZetaEven 0 s                            (def-eq, rfl)
  -- = ((hurwitzEvenFEPair 0).Λ (s/2)) / 2                     (def-eq, rfl)
  have hRe : (1 : ℝ) / 2 < (s / 2).re := by
    have hE : (s / 2).re = s.re / 2 := by simp
    rw [hE]; linarith
  -- `WeakFEPair.hasMellin` at `s / 2` for `hurwitzEvenFEPair 0`:
  --   mellin ((hurwitzEvenFEPair 0).f · - (hurwitzEvenFEPair 0).f₀) (s/2)
  --     = (hurwitzEvenFEPair 0).Λ (s / 2).
  have hMel :=
    ((hurwitzEvenFEPair 0).hasMellin (s := s / 2) (by exact_mod_cast hRe)).2
  -- The projections of `hurwitzEvenFEPair 0` are `f = ofReal ∘ evenKernel 0`
  -- and `f₀ = 1` (the `if` branch on `a = 0` is `1`), all definitionally.
  -- Cast `hMel` into the concrete form we need.
  have hMel' :
      mellin (fun t => ((evenKernel 0 t : ℂ) - 1)) (s / 2)
        = (hurwitzEvenFEPair 0).Λ (s / 2) := by
    have : (fun t => ((hurwitzEvenFEPair 0).f t - (hurwitzEvenFEPair 0).f₀))
              = (fun t => ((evenKernel 0 t : ℂ) - 1)) := by
      funext t
      show ((ofReal ∘ evenKernel 0) t - (if (0 : UnitAddCircle) = 0 then 1 else 0))
          = ((evenKernel 0 t : ℂ) - 1)
      simp
    rw [← this]; exact hMel
  -- Now build the RHS mellin of `Phi` from `hMel'` via `mellin_div_const`.
  have hDivConst :
      mellin (fun t => ((evenKernel 0 t : ℂ) - 1) / 2) (s / 2)
        = mellin (fun t => (evenKernel 0 t : ℂ) - 1) (s / 2) / 2 :=
    mellin_div_const _ _ _
  -- Assemble.
  show completedRiemannZeta s = mellin Phi (s / 2)
  have hLHS : completedRiemannZeta s
      = ((hurwitzEvenFEPair 0).Λ (s / 2)) / 2 := rfl
  rw [hLHS, ← hMel', ← hDivConst]
  rfl

end SIDELvConservation

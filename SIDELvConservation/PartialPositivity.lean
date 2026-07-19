import SIDELvConservation.RegisterPentagon
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Partial-positivity interface — statements frozen (item (iv), sitting one)

**STATEMENT-ONLY (B1 pattern — statement commit separate from discharge).**  This module
freezes the ξ-pattern interface that certifies **finite-range** Li positivity from verified
zeros, hanging on the pentagon's R4 face (`RegisterPentagon.Register4_positivity`).  It does
NOT close RH — the all-n tail stays the open gap.  Grade (expected at discharge):
**INTERFACES**, two classical named premises + one external-computation premise; no `sorry`
(the premises are hypothesis arguments), census stays exactly two intended sites.

Classical shape (Bombieri–Lagarias 1999; Voros 2004–06): the Li coefficient is the sum over
nontrivial zeros `λ_n = Σ_ρ Re[1 − (1 − 1/ρ)^n]`; an off-line zero at height `H` registers in
`λ_n` only for `n ≳ 2H²` (equivalently `|Im ρ| ≲ √(n/2)` — the census-resolved constant,
BALANCE_AND_POSITIVITY C.6/C.8, SCREENED from the literature form, not recalled).  Hence
zeros verified on the line up to height `T` certify `λ_n ≥ 0` for `n ≤ N₀(T) ≈ 2T²`.

**`li_bench300`'s role** (docstring, not a kernel object): the `n = 300` numeric measurement
sits far inside `N₀(T)` for any verified `T ≥ 10^6` (`N₀(10^6) = 2×10^12 ≫ 300`), so the
bench is a *checkable instance* of the compiled finite-range result — not its frontier.
-/

namespace SIDELvConservation
namespace PartialPositivity

open Complex
open scoped Classical

/-- Nontrivial zeros of ζ in the critical strip — the index set for the explicit-formula
sum over zeros. -/
def NontrivialZero : Type := {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}

/-- The Bombieri–Lagarias summand at a nontrivial zero `ρ`: `Re[1 − (1 − 1/ρ)^n]`. -/
noncomputable def blTerm (z : NontrivialZero) (n : ℕ) : ℝ :=
  (1 - (1 - 1 / (z.1 : ℂ)) ^ n).re

/-- **`VerifiedZerosTo T` — the external-computation premise (ξ-pattern).**  Every nontrivial
zero with `|Im| ≤ T` lies on the critical line.  This INTERFACES the computational record —
the nontrivial ζ-zeros have been verified on the line past height `10^9` by independent
computations (e.g. Platt–Trudgian).  A NAMED PREMISE; never claimed proved here. -/
def VerifiedZerosTo (T : ℝ) : Prop :=
  ∀ z : NontrivialZero, |z.1.im| ≤ T → z.1.re = 1 / 2

/-- **`N₀ T = ⌊2·T²⌋` — the detection threshold.**  An off-line zero at height `H` registers
in `λ_n` only for `n ≳ 2H²` (`|Im ρ| ≲ √(n/2)`; Voros; census C.6/C.8).  So verified zeros to
height `T` certify positivity for `n ≤ N₀(T)`. -/
noncomputable def N₀ (T : ℝ) : ℕ := ⌊2 * T ^ 2⌋₊

/-- **`ExplicitFormulaPremise lam` — classical named premise** (Bombieri–Lagarias 1999, via the
Guinand–Weil explicit formula; **NOT in Mathlib** at the pin).  Bundles the two facts the
finite-range argument consumes: (i) `λ_n` is the sum over nontrivial zeros of the BL summand;
(ii) each ON-LINE zero (`Re ρ = 1/2`) contributes a NON-NEGATIVE term.  Never claimed proved. -/
def ExplicitFormulaPremise (lam : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n → lam n = ∑' z : NontrivialZero, blTerm z n) ∧
  (∀ (z : NontrivialZero) (n : ℕ), z.1.re = 1 / 2 → 0 ≤ blTerm z n)

/-- **`TailBoundPremise lam T` — classical detection-threshold named premise** (Voros; **NOT
in Mathlib**).  For `n ≤ N₀(T)`, the contribution of zeros with `|Im| > T` (the tail) is
bounded below by the negative of the `|Im| ≤ T` contribution (the head) — high zeros do not
overwhelm the sign below the threshold `n ≳ 2T²`.  Never claimed proved. -/
def TailBoundPremise (T : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ N₀ T →
    - (∑' z : NontrivialZero, if |z.1.im| ≤ T then blTerm z n else 0)
      ≤ (∑' z : NontrivialZero, if |z.1.im| ≤ T then 0 else blTerm z n)

/-- **The bridge statement (frozen; discharged next sitting) — finite-range positivity.**
`VerifiedZerosTo T`, the explicit formula, and the tail bound together certify
`RegisterPentagon.Register4_positivity lam` **restricted to `n ≤ N₀(T)`**.  INTERFACES edge
(two classical named premises + the external-computation premise); the all-n tail stays the
open gap — this is NOT a proof of RH.

The discharge (next sitting) splits `λ_n` into head (`|Im| ≤ T`) and tail via
`ExplicitFormulaPremise`, uses `VerifiedZerosTo T` to put the head zeros on the line so the
head terms are `≥ 0` (`ExplicitFormulaPremise.2`), and `TailBoundPremise` to keep the tail
`≥ −head`; hence `λ_n = head + tail ≥ 0` for `n ≤ N₀(T)`. -/
def PartialPositivityFiniteRange : Prop :=
  ∀ (T : ℝ) (lam : ℕ → ℝ),
    VerifiedZerosTo T → ExplicitFormulaPremise lam → TailBoundPremise T →
      ∀ n : ℕ, 1 ≤ n → n ≤ N₀ T → 0 ≤ lam n

end PartialPositivity
end SIDELvConservation

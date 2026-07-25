import SIDELvConservation.ZeroActingPairing
import SIDELvConservation.PartialPositivity

/-!
# A2 — the finite-range partial inhabitant of the `ZeroActingPairing` interface

The interface's `yieldsInequality` clause delivers the two-channel inequality `−λ_A ≤ λ_Z` at
**every** `n`. This module compiles its **finite-range face**: a *graded* partial inhabitant carrying
the inequality only up to a coverage bound `N`, ordered by `N` (more coverage = stronger), with the
full interface sitting above every finite grade (the `N → ∞` case). It then shows the deposited
finite-range certificate `partialPositivity_finiteRange` — capped at the Voros detection threshold
`N₀(T) = ⌊2·T²⌋` — supplies exactly such a partial inhabitant, at coverage `N₀(T)`.

The coverage boundary is stated **exactly**: `n ≤ ⌊2·T²⌋` and no further. The `n > N₀(T)` range is
the open part of the totality — this is the finite-range certificate, **NOT RH**. In the ladder's
terms (W-LADDER), this is the SEARCH-grade face of the sign clause made a number: how much of the
realization-totality is certified versus what stays open.

`theorem` throughout (vanilla-build law); salt-check discipline — the partial inhabitant DERIVES from
the finite-range positivity, it does not extend it; every terminal's `#print axioms` read before
citation.
-/

namespace SIDELvConservation
namespace RegisterPentagon

open PartialPositivity

/-- The two-channel inequality restricted to a coverage bound `N`: `−λ_A ≤ λ_Z` for `1 ≤ n ≤ N`. -/
def Register4_channelInequality_upTo (lam_A lam_Z : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ N → -lam_A n ≤ lam_Z n

/-- **The graded partial inhabitant of the interface** at coverage `N` — the finite-range face of
`ZeroActingPairing.yieldsInequality`. The grade is `N`: how far the certified positivity reaches. -/
structure PartialChannelInequality (lam_A lam_Z : ℕ → ℝ) (N : ℕ) : Prop where
  coverage : Register4_channelInequality_upTo lam_A lam_Z N

/-- **The grading is monotone** — a wider coverage implies every narrower one. This is what makes the
partial inhabitants a *graded* family: `N` orders them, more coverage strictly stronger. -/
theorem partial_mono {lam_A lam_Z : ℕ → ℝ} {N M : ℕ} (hMN : M ≤ N)
    (h : PartialChannelInequality lam_A lam_Z N) :
    PartialChannelInequality lam_A lam_Z M :=
  ⟨fun n hn hnM => h.coverage n hn (Nat.le_trans hnM hMN)⟩

/-- **The full interface sits above every finite grade** — a genuine `ZeroActingPairing`'s inequality
(`Register4_channelInequality`, all `n`) restricts to the partial inhabitant at any coverage `N`. The
full object is the `N → ∞` limit of the graded family; closing that limit is RH. -/
theorem partial_of_full {lam_A lam_Z : ℕ → ℝ}
    (channelIneq : Register4_channelInequality lam_A lam_Z) (N : ℕ) :
    PartialChannelInequality lam_A lam_Z N :=
  ⟨fun n hn _ => channelIneq n hn⟩

/-- **From finite-range Li positivity to the partial inhabitant.** With the channel decomposition
`lam = lam_A + lam_Z`, finite-range positivity `0 ≤ lam n` for `n ≤ N` gives `−λ_A ≤ λ_Z` for
`n ≤ N`. -/
theorem partialChannelInequality_of_positivity {lam_A lam_Z lam : ℕ → ℝ} {N : ℕ}
    (hdecomp : ∀ n, lam n = lam_A n + lam_Z n)
    (hpos : ∀ n, 1 ≤ n → n ≤ N → 0 ≤ lam n) :
    PartialChannelInequality lam_A lam_Z N :=
  ⟨fun n hn hnN => by have h := hpos n hn hnN; rw [hdecomp n] at h; linarith⟩

/-- **The certified partial inhabitant at the Voros threshold** — wired to the deposited
`partialPositivity_finiteRange`. Under its three named premises (`VerifiedZerosTo`,
`ExplicitFormulaDecomp`, `TailBoundPremise`) and the channel decomposition, the interface's channel
inequality holds up to `N₀(T) = ⌊2·T²⌋` — the exact coverage boundary. The premises are the deposited
certificate's; this theorem adds only the lift into the interface's language. **NOT RH.** -/
theorem certifiedPartialInhabitant
    (T : ℝ) (lam_A lam_Z lam : ℕ → ℝ)
    (low : Finset NontrivialZero) (tail : ℕ → ℝ)
    (hdecomp : ∀ n, lam n = lam_A n + lam_Z n)
    (hV : VerifiedZerosTo T)
    (hEF : ExplicitFormulaDecomp lam low tail T)
    (hTail : TailBoundPremise low tail T) :
    PartialChannelInequality lam_A lam_Z (N₀ T) :=
  partialChannelInequality_of_positivity hdecomp
    (partialPositivity_finiteRange T lam low tail hV hEF hTail)

/-- **The coverage boundary, stated exactly:** the certified inhabitant reaches `n ≤ ⌊2·T²⌋` and no
further — the Voros detection threshold, verbatim from the deposited certificate. -/
theorem coverage_boundary_exact (T : ℝ) : N₀ T = ⌊2 * T ^ 2⌋₊ := rfl

end RegisterPentagon
end SIDELvConservation

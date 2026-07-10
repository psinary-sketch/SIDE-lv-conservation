# SIDE-lv-conservation

Lean 4 kernel formalizing the Conservation of Spectra content (PLACE TO
STAND programme, Ch. 13) against Mathlib. Lean v4.29.1, Mathlib pin
`5e932f9`. Mathlib is the sole dependency.

**T1 — Mellin factorization. Compiled, 0 sorry.** The completed Riemann
zeta function factors through the Mellin transform of a fixed function:
for `1 < re(s)`, `completedRiemannZeta s = mellin Φ (s/2)` with
`Φ(t) = ((evenKernel 0 t : ℂ) − 1)/2`, defined without reference to `s`.
Proved via Mathlib's `WeakFEPair.hasMellin`. The spectral parameter
enters only through the kernel `t^s` — stated as a theorem, not prose.

**T2 — s-darkness / no-other-channel. Compiled, 0 sorry** (six lemmas).
The Mellin transform's two-input exhaustion elevated to named theorems;
T2d packages the zero set of the completed zeta on the convergence
half-plane as a function of `Φ` alone.

**T3 — the per-class ⟹ all-combinations bridge. Pinned at exactly one
sorry** (`T3_StepNineBridge.lean`, citing programme finding
F.2026-07-09-b), goal state reproduced and convertibility-checked in
`PinnedGoal.lean`:

```
∀ C ∈ 𝒞, ∃ Φ, C Φ ∧ mellin Φ (s/2) ≠ 0  ⊢  ∃ Φ, (∀ C ∈ 𝒞, C Φ) ∧ mellin Φ (s/2) ≠ 0
```

The unrestricted bridge is a `∀∃ → ∃∀` commutation and is not expected
to hold in general; under the programme's *Determination* condition the
witness is shared (T1's fixed `Φ`) and the bridge closes. The closing
theorem-pair is scheduled for v0.2.0.

Axiom audit: all compiled theorems depend on
`{propext, Classical.choice, Quot.sound}` only; the single pinned
declaration additionally carries `sorryAx` and nothing else. No custom
axioms, no `native_decide`. Full details in `VERIFICATION_TRANSCRIPT.md`.

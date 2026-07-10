# SIDE-lv-conservation — VERIFICATION TRANSCRIPT

**Date.** 2026-07-09
**Repo.** `D:\SIDE-lv-conservation`
**Toolchain.** `leanprover/lean4:v4.29.1`
**Mathlib pin.** `5e932f97dd25535344f80f9dd8da3aab83df0fe6` (matches SIDE-grh-transfer)
**Federation discipline.** No Lake cross-dependencies on sister kernels; Mathlib is
the sole imported package. Pre-built Mathlib artifacts reused via a
Windows junction `.lake/packages → D:\SIDE-grh-transfer\.lake\packages`
(exact same pin).

## 1. Files and sizes

```
SIDELvConservation/T1_MellinFactorization.lean     77 lines, 3297 bytes,  0 sorry
SIDELvConservation/T2_SDarkness.lean              114 lines, 5104 bytes,  0 sorry
SIDELvConservation/T3_StepNineBridge.lean         110 lines, 5139 bytes,  1 sorry (pinned)
```

`grep 'sorry' T3_StepNineBridge.lean` reports three matches; two are
inside doc-strings/comments describing the pinning policy, and only
line 107 is an actual Lean `sorry`.  `lake build` confirms this: a
single warning `SIDELvConservation/T3_StepNineBridge.lean:91:8:
declaration uses \`sorry\`` is emitted (the `91:8` is the declaration
start; the `sorry` sits on line 107 within that declaration).

## 2. Build

```
$ lake build
✔ [2879/2879] Built SIDELvConservation.T3_StepNineBridge (15s)
warning: SIDELvConservation/T3_StepNineBridge.lean:91:8: declaration uses `sorry`
Build completed successfully (2879 jobs).
```

Exit code 0.  T1 and T2 compile without warning; T3 compiles with the
one intended `sorry`.  A separate smoke module (`SIDELvConservation/Smoke.lean`)
confirms the toolchain + Mathlib pin is wired up correctly.

## 3. Per-target status

### T1 — Mellin factorization (COMPILED, 0 sorry)

`theorem T1_completedRiemannZeta_factors_through_mellin`

Statement:
```
∃ Φ : ℝ → ℂ, ∀ s : ℂ, 1 < s.re →
  completedRiemannZeta s = mellin Φ (s / 2)
```

Witness: `Phi := fun t => ((HurwitzZeta.evenKernel 0 t : ℂ) - 1) / 2`,
defined without reference to `s`.

Proof strategy: apply `WeakFEPair.hasMellin` to `HurwitzZeta.hurwitzEvenFEPair 0`
at `s / 2` (valid on `re s > 1`, i.e. `re (s/2) > 1/2 = P.k`), then
apply `mellin_div_const` and the definitional chain
`completedRiemannZeta s = completedHurwitzZetaEven 0 s
                        = ((hurwitzEvenFEPair 0).Λ (s / 2)) / 2`.

Mathlib names actually used and verified on this machine:
* `Complex.completedRiemannZeta`
  (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:67`)
* `HurwitzZeta.evenKernel`
  (`Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:65`)
* `HurwitzZeta.hurwitzEvenFEPair`
  (`Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:254`)
* `WeakFEPair.hasMellin`
  (`Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean:421`)
* `mellin`, `mellin_div_const`
  (`Mathlib/Analysis/MellinTransform.lean:92,115`)

The work-order-suggested `Mathlib.Analysis.MellinTransform` name is
correct; the `completed ξ data` is `completedRiemannZeta` (not a
newly-named object).  No name drift required patching.

### T2 — s-darkness extension (COMPILED, 0 sorry)

Six theorems:

1. `T2a_mellin_congr_on_Ioi` — `Set.EqOn Φ₁ Φ₂ (Ioi 0) → ∀ s, mellin Φ₁ s = mellin Φ₂ s`.
2. `T2a'_mellin_congr` — `Φ₁ = Φ₂ → ∀ s, mellin Φ₁ s = mellin Φ₂ s`.
3. `T2b_mellin_exhaustion` — `mellin Φ s = ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) • Φ t`
   (Mathlib's `mellin` definition, elevated to a named theorem for
   citation as the "no-other-channel" statement).
4. `T2c_phi_side_predicates_are_s_dark` — for any predicate `P` on `ℝ → ℂ`
   and equal Φ's, mellin transforms agree at every `s`.
5. `completedRiemannZeta_eq_mellinPhi` — concrete non-classical variant of T1
   at a fixed `s`, exposing the explicit witness (avoids `Classical.choose`).
6. `T2d_zero_iff_mellinPhi_zero` — for `1 < re s`,
   `completedRiemannZeta s = 0 ↔ mellin Phi (s / 2) = 0`.  Packages
   T1 in the form T3 consumes.

### T3 — step-(9) bridge (COMPILED WITH ONE PINNED SORRY)

Four theorems:

1. `T3a_zeroLoc_is_function_of_Phi` — `Φ₁ = Φ₂ → ZeroLoc Φ₁ = ZeroLoc Φ₂`. **0 sorry.**
2. `T3b_joint_witness_gives_combinations_exclude` — a joint `Φ` witnessing
   every coupling and non-vanishing at `s / 2` gives combined exclusion. **0 sorry.**
3. `T3_perClass_to_combinations` — per-class exclusion ⟹ combined exclusion. **1 sorry (pinned).**

Pinned `sorry` location: `SIDELvConservation/T3_StepNineBridge.lean:107`
Comment cites `FINDINGS F.2026-07-09-b`.

**Pinned goal state at the `sorry`** (verified by an independent
`example` in `PinnedGoal.lean` whose type is *definitionally* the T3
goal — the fact that `PinnedGoal.lean` type-checks proves convertibility):

```
𝒞 : Set Coupling         -- Coupling := (ℝ → ℂ) → Prop
s : ℂ
h : ∀ C ∈ 𝒞, PerClassExcludes C s
  -- unfolded: ∀ C ∈ 𝒞, ∃ Φ, C Φ ∧ mellin Φ (s / 2) ≠ 0
⊢ ∃ Φ : ℝ → ℂ, (∀ C ∈ 𝒞, C Φ) ∧ mellin Φ (s / 2) ≠ 0
```

This is a `∀∃ ⟹ ∃∀` commutation.  It fails without an additional
witness-selection / joint-consistency / cofinality assumption on the
family `𝒞 ⊆ (ℝ → ℂ) → Prop`.  The manuscript's per-class witnesses
`{Φ_C : C Φ_C ∧ mellin Φ_C (s/2) ≠ 0}` need not share a common point
in `Φ`-space, which is exactly the **emergent-totality question**
flagged in FINDINGS F.2026-07-09-b.

Per work-order T3 rules:
* Statement not weakened.
* No new axiom introduced.
* No `native_decide` invoked.
* Exactly one `sorry`, at the exact step where a new assumption would
  be required.

## 4. Axiom audit (`#print axioms`)

Reproduced from `AxiomCheck.lean`:

```
'SIDELvConservation.T1_completedRiemannZeta_factors_through_mellin'
  depends on axioms: [propext, Classical.choice, Quot.sound]

'SIDELvConservation.T2a_mellin_congr_on_Ioi'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'SIDELvConservation.T2a'_mellin_congr'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'SIDELvConservation.T2b_mellin_exhaustion'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'SIDELvConservation.T2c_phi_side_predicates_are_s_dark'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'SIDELvConservation.completedRiemannZeta_eq_mellinPhi'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'SIDELvConservation.T2d_zero_iff_mellinPhi_zero'
  depends on axioms: [propext, Classical.choice, Quot.sound]

'SIDELvConservation.T3.T3a_zeroLoc_is_function_of_Phi'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'SIDELvConservation.T3.T3b_joint_witness_gives_combinations_exclude'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'SIDELvConservation.T3.T3_perClass_to_combinations'
  depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

**Interpretation.**  T1 (1 theorem), T2 (6 theorems), and T3's trivial
half (2 theorems) reduce to the standard Mathlib base:
`propext`, `Classical.choice`, `Quot.sound`.  T3's load-bearing bridge
additionally lists `sorryAx`, corresponding to the pinned
emergent-totality gap.  No stray axioms surfaced.

## 5. Summary

* **T1 (Mellin factorization):** COMPILED, 0 sorry.
* **T2 (s-darkness extension):** COMPILED, 0 sorry.
* **T3 (step-9 bridge):** COMPILED with exactly one pinned `sorry` at
  `T3_StepNineBridge.lean:107`, citing FINDINGS F.2026-07-09-b.
* **Axiom profile:** T1, T2, and T3's auxiliary lemmas
  = `{propext, Classical.choice, Quot.sound}`; T3's main bridge
  additionally = `{sorryAx}` (the pinned emergent-totality gap).

The compiler's verdict per the work order is that T1+T2 fully close
(the trivial-restatement direction is confirmed as trivial, and the
s-darkness/no-other-channel statement is the `mellin` definition
elevated to a citable theorem), while T3's substantive content pins
to a `∀∃ ⟹ ∃∀` commutation that no free move can close.  This is
consistent with the work order's honest-scoping clause: partial
closure (T1 + T2 compiled, T3 pinned) is the expected full-success
regime here — it converts prose disagreement into an address.

---

## Addendum — 2026-07-09 (v0.2.0): T3′ and T3″

Two new theorems added to `SIDELvConservation/T3_StepNineBridge.lean`,
below the original pinned `T3_perClass_to_combinations`.  The pinned
`sorry` was not touched and no earlier statement was weakened.  The
`lake build` output still emits exactly one `declaration uses \`sorry\``
warning, on the same original declaration at line 92.

### T3′ — Determination's shared-witness bridge

`T3prime_shared_witness (𝒞 : Set Coupling) (s : ℂ)
    (h1 : ∀ C ∈ 𝒞, C Phi) (h2 : mellin Phi (s / 2) ≠ 0) :
    ∃ Φ, (∀ C ∈ 𝒞, C Φ) ∧ mellin Φ (s / 2) ≠ 0`

**Status.** COMPILED, 0 sorry.  Proof: `⟨Phi, h1, h2⟩`.

Reading: if the programme's Determination condition is in force,
every coupling in `𝒞` is satisfied by T1's fixed `Phi`, and that
`Phi` has non-vanishing Mellin factor at `s / 2`.  Under those
hypotheses the T3 `∀∃ ⟹ ∃∀` gap collapses trivially — the shared
witness is both the per-class witness for every `C ∈ 𝒞` and the
joint witness for the combined conclusion.  The theorem is not a
weakening of T3; `h1, h2` name the extra information Determination
supplies.

### T3″ — countermodel: the unrestricted bridge fails

`T3doubleprime_general_commutation_fails :
    ¬ ∀ (𝒞 : Set Coupling) (s : ℂ),
        (∀ C ∈ 𝒞, ∃ Φ, C Φ ∧ mellin Φ (s / 2) ≠ 0) →
        ∃ Φ, (∀ C ∈ 𝒞, C Φ) ∧ mellin Φ (s / 2) ≠ 0`

**Status.** COMPILED, 0 sorry.  Explicit countermodel at `s = 3`:

* `f₁ t := if 0 < t then Phi t else 0`
* `f₂ t := if 0 < t then Phi t else 1`
* `C₁ Φ := (Φ = f₁)`, `C₂ Φ := (Φ = f₂)`, `𝒞 := {C₁, C₂}`.

Verifications discharged inside the proof:

* `mellin Phi (3 / 2) ≠ 0` — via `completedRiemannZeta_eq_mellinPhi 3 hRe`
  reducing to `completedRiemannZeta 3 ≠ 0`, then to
  `riemannZeta 3 ≠ 0` (`riemannZeta_ne_zero_of_one_lt_re`) using
  `riemannZeta_def_of_ne_zero` and `s ≠ 0`.
* `mellin f₁ (3/2) = mellin Phi (3/2)` and `mellin f₂ (3/2) = mellin Phi (3/2)` —
  by `setIntegral_congr_fun measurableSet_Ioi`, since `f₁ = f₂ = Phi`
  on `Ioi 0`.
* No `Φ` satisfies both `C₁` and `C₂`: `Φ = f₁ ∧ Φ = f₂ ⇒ f₁ = f₂`,
  but evaluating at `t = -1 ∉ Ioi 0` gives `f₁(-1) = 0` and
  `f₂(-1) = 1`, so `(0 : ℂ) = 1`, contradiction (`zero_ne_one`).

Consequence: **Determination is doing real work in T3′**.  The
unrestricted `∀∃ ⟹ ∃∀` bridge over `(𝒞, s)` is *provably false*,
so the closure in T3′ requires — and is genuinely served by — the
shared-witness hypothesis `h1`.

### Updated sorry count and axiom audit (v0.2.0)

`lake build` output:

```
warning: SIDELvConservation/T3_StepNineBridge.lean:92:8: declaration uses `sorry`
Build completed successfully.
```

Exactly one `sorry`, the pinned emergent-totality gap of the original
`T3_perClass_to_combinations`.  Both new theorems compile clean.

`#print axioms` (v0.2.0 additions):

```
'SIDELvConservation.T3.T3prime_shared_witness'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'SIDELvConservation.T3.T3doubleprime_general_commutation_fails'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

Neither carries `sorryAx`; neither introduces a new axiom.

### Updated summary

* **T1 (Mellin factorization):** COMPILED, 0 sorry.
* **T2 (s-darkness extension):** COMPILED, 0 sorry.
* **T3 (step-9 bridge, original):** COMPILED with one pinned `sorry`
  at `T3_StepNineBridge.lean:108`, citing F.2026-07-09-b.
* **T3′ (Determination's shared-witness bridge):** COMPILED, 0 sorry.
* **T3″ (countermodel, unrestricted bridge fails):** COMPILED, 0 sorry.
* **Axiom profile:** T1, T2, and all closed T3 sub-lemmas (including
  T3′ and T3″) = `{propext, Classical.choice, Quot.sound}`.  Only the
  original `T3_perClass_to_combinations` additionally = `{sorryAx}`.

The pair T3′ / T3″ *bracket* the original T3 statement:  T3′ shows
what closure looks like once Determination is available; T3″ shows
that closure is not free without it.  Both are compiler-verdicts, not
prose.

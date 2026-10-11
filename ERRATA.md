# Errata

This file records corrections to SIDE-lv-conservation`s main. Each entry lists the declaration, the affected file and line, the correction, and the date; entries are retained.

## E-2026-10-10-1 — 1 `sorry`-closed declarations quarantined from main (b648, the author`s ruling (R258)(2))

Every declaration below closed by `sorry` on main at `2f71068`, in files outside every `lean_lib` of the lakefile; each entered main before the programme`s standing line "no `sorry` on any `main`" (its first ledger line, PLACE-papers OPEN_TRAILS.md :11508, 2026-09-29). Each is removed from main and kept whole on the branch `sorry-quarantine-SIDE-lv-conservation`, made at `2f71068`. Correction: removed from main, quarantined. Date: 2026-10-10.

- `(example)` (example), `PinnedGoal.lean` :17 (its `sorry` at :23), entered 2026-07-09 at `45c2759`: `example (𝒞 : Set Coupling) (s : ℂ) (h : ∀ C ∈ 𝒞, PerClassExcludes C s) : ∃ Φ : ℝ → ℂ, (∀ C ∈ 𝒞, C Φ) ∧ mellin Φ (s / 2) ≠ 0 := by -- Same goal shape as at T3_StepNineBridge.lean:107. Reproduced only -- to guarantee the t`.

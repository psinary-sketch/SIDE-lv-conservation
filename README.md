# The legacy map of sorry-quarantine-SIDE-lv-conservation

This branch holds, as they stood, the declarations that b648 quarantined from `main` under the author’s ruling (R258)(2): each was closed by `sorry` and entered `main` before the standing rule that no `sorry` reaches any `main` (relay OPEN_TRAILS :11508). The branch’s tip, `2f71068`, is the commit of `main` they were quarantined from; `main` (`b2238d4` when this map was written) no longer carries them, and the kernel’s `ERRATA.md` on `main` names each. Each row gives the declaration’s file and line at the tip, its statement, the date it entered `main`, and its successor in the built kernel -- the declaration in a lean_lib of `main` proving the same content, by file and line -- or “no successor; superseded by” with the reason. Written by relay b649 under (R259)(3) from relay `data/b648_sorry_classification.json`.

The kernel’s own `README.md`, which this map replaces on this branch alone, stands whole at the tip `2f71068` (blob `879c900ee218`) and on `main`.

| # | file :line (at `2f71068`) | kind | declaration | its `sorry` | statement | entered main | successor |
|:--|:--|:--|:--|:--|:--|:--|:--|
| 1 | `PinnedGoal.lean` :17 | example | `(example)` | :23 | `example (𝒞 : Set Coupling) (s : ℂ) (h : ∀ C ∈ 𝒞, PerClassExcludes C s) : ∃ Φ : ℝ → ℂ, (∀ C ∈ 𝒞, C Φ) ∧ mellin Φ (s / 2) ≠ 0` | 2026-07-09 | no successor; superseded by SIDELvConservation/T3_StepNineBridge.lean :108, the goal it reproduced, the theorem b648 RESTATED as a Prop on branch b648-restate-SIDE-lv-conservation |

1 quarantined declarations (1 `sorry` lines); 0 with a successor in the built kernel.


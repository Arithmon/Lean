# Arithmon / Lean

The machine-checked formal layer of the [Arithmon program](https://github.com/arithmon).
It certifies, in Lean 4, the two things the [Sieve](https://github.com/arithmon/sieve)
methodology needs a proof assistant for:

1. **Expression-space counts.** The size of the haystack `|E(G, k)|`, the
   denominator of every trials-factor computation (skeleton figure F2 /
   section 7.3), computed exactly rather than trusted to a floating-point proxy.
2. **The in-framework-theorem rebate (Q5).** A relation found by search pays a
   look-elsewhere factor equal to the value-haystack it scanned; a relation that
   is a theorem of a pre-specified structure, committed before the target was
   consulted, pays 1. The rebate is a binary indicator times a certified count,
   not a continuous fitting resource, which is why it escapes the closeness and
   coverage (N2) trap by construction.

## What is certified today

- `Arithmon/Sieve/GStruct.lean`: a faithful port of the frozen
  `G_STRUCT(betti = 21, 77)` grammar (freeze v1.0,
  DOI 10.5281/zenodo.20666879). The **rational fragment** (the grammar without
  `sqrt`, so values stay rational and dedup is by exact `Rat` equality) has
  certified counts `|E_rat(G_STRUCT, k)| = 32, 91, 1416` at budgets 1, 2, 3,
  cross-checked against an exact-rational re-run of the Sieve engine. Koide's
  2/3 is shown reachable in the real grammar.
- `Arithmon/Rebate/Core.lean`: the generic rebate definitions and a minimal
  worked example (toy grammar) exhibiting the search-versus-theorem contrast
  end to end, all by `native_decide`, zero `sorry`.

Why the rational fragment: the Sieve's Python engine dedups by a float rounded
to 12 significant digits, a practical proxy with a small risk of false merges.
Restricting to the exactly-representable rational operations gives a provably
correct count for that fragment, strictly stronger than the float proxy. The
full grammar (with `sqrt`) stays in Python; this is its auditable rational core.

## Architecture: two layers

- **Generic layer (this repository, today).** Pure Lean 4 core, **no Mathlib**,
  so the trusted base of the certified counts is as small as possible.
- **Per-client audit layer (next).** Confirming that a specific framework
  relation is a proven consequence of the framework axioms, not a numerical
  lemma asserting a value, requires reading that framework's Lean. The audit
  decomposes into three checkable conditions (Sieve ledger D24): **R1a** the
  value is a proven consequence of the framework's invariants (the gate);
  **R1b** the value is not over-reachable within the framework, one forced
  formula rather than many (the popularity discount); **R1c** the physical
  observable is derived and shown equal to the value, not merely identified
  with it. This layer will depend on the audited framework's Lean (for the GIFT
  case study, GIFT core) at the **same pinned Mathlib release as this toolchain,
  `v4.29.0`**. Pinning to a Mathlib release tag (as GIFT core already does) is
  what keeps this aligned with upstream and interoperable with core; the
  repository is a normal `lake` project that *requires* Mathlib, not a fork of
  it. Per-relation audit verdicts of a case study are the methodology paper's
  payload, not published here.

## Build

```
lake build
```

Requires the Lean toolchain in `lean-toolchain` (`v4.29.0`); `elan` installs it
automatically. The generic layer has no dependencies, so the build is offline
and fast.

## Scope and honesty

This layer formalizes the rebate and certifies counts. It does **not** yet
award the rebate to any GIFT relation: that is the per-client R1 audit above,
where the real risk lives. "Theorem" here means built and certified (classical
Lean), not intuitionistically constructive.

---

Siblings: [Program](https://github.com/arithmon/program) ·
[Atlas](https://github.com/arithmon/atlas) ·
[Sieve](https://github.com/arithmon/sieve)

<sub>GIFT is the founding framework of the Arithmon program.
Program: [arithmon.com](https://arithmon.com) ·
[github.com/arithmon](https://github.com/arithmon)</sub>

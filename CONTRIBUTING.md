# Contributing to Arithmon / Lean

This repository is the machine-checked layer: it certifies, in Lean 4, the
counts the Sieve methodology needs proved rather than trusted to a
floating-point proxy. A contribution here is a proof, held to the standard of a
proof.

Org-wide rules (what helps, what does not, house style) are in the
[organization CONTRIBUTING](https://github.com/arithmon/.github/blob/main/CONTRIBUTING.md).

## What a valid contribution looks like

- **Zero `sorry`.** No admitted lemmas, no `axiom` introduced to close a goal.
  `lake build` must be green.
- **Reproducible.** A count closed by `native_decide` must come with the exact
  statement of what is counted, so it can be re-run independently.
- **Cross-checked.** A certified count that mirrors a Sieve figure must agree
  with an exact-rational re-run of the Sieve engine (not the float pipeline).
  State which Sieve artifact it matches.
- **Faithful to the freeze.** A grammar ported into Lean must match the frozen
  `G_STRUCT` specification (freeze v1.0,
  DOI [10.5281/zenodo.20666879](https://doi.org/10.5281/zenodo.20666879)). A
  port that quietly differs is a bug, not an improvement.

## Good contributions

- Extending a certified count to a larger budget, if `native_decide` stays
  tractable (note the elaboration cost; chunking is often needed).
- Porting another frozen grammar faithfully, with its cross-check.
- Tightening a proof: replacing a `native_decide` with a structural argument,
  or removing a dependency.
- Finding a discrepancy between a Lean count and the Sieve engine. Report it as
  an issue with both numbers; a divergence is a real finding.

## What does not belong

- A count that is "probably right" but not machine-checked. The whole point of
  this layer is that probably-right is not enough.
- A proof that depends on widening the grammar or the vocabulary to make a
  target reachable.

Mathlib is a pinned dependency (v4.29.0, matching the GIFT core). Do not vendor
or fork it.

---

Siblings: [Program](https://github.com/arithmon/program) ·
[Atlas](https://github.com/arithmon/atlas) ·
[Sieve](https://github.com/arithmon/sieve)

<sub>GIFT is the founding framework of the Arithmon program.
Program: [arithmon.com](https://arithmon.com) ·
[github.com/arithmon](https://github.com/arithmon)</sub>

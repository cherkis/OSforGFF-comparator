# Basis for the priority statement

The project description states that the pinned library is, to our knowledge, the first
machine-checked verification of the Osterwalder–Schrader axioms. This file documents the
literature search behind that statement: what was searched, when, with which terms, and
what was found. The claim remains a "to our knowledge" statement — the search below is its
documented basis, not a proof of a negative.

## Search scope (performed 2026-08-31)

- **Web search** (arXiv, general web) over combinations of: *machine-checked / formalization
  / formal verification*, *Osterwalder–Schrader axioms*, *Euclidean field theory*,
  *constructive quantum field theory*, *Wightman axioms*, *reflection positivity*,
  *Gaussian free field*, *Glimm–Jaffe*, with each of *Lean*, *Isabelle*, *Coq/Rocq*,
  *proof assistant*.
- **Isabelle Archive of Formal Proofs**: the AFP topic index (isa-afp.org/topics). The
  physics-adjacent topics are *Quantum computing* and *Quantum information*; there is no
  quantum field theory, Euclidean field theory, or reflection-positivity entry.
- **PhysLean / physlib** (`leanprover-community/physlib`, formerly HEPLean/PhysLean): a scan
  of the repository's full file tree for *Osterwalder*, *Wightman*, *Schwinger*,
  *reflection*, *Euclidean*. It carries Euclidean-group infrastructure and
  perturbation-theory material (notably Wick's theorem, Tooby-Smith, arXiv:2505.07939), but
  no statement or proof of the OS axioms. Its open issue #938 ("Integrate Glimm-Jaffe AQFT
  Framework into PhysLean") proposes integrating **this project's** library as that
  framework.
- **Lean Zulip** (via web search over the public archive) for *Osterwalder–Schrader*,
  *Euclidean field theory*, *Glimm–Jaffe* formalization discussions.

## Findings

Every hit describing a machine-checked verification of the OS (Glimm–Jaffe) axioms refers
to the pinned library itself — `mrdouglasny/OSforGFF` — or to its informal companion
account (M. R. Douglas, *Formalization of QFT*, arXiv:2603.15770) and public discussion of
it. No prior or independent machine-checked statement or proof of the OS axioms was found
in Lean, Isabelle, or Coq/Rocq.

Related but distinct formalization work found by the search:

- **PhysLean / physlib** — physics in Lean 4, including Wick's theorem
  (arXiv:2505.07939) and Euclidean-group actions on Schwartz functions; explicitly not
  tied to an axiomatic-QFT formulation, and containing no OS-axioms development (see
  issue #938, which points here).
- **Isabelle AFP quantum entries** — quantum computation and quantum information
  (e.g. *Isabelle Marries Dirac*), not quantum field theory.
- **Lean quantum-information formalizations** — e.g. the generalized quantum Stein's
  lemma (arXiv:2510.08672); a different subject.

## Limits

The search was an English-language web and repository search on the date given; it did not
include a systematic sweep of every proof-assistant library or non-indexed development.
This is why the description says "to our knowledge" rather than asserting priority
absolutely.

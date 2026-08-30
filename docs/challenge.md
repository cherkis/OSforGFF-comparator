# The registry Challenge: design and dictionary

`Challenge.lean` restates the headline result of
[mrdouglasny/OSforGFF](https://github.com/mrdouglasny/OSforGFF) — *the free Gaussian Free
Field exists and satisfies the Osterwalder–Schrader axioms in every dimension `d ≥ 2`* — in
a form auditable **without trusting or reading that library**: its transitive imports are
Mathlib only. `Solution.lean` proves it from the library, which `lakefile.toml` pins at an
exact commit. This document explains the design choices and tabulates the dictionary
between the Challenge's self-contained definitions and the library's originals; library
file paths below refer to the pinned commit.

## The statement

```lean
theorem Challenge.gaussianFreeField_satisfies_OS_axioms
    (d : ℕ) [Fact (2 ≤ d)] (m : ℝ) (hm : 0 < m) :
    ∃ μ : ProbabilityMeasure (FieldConfiguration d),
      (∀ f : TestFunction d,
        GJGeneratingFunctional μ f =
          Complex.exp (-(1 / 2 : ℂ) * ((covarianceForm d m f f : ℝ) : ℂ))) ∧
      EuclideanPullbackExists d ∧ TimeReflectionStarExists d ∧ TimeTranslationExists d ∧
      TranslationExists d ∧
      OS0_Analyticity μ ∧ OS1_Regularity μ ∧ OS2_EuclideanInvariance μ ∧
      OS3_ReflectionPositivity μ ∧ OS4_Clustering μ ∧ OS4_Ergodicity μ
```

**Why existential + characterization.** The library states its theorem about a *named*
measure, `gaussianFreeField_free`, whose construction goes through the Minlos theorem
(external `bochner` library) and therefore cannot appear in a Mathlib-only file. The
Challenge instead asserts the existence of a measure **together with the property that
determines it uniquely**: its generating functional is the Gaussian
`Z[f] = exp(−½⟨f, C f⟩)`. This clause is essential — a bare "there exists a measure
satisfying OS0–OS4" would be discharged by the Dirac measure at `0` (for which `Z ≡ 1`).
With it, the statement is exactly "the free field with covariance `(−Δ + m²)⁻¹` exists and
satisfies the OS axioms": a Gaussian probability measure on `S'(ℝ^d)` is determined by its
characteristic functional.

**Why the proper-time covariance.** The free covariance is presented by its Schwinger
(heat-kernel) integral

```
C(x, y) = ∫₀^∞ e^{−t m²} (4πt)^{−d/2} e^{−‖x−y‖²/(4t)} dt ,
```

an elementary closed formula requiring no operator theory, valid uniformly in the dimension.
It matches the library's canonical propagator `GFFPropagator.ofProperTime`
(`OSforGFF/Covariance/Propagator.lean`), for which the identification is definitional — so
the Solution's characterization clause is exactly the library lemma
`gff_real_characteristic`.

**Why characterised transforms.** Four of the axioms speak about transformed test
functions: the Euclidean pullback `f(g⁻¹x)` (OS2), the reflected conjugate
`(f*)(x) = conj (f (Θx))` (OS3), the translate `f(x − a)` (OS4 clustering and the OS1
mollifier smearing), and the time translate `f(timeShift s x)` (OS4 ergodicity). That each
transform is again a Schwartz function is a fact of *analysis*, not part of the statement —
constructing them as Schwartz maps inside the Challenge would mean carrying decay and
growth estimates on the audit surface. The Challenge instead **characterises each transform
pointwise**: the axiom quantifies over any test function with the required values, as in
"for every `f'` with `f' x = f (g⁻¹ x)`, …". Two Schwartz functions with the same values
are equal (`SchwartzMap.ext`), so this states the same axiom — *provided such `f'` exist at
all*. The four `…Exists` conjuncts of the theorem (`EuclideanPullbackExists`,
`TimeReflectionStarExists`, `TimeTranslationExists`, `TranslationExists`) assert precisely
that existence, so no axiom holds vacuously; each is proved outright in the Solution by
exhibiting the library's constructed transform as the witness. The characterised statement
is therefore **strictly stronger, conjunct by conjunct**, than the fully-constructed
formulation it replaced.

That equivalence is itself machine-checked: `StatementEquivalence.lean` (repository root)
reproduces the earlier fully-constructed formulation verbatim under `Challenge.Orig`,
verifies the shared foundation is byte-identical, and proves the two full `∃ μ` theorem
statements equivalent for every `d ≥ 2` and mass — per-axiom iffs plus the existence
conjuncts, all bridges definitional. It is deliberately not a lake target (it plays no role
in the Comparator run); check it with `lake env lean StatementEquivalence.lean`.

One transform family stays constructed: the mollifier bumps
`bumpToSchwartz`/`standardBumpSequence` used by OS1's two-point regularity. Quantifying
over arbitrary mollifier families would genuinely change the statement's strength — the
library's convergence engine is stated for `ContDiffBump` sequences — so the bumps are the
correct load-bearing data, not removable apparatus.

**Hypotheses.** `2 ≤ d` is carried as a `Fact` instance because the positive-time apparatus
of OS3 (the time coordinate `x₀`) consumes it through instances; `0 < m` is a plain
hypothesis. Neither weakens the statement: both are the standard hypotheses of the theory
(`d ≥ 2` for a time/space split, `m > 0` for a mass gap). OS3's support restriction is the
plain hypothesis `tsupport (f i) ⊆ positiveTimeSet` — no subtype of positive-time test
functions is defined.

## Verification workflow

- `lake build` — builds both root modules (the default targets); `Challenge` reports
  exactly one `sorry` (the hole), `Solution` is clean.
- `diff Challenge.lean Solution.lean` — the files agree except for the import line, the
  module docstring, and the proof.
- `comparator.json` — drives the Comparator: identical statement, only
  `propext`/`Classical.choice`/`Quot.sound`, kernel replay. Run it under a real sandbox
  with `./scripts/verify-comparator.sh`.
- `scripts/check-pair.sh` — additionally gates the pair at source level (no axioms or
  escape hatches; exactly one `sorry`, in `Challenge.lean`).
- `lake env lean StatementEquivalence.lean` — checks the equivalence of the characterised
  statement with the fully-constructed formulation (see above; not a lake target).

## Dictionary

Every Challenge definition is a copy of a library definition (the embedded *proofs* may
differ — by proof irrelevance only the data must agree), except where a row says
*characterised*: there the Challenge defines no Schwartz-map transform at all, and the
library's construction enters only as the Solution's existence witness. The table gives
the corresponding library declaration and file.

### Spacetime, test functions, field configurations

| Challenge (`Challenge.*`) | Library | File |
|---|---|---|
| `SpaceTime` | `SpaceTime` | `OSforGFF/Spacetime/Basic.lean` |
| `TestFunction`, `TestFunctionℂ` | `SchwartzTestFunction`, `SchwartzTestFunctionℂ` | `OSforGFF/Spacetime/Basic.lean` |
| `FieldConfiguration` | `FieldConfiguration` | `OSforGFF/Spacetime/Basic.lean` |
| `measurableSpaceWeakDual` (cylinder σ-algebra) | `instance : MeasurableSpace (WeakDual ℝ E)` | `bochner`: `Minlos/NuclearSpace.lean` |
| `NeZero` instance, `getTimeComponent` | same | `OSforGFF/Spacetime/Basic.lean` |

The cylinder σ-algebra `⨆ f, (borel ℝ).comap (ω ↦ ω f)` is the one definition whose
original lives in an external dependency; it is copied verbatim so that the Challenge's
`ProbabilityMeasure (FieldConfiguration d)` is definitionally the library's.

### Pairings and generating functionals

| Challenge | Library | File |
|---|---|---|
| `distributionPairing` | `distributionPairing` | `OSforGFF/Spacetime/Basic.lean` |
| `GJGeneratingFunctional`, `GJGeneratingFunctionalℂ` | same | `OSforGFF/Spacetime/Basic.lean` |
| `schwartz_comp_clm`, `complex_testfunction_decompose`, `distributionPairingℂ_real` | same | `OSforGFF/Spacetime/Basic.lean` |

### The free covariance

| Challenge | Library | File |
|---|---|---|
| `heatKernelProfile` | `heatKernelProfile` | `OSforGFF/Covariance/Propagator.lean` |
| `properTimeCovariance` | `properTimeCovariance` | `OSforGFF/Covariance/Propagator.lean` |
| `freeCovariance d m x y` | `freeCovariance d m x y` with `Cprofile := GFFPropagator.ofProperTime` | `OSforGFF/Covariance/Propagator.lean` |
| `covarianceForm` | `QFT.freeCovarianceFormR` | `OSforGFF/Covariance/RealForm.lean` |

### Schwinger functions and the two-point function (OS1)

| Challenge | Library | File |
|---|---|---|
| `SchwingerFunction`, `SchwingerFunction₂` | same | `OSforGFF/Schwinger/Defs.lean` |
| `bumpToSchwartz`, `standardBumpSequence` | same | `OSforGFF/Schwinger/TwoPoint.lean` |
| translated mollifier `φₙ(· − x)` | *characterised* in `TwoPointIntegrable`; witness `SchwartzMap.translate` | `OSforGFF/General/FunctionalAnalysis.lean` |

The library's smearing chain (`translateSchwartz`, `SmearedTwoPointFunction`,
`SchwingerTwoPointFunction`) does not appear in the Challenge: `TwoPointIntegrable` inlines
the mollifier limit, quantifying over any `smear` family with the translate's pointwise
values.

### Euclidean motions (OS2)

The Challenge defines no Euclidean-group structure at all. `OS2_EuclideanInvariance`
quantifies over Mathlib's linear isometry equivalences `R : SpaceTime d ≃ₗᵢ[ℝ] SpaceTime d`
and translation vectors `b`, and characterises the pullback pointwise
(`f' x = f (R.symm (x − b))`). The library's group `QFT.E d` (`OSforGFF/Spacetime/
Euclidean.lean`), its action `QFT.act`, and the constructed pullback
`QFT.euclidean_action` enter only in the Solution, which bridges via the component mapping
`(R, b) ↦ ⟨R.toLinearIsometry, b⟩` and witnesses `EuclideanPullbackExists` with
`QFT.euclidean_action`.

### Time reflection, star, positive time (OS3)

| Challenge | Library | File |
|---|---|---|
| `timeReflection` (raw map `Θ`) | `QFT.timeReflection` | `OSforGFF/Spacetime/DiscreteSymmetry.lean` |
| `HasPositiveTime`, `positiveTimeSet` | same | `OSforGFF/Spacetime/PositiveTimeTestFunction.lean` |
| OS star `(f*)(x) = conj (f (Θx))` | *characterised* in `OS3_ReflectionPositivity`; witness the `Star (TestFunctionℂ d)` instance | `OSforGFF/Spacetime/PositiveTimeTestFunction.lean` |

The library's Schwartz-map reflection apparatus (`timeReflectionCLM`,
`compTimeReflection`, `starTestFunction` as a construction) and its positive-time subtype
`PositiveTimeTestFunctionℂ` do not appear: the star is characterised pointwise (the bridge
in the Solution is `rfl` — the library star's pointwise formula is definitional), and the
support restriction is a plain hypothesis on each `f i`.

### Time translations (OS4 ergodicity)

| Challenge | Library | File |
|---|---|---|
| `timeShift` (raw map on points) | `TimeTranslation.timeShift` | `OSforGFF/Spacetime/TimeTranslation.lean` |
| time translate of a test function | *characterised* in `OS4_Ergodicity`; witness `TimeTranslation.timeTranslationSchwartzCLM` | `OSforGFF/Spacetime/TimeTranslation.lean` |

### The OS axioms

| Challenge | Library | File |
|---|---|---|
| `OS0_Analyticity` | `OS0_Analyticity` | `OSforGFF/OS/Axioms.lean` |
| `TwoPointIntegrable`, `OS1_Regularity` | same (translate characterised, see OS1 above) | `OSforGFF/OS/Axioms.lean` |
| `OS2_EuclideanInvariance` | `OS2_EuclideanInvariance` (pullback characterised) | `OSforGFF/OS/Axioms.lean` |
| `OS3_ReflectionPositivity` | `OS3_ReflectionPositivity` (star characterised, support as hypothesis) | `OSforGFF/OS/Axioms.lean` |
| `OS4_Clustering` | `OS4_Clustering` (translate characterised) | `OSforGFF/OS/Axioms.lean` |
| `OS4_Ergodicity` | `OS4_Ergodicity` (time translate characterised) | `OSforGFF/OS/Axioms.lean` |

### The existence conjuncts

| Challenge | Solution witness | File |
|---|---|---|
| `EuclideanPullbackExists` | `QFT.euclidean_action` | `OSforGFF/Spacetime/Euclidean.lean` |
| `TimeReflectionStarExists` | `star` (the library `Star` instance; bridge `rfl`) | `OSforGFF/Spacetime/PositiveTimeTestFunction.lean` |
| `TimeTranslationExists` | `TimeTranslation.timeTranslationSchwartzCLM` | `OSforGFF/Spacetime/TimeTranslation.lean` |
| `TranslationExists` | `SchwartzMap.translate` (via `SchwartzMap.translate_apply`) | Mathlib / `OSforGFF/General/FunctionalAnalysis.lean` |

These have no library counterpart as *statements*; each records the analytic fact that the
corresponding transform lands back in Schwartz space, which the library carries inside its
constructions.

### The theorem

| Challenge | Proved from | File |
|---|---|---|
| `gaussianFreeField_satisfies_OS_axioms` | `OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_generic` under `GFFPropagator.ofProperTime`, with `gff_real_characteristic` for the characterization clause and the four witnesses above for the existence conjuncts | `OSforGFF/OS/Master.lean`, `OSforGFF/Measure/Construct.lean` |

The witness is the library's Minlos-constructed measure `gaussianFreeField_free`
(`OSforGFF/Measure/Construct.lean`); the five OS conjuncts are the fields of the master
theorem, with each characterised transform identified with the library's construction by
`SchwartzMap.ext` and a definitional pointwise formula.

## Known divergences from the sources

As in the library (see `formalization.yaml`, `fidelity`): the axioms are stated in the
Glimm–Jaffe probability-measure formulation rather than for Schwinger functions; OS3 is the
complex star formulation (Osterwalder–Schrader 1975, axiom E2); OS4 is split into
clustering and ergodicity. The Challenge restates these verbatim, adding only the
existential packaging and the pointwise characterisation of the transformed test functions
described above — with the four existence conjuncts keeping the characterised axioms
non-vacuous, and `StatementEquivalence.lean` certifying the equivalence with the
fully-constructed formulation.

import Challenge

/-!
# Equivalence of the constructed and characterised Challenge statements

The registry Challenge exists in two formulations: the original 655-line file, in which
every transformed test function entering an OS axiom (Euclidean pullback, OS star, time
translate, spacetime translate, smeared mollifier) is CONSTRUCTED as a Schwartz map, and
the slimmed 389-line file, in which each axiom instead QUANTIFIES over any test function
with the required pointwise values, with existence conjuncts in the theorem guarding
against vacuity.

This file proves the two are equivalent, axiom by axiom and for the full theorem
statements. It imports the slim `Challenge`, reproduces the original file's constructed
apparatus and axiom definitions verbatim under the namespace `Challenge.Orig` (the shared
foundation — spacetime, test functions, pairings, generating functionals, `timeReflection`,
`timeShift`, the bump machinery — is byte-identical in the two files, so it is taken from
the slim import), and proves:

* `OS1_iff`, `OS2_iff`, `OS3_iff`, `OS4_Clustering_iff`, `OS4_Ergodicity_iff`,
  `twoPointIntegrable_iff` — each original axiom holds iff its characterised counterpart
  does, for every measure;
* `euclideanPullbackExists`, `timeReflectionStarExists`, `timeTranslationExists`,
  `translationExists` — the four existence conjuncts hold outright;
* `statements_equiv` — the two theorem statements (the full `∃ μ, …` propositions) are
  equivalent, for every `d ≥ 2` and every mass.

This file is a verification artifact, not part of the registry pair.
-/

namespace Challenge

namespace Orig

open MeasureTheory Complex

noncomputable section

variable {d : ℕ}

lemma sub_const_hasTemperateGrowth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) : Function.HasTemperateGrowth (fun x : E => x - a) := by fun_prop

lemma sub_const_antilipschitz {E : Type*} [NormedAddCommGroup E] (a : E) :
    AntilipschitzWith 1 (fun x : E => x - a) := by
  intro x y
  simp [edist_dist, dist_eq_norm]

/-- Translation of a Schwartz function by a vector: `(translateSchwartz f a)(x) = f(x − a)`.
Translation `x ↦ x − a` is an isometry with temperate growth, so it preserves the Schwartz
class. -/
def translateSchwartz (f : TestFunction d) (a : SpaceTime d) : TestFunction d :=
  SchwartzMap.compCLMOfAntilipschitz ℝ (sub_const_hasTemperateGrowth a)
    (sub_const_antilipschitz a) f
/-- The two-point function smeared against a mollifier: the covariance evaluated on a
normalized bump translated to `x` against the same bump at the origin,
`∫∫ φ(u − x) ⟨φ(u) φ(v)⟩ φ(v) du dv`. -/
def SmearedTwoPointFunction (dμ_config : ProbabilityMeasure (FieldConfiguration d))
    (φ : ContDiffBump (0 : SpaceTime d)) (x : SpaceTime d) : ℝ :=
  SchwingerFunction₂ dμ_config (translateSchwartz (bumpToSchwartz φ) x) (bumpToSchwartz φ)
/-- The pointwise two-point function `S₂(x)`, defined as the mollifier limit of smeared
two-point functions along the standard bump sequence, regularized to `0` at the coincident
point `x = 0` (where the two-point function of a quantum field diverges). -/
def SchwingerTwoPointFunction
    (dμ_config : ProbabilityMeasure (FieldConfiguration d)) (x : SpaceTime d) : ℝ :=
  if x = 0 then 0
  else
    Filter.limUnder Filter.atTop
      (fun n : ℕ => if hn : n = 0 then 0
        else SmearedTwoPointFunction dμ_config (standardBumpSequence n hn) x)
/-! ## The Euclidean group and its action on test functions -/

/-- Orthogonal linear isometries of `ℝ^d`: the group `O(d)`. -/
abbrev Rotation (d : ℕ) : Type :=
  LinearIsometry (RingHom.id ℝ) (SpaceTime d) (SpaceTime d)

/-- A Euclidean motion of `ℝ^d`: a rotation/reflection `R ∈ O(d)` followed by a translation,
`x ↦ R x + t`. These form the Euclidean group `E(d) = ℝ^d ⋊ O(d)`. -/
structure E (d : ℕ) where
  /-- The rotation/reflection part. -/
  R : Rotation d
  /-- The translation part. -/
  t : SpaceTime d

/-- The action of a Euclidean motion on a spacetime point: `g • x = R x + t`. -/
def act (g : E d) (x : SpaceTime d) : SpaceTime d := g.R x + g.t

/-- The inverse of a linear isometry of `ℝ^d` (finite dimension makes every isometry
surjective, so the inverse isometry exists). -/
noncomputable def Rotation.inv (g : Rotation d) : Rotation d :=
  ((g.toLinearIsometryEquiv rfl).symm).toLinearIsometry

/-- The inverse Euclidean motion: `(R, t)⁻¹ = (R⁻¹, −R⁻¹ t)`. -/
noncomputable instance instInvE : Inv (E d) where
  inv g := ⟨Rotation.inv g.R, -(Rotation.inv g.R) g.t⟩

/-- The pullback map underlying the action of `g` on functions: `x ↦ g⁻¹ • x`. -/
noncomputable def euclidean_pullback (g : E d) : SpaceTime d → SpaceTime d := act g⁻¹

lemma contDiff_act_inv (g : E d) : ContDiff ℝ ⊤ (act g⁻¹) := by
  have h₁ : ContDiff ℝ ⊤ (fun x : SpaceTime d => g⁻¹.R x) := g⁻¹.R.contDiff
  have h₂ : ContDiff ℝ ⊤ (fun _ : SpaceTime d => g⁻¹.t) := contDiff_const
  unfold act
  exact h₁.add h₂

lemma fderiv_linear_add_const (L : SpaceTime d →L[ℝ] SpaceTime d) (c : SpaceTime d)
    (x : SpaceTime d) : fderiv ℝ (fun y => L y + c) x = fderiv ℝ L x :=
  fderiv_add_const _

theorem fderiv_act_inv_eq_linear (g : E d) :
    (fun x => fderiv ℝ (act g⁻¹) x) = fun _ => g⁻¹.R.toContinuousLinearMap := by
  ext x v i
  let L := g⁻¹.R.toContinuousLinearMap
  calc (fderiv ℝ (act g⁻¹) x v) i
      = (fderiv ℝ (fun y => L y + g⁻¹.t) x v) i := rfl
    _ = ((fderiv ℝ (fun y => L y + g⁻¹.t) x) v) i := rfl
    _ = ((fderiv ℝ L x) v) i := by rw [fderiv_linear_add_const]
    _ = (L v) i := by rw [ContinuousLinearMap.fderiv]

theorem fderiv_has_temperate_growth (g : E d) :
    Function.HasTemperateGrowth (fun x => fderiv ℝ (act g⁻¹) x) := by
  rw [fderiv_act_inv_eq_linear g]
  exact Function.HasTemperateGrowth.const _

theorem act_inv_poly_bound (g : E d) :
    ∃ k : ℕ, ∃ C : ℝ, ∀ x : SpaceTime d, ‖act g⁻¹ x‖ ≤ C * (1 + ‖x‖) ^ k := by
  use 1, (1 + ‖g⁻¹.t‖)
  intro x
  have : act g⁻¹ x = g⁻¹.R x + g⁻¹.t := by simp [act]
  rw [this]
  calc ‖g⁻¹.R x + g⁻¹.t‖
      ≤ ‖g⁻¹.R x‖ + ‖g⁻¹.t‖ := norm_add_le _ _
    _ = ‖x‖ + ‖g⁻¹.t‖ := by rw [g⁻¹.R.norm_map x]
    _ ≤ (1 + ‖g⁻¹.t‖) * (1 + ‖x‖) ^ 1 := by
        simp only [pow_one]
        ring_nf
        have h1 : 0 ≤ ‖x‖ := norm_nonneg x
        have h2 : 0 ≤ ‖g⁻¹.t‖ := norm_nonneg _
        linarith [mul_nonneg h2 h1]

/-- The pullback map `x ↦ g⁻¹ • x` has temperate growth (an affine map). -/
lemma euclidean_pullback_temperate_growth (g : E d) :
    Function.HasTemperateGrowth (euclidean_pullback g) := by
  unfold euclidean_pullback
  obtain ⟨k, C, hbound⟩ := act_inv_poly_bound g
  exact Function.HasTemperateGrowth.of_fderiv (fderiv_has_temperate_growth g)
    ((contDiff_act_inv g).differentiable WithTop.top_ne_zero) hbound

/-- The pullback map satisfies the polynomial lower bound needed to precompose Schwartz
functions: `‖x‖ ≤ C (1 + ‖g⁻¹ • x‖)^k`. -/
lemma euclidean_pullback_polynomial_bounds (g : E d) :
    ∃ (k : ℕ) (C : ℝ), ∀ x : SpaceTime d, ‖x‖ ≤ C * (1 + ‖euclidean_pullback g x‖) ^ k := by
  use 1, (1 + ‖g⁻¹.t‖)
  intro x
  simp only [pow_one, euclidean_pullback, act]
  have h_iso : ‖g⁻¹.R x‖ = ‖x‖ := g⁻¹.R.norm_map x
  rw [← h_iso]
  have h_ineq : ‖g⁻¹.R x‖ ≤ ‖g⁻¹.R x + g⁻¹.t‖ + ‖g⁻¹.t‖ := norm_le_add_norm_add _ _
  calc ‖g⁻¹.R x‖
      ≤ ‖g⁻¹.R x + g⁻¹.t‖ + ‖g⁻¹.t‖ := h_ineq
    _ ≤ (1 + ‖g⁻¹.t‖) * (1 + ‖g⁻¹.R x + g⁻¹.t‖) := by
        have h1 : 0 ≤ ‖g⁻¹.R x + g⁻¹.t‖ := norm_nonneg _
        have h2 : 0 ≤ ‖g⁻¹.t‖ := norm_nonneg _
        ring_nf
        linarith [mul_nonneg h2 h1]

/-- The action of a Euclidean motion on complex test functions by pullback:
`(g • f)(x) = f(g⁻¹ • x)`. -/
noncomputable def euclidean_action (g : E d) (f : TestFunctionℂ d) : TestFunctionℂ d :=
  SchwartzMap.compCLM (𝕜 := ℂ)
    (hg := euclidean_pullback_temperate_growth g)
    (hg_upper := euclidean_pullback_polynomial_bounds g) f
/-- Time reflection as a linear map on `ℝ^d`. -/
def timeReflectionLinear [Fact (2 ≤ d)] : SpaceTime d →ₗ[ℝ] SpaceTime d :=
  { toFun := timeReflection
    map_add' := by
      intro x y
      apply PiLp.ext
      intro i
      simp only [timeReflection, WithLp.equiv_symm_apply]
      by_cases h : i = 0
      · subst h
        simp [Function.update_self]
        ring
      · simp [Function.update_of_ne h]
    map_smul' := by
      intro c x
      apply PiLp.ext
      intro i
      simp only [timeReflection, RingHom.id_apply, WithLp.equiv_symm_apply]
      by_cases h : i = 0
      · subst h
        simp [Function.update_self]
      · simp [Function.update_of_ne h] }

/-- Time reflection as a continuous linear map on `ℝ^d`. -/
noncomputable def timeReflectionCLM [Fact (2 ≤ d)] : SpaceTime d →L[ℝ] SpaceTime d :=
  timeReflectionLinear.toContinuousLinearMap (E := SpaceTime d) (F' := SpaceTime d)

open InnerProductSpace in
/-- Time reflection preserves the Euclidean inner product. -/
lemma timeReflection_inner_map [Fact (2 ≤ d)] (x y : SpaceTime d) :
    ⟪timeReflection x, timeReflection y⟫_ℝ = ⟪x, y⟫_ℝ := by
  simp only [inner]
  congr 1
  ext i
  simp only [timeReflection]
  by_cases h : i = 0
  · rw [h]; simp
  · simp [h]

/-- Time reflection is an involution: `Θ ∘ Θ = id`. -/
@[simp] lemma timeReflection_involutive [Fact (2 ≤ d)] (x : SpaceTime d) :
    timeReflection (timeReflection x) = x := by
  apply PiLp.ext
  intro i
  simp only [timeReflection, WithLp.equiv_symm_apply]
  by_cases h : i = 0
  · subst h
    simp [Function.update_self]
  · simp [Function.update_of_ne h]

open InnerProductSpace in
/-- Time reflection as a linear isometry equivalence of `ℝ^d`. -/
def timeReflectionLE [Fact (2 ≤ d)] : SpaceTime d ≃ₗᵢ[ℝ] SpaceTime d :=
  { toFun := timeReflection
    invFun := timeReflection
    left_inv := timeReflection_involutive
    right_inv := timeReflection_involutive
    map_add' := timeReflectionLinear.map_add'
    map_smul' := timeReflectionLinear.map_smul'
    norm_map' := by
      intro x
      show ‖timeReflection x‖ = ‖x‖
      have h : ⟪timeReflection x, timeReflection x⟫_ℝ = ⟪x, x⟫_ℝ := timeReflection_inner_map x x
      have h1 : ⟪timeReflection x, timeReflection x⟫_ℝ = ‖timeReflection x‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq]
      have h2 : ⟪x, x⟫_ℝ = ‖x‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq]
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
      rw [← h1, ← h2, h] }

/-- Time reflection has temperate growth (it is a linear isometry). -/
lemma timeReflection_hasTemperateGrowth [Fact (2 ≤ d)] :
    Function.HasTemperateGrowth (timeReflection (d := d)) := by
  have h : timeReflection (d := d) = ⇑(timeReflectionCLM (d := d)) := rfl
  rw [h]
  exact ContinuousLinearMap.hasTemperateGrowth (timeReflectionCLM (d := d))

/-- Time reflection is antilipschitz (it is an isometry). -/
lemma timeReflection_antilipschitz [Fact (2 ≤ d)] :
    AntilipschitzWith 1 (timeReflection (d := d)) := by
  have h : timeReflection (d := d) = ⇑(timeReflectionLE (d := d)) := rfl
  rw [h]
  exact (timeReflectionLE (d := d)).isometry.antilipschitz

/-- Composition with time reflection, `f ↦ f ∘ Θ`, as a continuous linear map on complex
test functions. -/
noncomputable def compTimeReflection [Fact (2 ≤ d)] : TestFunctionℂ d →L[ℝ] TestFunctionℂ d :=
  SchwartzMap.compCLMOfAntilipschitz ℝ timeReflection_hasTemperateGrowth
    timeReflection_antilipschitz

lemma starRingEnd_iteratedFDeriv_norm_eq (g : TestFunctionℂ d) (n : ℕ) (x : SpaceTime d) :
    ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (g x)) x‖ = ‖iteratedFDeriv ℝ n g x‖ := by
  have h : (fun x => starRingEnd ℂ (g x)) = Complex.conjLIE ∘ g := by
    ext y
    rw [Function.comp_apply]
    exact congr_fun (@RCLike.conjLIE_apply ℂ _) (g y)
  rw [h]
  exact LinearIsometryEquiv.norm_iteratedFDeriv_comp_left Complex.conjLIE g x n

/-- The Osterwalder–Schrader star operation on complex test functions: time reflection
followed by pointwise complex conjugation, `(star f)(x) = conj (f (Θ x))`. -/
noncomputable def starTestFunction [Fact (2 ≤ d)] (f : TestFunctionℂ d) : TestFunctionℂ d :=
  let f_reflected := compTimeReflection f
  ⟨fun x => starRingEnd ℂ (f_reflected x),
   by
     apply ContDiff.comp
     · exact ContinuousLinearMap.contDiff (Complex.conjLIE.toContinuousLinearMap)
     · exact f_reflected.smooth ⊤,
   fun k n => by
     obtain ⟨C, hC⟩ := f_reflected.decay' k n
     use C
     intro x
     have h_eq : ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (f_reflected x)) x‖ =
         ‖iteratedFDeriv ℝ n f_reflected x‖ :=
       starRingEnd_iteratedFDeriv_norm_eq f_reflected n x
     calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (f_reflected x)) x‖
         = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f_reflected x‖ := by rw [h_eq]
       _ ≤ C := hC x⟩

/-- The star operation as a `Star` instance on complex test functions. -/
noncomputable instance instStarTestFunction [Fact (2 ≤ d)] : Star (TestFunctionℂ d) where
  star f := starTestFunction f
/-- The ℂ-submodule of complex test functions supported in the positive-time half-space. -/
def PositiveTimeTestFunctionsℂ.submodule [Fact (2 ≤ d)] : Submodule ℂ (TestFunctionℂ d) where
  carrier := { f : TestFunctionℂ d | tsupport f ⊆ positiveTimeSet }
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    suffices h : tsupport (0 : TestFunctionℂ d) = ∅ by
      rw [h]
      apply Set.empty_subset
    rw [tsupport_eq_empty_iff]
    rfl
  add_mem' := fun {f g} hf hg => Set.Subset.trans (tsupport_add f g) (Set.union_subset hf hg)
  smul_mem' := by
    intro c f hf
    refine (tsupport_smul_subset_right (fun _ : SpaceTime d => c) f).trans hf

/-- Complex test functions supported at positive time (the domain of the OS3 reflection
positivity form). -/
abbrev PositiveTimeTestFunctionℂ (d : ℕ) [Fact (2 ≤ d)] : Type :=
  PositiveTimeTestFunctionsℂ.submodule (d := d)
/-- Time shift preserves the Euclidean distance. -/
lemma timeShift_dist (s : ℝ) (u v : SpaceTime d) :
    dist (timeShift s u) (timeShift s v) = dist u v := by
  simp only [EuclideanSpace.dist_eq, timeShift]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · congr 1; simp only [Real.dist_eq, add_sub_add_right_eq_sub]
  · rfl

/-- Time shift is an isometry of `ℝ^d`. -/
lemma timeShift_isometry (s : ℝ) : Isometry (timeShift (d := d) s) := by
  rw [isometry_iff_dist_eq]
  exact fun u v => timeShift_dist s u v

lemma timeShift_antilipschitz (s : ℝ) : AntilipschitzWith 1 (timeShift (d := d) s) :=
  (timeShift_isometry s).antilipschitz

/-- The constant vector expressing `timeShift` as `id + const`. -/
def timeShiftConst (s : ℝ) : SpaceTime d :=
  WithLp.toLp 2 (fun i => if i.val = 0 then s else 0)

lemma timeShift_eq_add_const (s : ℝ) (u : SpaceTime d) :
    timeShift s u = u + timeShiftConst s := by
  simp only [timeShift, timeShiftConst]
  ext i
  simp only [PiLp.add_apply]
  split_ifs with h <;> ring

/-- Time shift has temperate growth (it is an affine map). -/
lemma timeShift_hasTemperateGrowth (s : ℝ) :
    Function.HasTemperateGrowth (timeShift (d := d) s) := by
  have h_fderiv_temperate : Function.HasTemperateGrowth (fderiv ℝ (timeShift (d := d) s)) := by
    have h_eq : fderiv ℝ (timeShift (d := d) s) =
        fun _ => ContinuousLinearMap.id ℝ (SpaceTime d) := by
      ext x v
      have h : timeShift (d := d) s = fun u => u + timeShiftConst s :=
        funext (timeShift_eq_add_const s)
      rw [h]
      simp only [fderiv_add_const, fderiv_fun_id, ContinuousLinearMap.id_apply]
    rw [h_eq]
    exact Function.HasTemperateGrowth.const _
  have h_diff : Differentiable ℝ (timeShift (d := d) s) := by
    intro x
    have h : timeShift (d := d) s = fun u => u + timeShiftConst s :=
      funext (timeShift_eq_add_const s)
    rw [h]
    exact differentiableAt_id.add_const _
  have h_bound : ∀ x : SpaceTime d,
      ‖timeShift s x‖ ≤ (1 + ‖timeShiftConst (d := d) s‖) * (1 + ‖x‖) ^ 1 := by
    intro x
    rw [timeShift_eq_add_const, pow_one]
    calc ‖x + timeShiftConst s‖
        ≤ ‖x‖ + ‖timeShiftConst s‖ := norm_add_le _ _
      _ ≤ (1 + ‖timeShiftConst s‖) * (1 + ‖x‖) := by
          nlinarith [norm_nonneg x, norm_nonneg (timeShiftConst (d := d) s)]
  exact Function.HasTemperateGrowth.of_fderiv h_fderiv_temperate h_diff h_bound

/-- Time translation `f ↦ f ∘ (timeShift s)` as a continuous linear map on real test
functions: `(T_s f)(t, x̄) = f(t + s, x̄)`. -/
def timeTranslationSchwartzCLM (s : ℝ) : TestFunction d →L[ℝ] TestFunction d :=
  SchwartzMap.compCLMOfAntilipschitz ℝ (timeShift_hasTemperateGrowth s)
    (timeShift_antilipschitz s)

/-- Time translation on tempered distributions, by duality:
`⟨T_s ω, f⟩ = ⟨ω, T_{−s} f⟩`. -/
def timeTranslationDistribution (s : ℝ) (ω : FieldConfiguration d) : FieldConfiguration d :=
  ω.comp (timeTranslationSchwartzCLM (-s))
/-! ## The original axiom definitions -/

/-- Local integrability of the pointwise two-point function, the additional condition OS1
imposes in the borderline case `p = 2`. -/
def TwoPointIntegrable (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  LocallyIntegrable (fun x => SchwingerTwoPointFunction dμ_config x) volume

/-- **OS1 (Regularity):** the generating functional satisfies an exponential bound
`‖Z[f]‖ ≤ exp (c (‖f‖₁ + ‖f‖ₚᵖ))` for some `1 ≤ p ≤ 2` and `c > 0`; when `p = 2`, the
two-point function is additionally required to be locally integrable. -/
def OS1_Regularity (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∃ (p : ℝ) (c : ℝ), 1 ≤ p ∧ p ≤ 2 ∧ c > 0 ∧
    (∀ (f : TestFunctionℂ d),
      ‖GJGeneratingFunctionalℂ dμ_config f‖ ≤
        Real.exp (c * (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖ ^ p ∂volume))) ∧
    (p = 2 → TwoPointIntegrable dμ_config)

/-- **OS2 (Euclidean invariance):** the generating functional is invariant under the pullback
action of every Euclidean motion. -/
def OS2_EuclideanInvariance (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (g : E d) (f : TestFunctionℂ d),
    GJGeneratingFunctionalℂ dμ_config f =
    GJGeneratingFunctionalℂ dμ_config (euclidean_action g f)

/-- **OS3 (Reflection positivity):** the generating functional defines a positive
semi-definite Hermitian form on test functions supported at positive time. This is the
complex (star) formulation of Osterwalder–Schrader (1975, axiom E2): for all positive-time
complex test functions `f₁, …, fₙ` and coefficients `c₁, …, cₙ ∈ ℂ`,
`∑ᵢⱼ c̄ᵢ cⱼ Z[fᵢ − fⱼ*] ≥ 0`, where `(f*)(x) = conj (f (Θ x))` combines time reflection
with complex conjugation. -/
def OS3_ReflectionPositivity [Fact (2 ≤ d)]
    (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (n : ℕ) (f : Fin n → PositiveTimeTestFunctionℂ d) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      GJGeneratingFunctionalℂ dμ_config
        ((f i).val - star ((f j).val))).re

/-- **OS4 (Clustering):** correlations of distant regions decay:
`Z[f + T_a g] → Z[f] Z[g]` as the translation `‖a‖ → ∞`, so that widely separated test
functions become statistically independent. -/
def OS4_Clustering (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (f g : TestFunction d) (ε : ℝ), ε > 0 → ∃ (R : ℝ), R > 0 ∧ ∀ (a : SpaceTime d),
    ‖a‖ > R →
    ‖GJGeneratingFunctional dμ_config (f + translateSchwartz g a) -
     GJGeneratingFunctional dμ_config f * GJGeneratingFunctional dμ_config g‖ < ε

/-- **OS4 (Ergodicity):** for observables `A(ω) = ∑ⱼ zⱼ e^{⟨ω, fⱼ⟩}`, the time average
`(1/T) ∫₀ᵀ A(T_s ω) ds` converges to the expectation `𝔼_μ[A]` in `L²(μ)` as `T → ∞`. -/
def OS4_Ergodicity (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ) (f : Fin n → TestFunctionℂ d),
    let μ := dμ_config.toMeasure
    let A : FieldConfiguration d → ℂ := fun ω =>
      ∑ j, z j * Complex.exp (distributionPairingℂ_real ω (f j))
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ ω, ‖(1 / T) * ∫ s in Set.Icc (0 : ℝ) T,
          A (timeTranslationDistribution s ω)
          - ∫ ω', A ω' ∂μ‖ ^ 2 ∂μ)
      Filter.atTop
      (nhds 0)

end

end Orig

/-! ## Equivalence -/

noncomputable section

open MeasureTheory Complex

variable {d : ℕ}

/-! ### Pointwise formulas for the constructed transforms

Each constructed transform evaluates by its defining formula. All four are definitional
(`rfl`), which is the heart of the equivalence: the characterised hypotheses are satisfied
by the constructions on the nose. -/

lemma translateSchwartz_apply (f : TestFunction d) (a x : SpaceTime d) :
    Orig.translateSchwartz f a x = f (x - a) := rfl

lemma euclidean_action_apply (g : Orig.E d) (f : TestFunctionℂ d) (x : SpaceTime d) :
    Orig.euclidean_action g f x = f (Orig.act g⁻¹ x) := rfl

lemma star_apply [Fact (2 ≤ d)] (f : TestFunctionℂ d) (x : SpaceTime d) :
    (star f) x = starRingEnd ℂ (f (timeReflection x)) := rfl

lemma timeTranslation_apply (s : ℝ) (g : TestFunction d) (x : SpaceTime d) :
    Orig.timeTranslationSchwartzCLM s g x = g (timeShift s x) := rfl

/-- Upgrading a linear isometry of `ℝ^d` to an equivalence (possible because finite
dimension forces surjectivity) and forgetting back down is the identity. -/
lemma toLinearIsometryEquiv_toLinearIsometry (R : SpaceTime d ≃ₗᵢ[ℝ] SpaceTime d) :
    R.toLinearIsometry.toLinearIsometryEquiv rfl = R :=
  LinearIsometryEquiv.ext fun _ => rfl

/-- The inverse Euclidean motion acts by `x ↦ R⁻¹ (x − t)`, with `R⁻¹` realised as the
`symm` of the linear isometry equivalence associated to the rotation part. -/
lemma act_inv_eq (g : Orig.E d) (x : SpaceTime d) :
    Orig.act g⁻¹ x = (g.R.toLinearIsometryEquiv rfl).symm (x - g.t) := by
  show (g.R.toLinearIsometryEquiv rfl).symm x + -((g.R.toLinearIsometryEquiv rfl).symm g.t) =
    (g.R.toLinearIsometryEquiv rfl).symm (x - g.t)
  rw [map_sub, sub_eq_add_neg]

/-! ### The four existence conjuncts hold outright -/

theorem euclideanPullbackExists (d : ℕ) : EuclideanPullbackExists d := by
  intro R b f
  refine ⟨Orig.euclidean_action ⟨R.toLinearIsometry, b⟩ f, fun x => ?_⟩
  rw [euclidean_action_apply, act_inv_eq, toLinearIsometryEquiv_toLinearIsometry]

theorem timeReflectionStarExists (d : ℕ) [Fact (2 ≤ d)] : TimeReflectionStarExists d :=
  fun f => ⟨star f, fun _ => rfl⟩

theorem timeTranslationExists (d : ℕ) : TimeTranslationExists d :=
  fun s g => ⟨Orig.timeTranslationSchwartzCLM s g, fun _ => rfl⟩

theorem translationExists (d : ℕ) : TranslationExists d :=
  fun g a => ⟨Orig.translateSchwartz g a, fun _ => rfl⟩

/-! ### The per-axiom equivalences -/

/-- The constructed and characterised formulations of OS2 agree for every measure. The
original quantifies over Euclidean motions whose rotation part is a `LinearIsometry`
(surjectivity being automatic in finite dimension); the characterised form quantifies over
`LinearIsometryEquiv`, and the proof identifies the two. -/
theorem OS2_iff (μ : ProbabilityMeasure (FieldConfiguration d)) :
    Orig.OS2_EuclideanInvariance μ ↔ OS2_EuclideanInvariance μ := by
  constructor
  · intro h R b f f' hf'
    have hf'eq : f' = Orig.euclidean_action ⟨R.toLinearIsometry, b⟩ f :=
      SchwartzMap.ext fun x => by
        rw [hf' x, euclidean_action_apply, act_inv_eq, toLinearIsometryEquiv_toLinearIsometry]
    rw [hf'eq]
    exact h ⟨R.toLinearIsometry, b⟩ f
  · intro h g f
    exact h (g.R.toLinearIsometryEquiv rfl) g.t f (Orig.euclidean_action g f) fun x => by
      rw [euclidean_action_apply, act_inv_eq]

/-- The constructed and characterised formulations of OS3 agree for every measure: subtype
membership in the positive-time submodule is exactly the `tsupport` hypothesis, and the
constructed star is the unique test function with the characterised values. -/
theorem OS3_iff [Fact (2 ≤ d)] (μ : ProbabilityMeasure (FieldConfiguration d)) :
    Orig.OS3_ReflectionPositivity μ ↔ OS3_ReflectionPositivity μ := by
  constructor
  · intro h n f fstar c hsupp hstar
    have hfs : ∀ j, fstar j = star (f j) :=
      fun j => SchwartzMap.ext fun x => by rw [hstar j x, star_apply]
    simp only [hfs]
    exact h n (fun i => ⟨f i, hsupp i⟩) c
  · intro h n f c
    exact h n (fun i => (f i).val) (fun j => star ((f j).val)) c
      (fun i => (f i).property) (fun j _ => rfl)

/-- The constructed and characterised formulations of the two-point local-integrability
condition agree for every measure. -/
theorem twoPointIntegrable_iff (μ : ProbabilityMeasure (FieldConfiguration d)) :
    Orig.TwoPointIntegrable μ ↔ TwoPointIntegrable μ := by
  constructor
  · intro h smear hsmear
    have hs : ∀ (φ : ContDiffBump (0 : SpaceTime d)) x,
        smear φ x = Orig.translateSchwartz (bumpToSchwartz φ) x :=
      fun φ x => SchwartzMap.ext fun y => hsmear φ x y
    simp only [hs]
    exact h
  · intro h
    exact h (fun φ x => Orig.translateSchwartz (bumpToSchwartz φ) x) fun _ _ _ => rfl

/-- The constructed and characterised formulations of OS1 agree for every measure. -/
theorem OS1_iff (μ : ProbabilityMeasure (FieldConfiguration d)) :
    Orig.OS1_Regularity μ ↔ OS1_Regularity μ := by
  unfold Orig.OS1_Regularity OS1_Regularity
  simp only [twoPointIntegrable_iff]

/-- The constructed and characterised formulations of OS4 clustering agree for every
measure. -/
theorem OS4_Clustering_iff (μ : ProbabilityMeasure (FieldConfiguration d)) :
    Orig.OS4_Clustering μ ↔ OS4_Clustering μ := by
  constructor
  · intro h f g ε hε
    obtain ⟨R, hR, hbound⟩ := h f g ε hε
    refine ⟨R, hR, fun a g' ha hg' => ?_⟩
    have hg'eq : g' = Orig.translateSchwartz g a := SchwartzMap.ext fun x => hg' x
    rw [hg'eq]
    exact hbound a ha
  · intro h f g ε hε
    obtain ⟨R, hR, hbound⟩ := h f g ε hε
    exact ⟨R, hR, fun a ha => hbound a (Orig.translateSchwartz g a) ha fun _ => rfl⟩

/-- The constructed and characterised formulations of OS4 ergodicity agree for every
measure: any family with the translation values IS the constructed time-translation
operator, and the translated observable then coincides with the observable composed with
the dual translation on distributions. -/
theorem OS4_Ergodicity_iff (μ : ProbabilityMeasure (FieldConfiguration d)) :
    Orig.OS4_Ergodicity μ ↔ OS4_Ergodicity μ := by
  constructor
  · intro h translate htrans n z f
    have htr : translate = fun s g => Orig.timeTranslationSchwartzCLM s g :=
      funext fun s => funext fun g => SchwartzMap.ext fun x => htrans s g x
    subst htr
    exact h n z f
  · intro h n z f
    exact h (fun s g => Orig.timeTranslationSchwartzCLM s g) (fun _ _ _ => rfl) n z f

/-! ### The theorem statements are equivalent -/

/-- **The two Challenge statements are equivalent.** The proposition proved by the original
(constructed) Challenge and the proposition proved by the characterised Challenge imply
each other, for every dimension `d ≥ 2` and every mass parameter. In particular the
characterised statement is not weaker: its existence conjuncts are theorems, and each
characterised axiom pins the transformed test function down uniquely (two Schwartz
functions with the same values are equal). -/
theorem statements_equiv (d : ℕ) [Fact (2 ≤ d)] (m : ℝ) :
    (∃ μ : ProbabilityMeasure (FieldConfiguration d),
      (∀ f : TestFunction d,
        GJGeneratingFunctional μ f =
          Complex.exp (-(1 / 2 : ℂ) * ((covarianceForm d m f f : ℝ) : ℂ))) ∧
      OS0_Analyticity μ ∧ Orig.OS1_Regularity μ ∧ Orig.OS2_EuclideanInvariance μ ∧
      Orig.OS3_ReflectionPositivity μ ∧ Orig.OS4_Clustering μ ∧ Orig.OS4_Ergodicity μ) ↔
    (∃ μ : ProbabilityMeasure (FieldConfiguration d),
      (∀ f : TestFunction d,
        GJGeneratingFunctional μ f =
          Complex.exp (-(1 / 2 : ℂ) * ((covarianceForm d m f f : ℝ) : ℂ))) ∧
      EuclideanPullbackExists d ∧ TimeReflectionStarExists d ∧ TimeTranslationExists d ∧
      TranslationExists d ∧
      OS0_Analyticity μ ∧ OS1_Regularity μ ∧ OS2_EuclideanInvariance μ ∧
      OS3_ReflectionPositivity μ ∧ OS4_Clustering μ ∧ OS4_Ergodicity μ) := by
  constructor
  · rintro ⟨μ, hchar, h0, h1, h2, h3, h4c, h4e⟩
    exact ⟨μ, hchar, euclideanPullbackExists d, timeReflectionStarExists d,
      timeTranslationExists d, translationExists d, h0, (OS1_iff μ).mp h1,
      (OS2_iff μ).mp h2, (OS3_iff μ).mp h3, (OS4_Clustering_iff μ).mp h4c,
      (OS4_Ergodicity_iff μ).mp h4e⟩
  · rintro ⟨μ, hchar, -, -, -, -, h0, h1, h2, h3, h4c, h4e⟩
    exact ⟨μ, hchar, h0, (OS1_iff μ).mpr h1, (OS2_iff μ).mpr h2, (OS3_iff μ).mpr h3,
      (OS4_Clustering_iff μ).mpr h4c, (OS4_Ergodicity_iff μ).mpr h4e⟩

end

end Challenge

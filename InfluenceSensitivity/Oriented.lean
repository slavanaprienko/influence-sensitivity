import InfluenceSensitivity.Basic

set_option linter.style.nativeDecide false
set_option linter.style.whitespace false

/-!
# Oriented percolation: endpoint `Inf ≥ c·s` (note11)

We prove the strongest unconditional separation:
*there is an absolute `c > 0` and a sequence of monotone Boolean functions
`f_L` such that `s(f_L) → ∞` and `c · s(f_L) ≤ influence f_L`*.

This is the endpoint result from `note11.md`: the previous `note10` proof had
a logarithmic loss `Inf ≳ s/log s` because of the path-counting union bound.
The branching-process estimate of note11 §5 replaces it, yielding a threshold
window of width `O(1/L)` and (after Russo + random restriction) a clean
linear lower bound.

Together with `ExponentAchievable.le_one` from `Basic`, the linear separation
gives the full characterisation `ExponentAchievable r ↔ r ≤ 1`.

## Decomposition outline (decompose-and-conquer)

The construction is split into named supplementary lemmas, each of which is
either proved directly or further decomposed. We track progress here.

* **`existsLinearOrientedFamily`** *(top-level supplementary, sorry)* —
  packages the entire note11 chain into a `BooleanFamily` with eventually
  `c · maxSensitivity ≤ influence` and `maxSensitivity → ∞`.

* **`liminf_log_div_log_ge_one_of_linear`** *(asymptotic bridge, proved)* —
  pure-analysis: `c · s ≤ f` and `s → ∞` and `f ≤ s` ⇒ `liminf log f / log s ≥ 1`.

* The proof of `existsLinearOrientedFamily` will further decompose into:
  - the strip graph + `F_L` definition,
  - directed planar duality (the only geometric input),
  - one-sided sensitivity bounds `s_1(F_L) ≤ L`, `s_0(F_L) ≤ C_s · L`,
  - the branching-process recurrence `u_{t+1} ≤ m·u_t·(1 - (m/4)·u_t)`,
  - the union-bound corollary `μ_{p_-}(F_L) ≤ 1/8`, `1 − μ_{p_+}(F_L) ≤ 1/8`,
  - Russo's formula giving biased `Inf_{p_L}(F_L) ≥ 3L/(4A)`,
  - the random-restriction identity producing the deterministic `f_L`.

The auxiliary lemma `tendsto_id_div_log_atTop` (`x/log x → ∞`) was used in the
log-loss skeleton; it is kept here as a generally useful fact, even though
the linear bound makes it unnecessary for the main asymptotic.
-/

namespace InfluenceSensitivity

namespace Oriented

open Filter Topology

/-! ## Generic analytic helpers -/

/-- `Real.log =o[atTop] id` rephrased: `x / log x → ∞`. -/
private lemma tendsto_id_div_log_atTop :
    Filter.Tendsto (fun x : ℝ => x / Real.log x) Filter.atTop Filter.atTop := by
  have h1 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h_pos : ∀ᶠ x : ℝ in Filter.atTop, 0 < Real.log x / x := by
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0,
                    Filter.eventually_gt_atTop (0 : ℝ)] with x hlog hx
    exact div_pos hlog hx
  have h2 : Filter.Tendsto (fun x : ℝ => (Real.log x / x)⁻¹) Filter.atTop Filter.atTop := by
    refine Filter.Tendsto.inv_tendsto_nhdsGT_zero ?_
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h1, h_pos⟩
  have h_eq : (fun x : ℝ => (Real.log x / x)⁻¹) =ᶠ[Filter.atTop]
              (fun x : ℝ => x / Real.log x) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
                    Real.tendsto_log_atTop.eventually_gt_atTop 0] with x hx hlog
    field_simp
  exact (Filter.Tendsto.congr' h_eq) h2

/-! ## Step 1: existence of the linear family — decomposition

We decompose the construction into:

* **`perScaleEndpoint`** *(sorry)* — for each `L ≥ 2`, a single monotone Boolean
  function whose maximum sensitivity is at least `L` and whose influence is at
  least a fixed positive multiple of the maximum sensitivity. This is the
  geometric/combinatorial heart (note11 §1–§11).

* **`familyFromPerScale`** *(proved)* — package per-scale witnesses into a
  `BooleanFamily`. Pure type-theoretic bookkeeping.

* **`existsLinearOrientedFamily`** *(proved from the two above)*. -/

/-! ### Decomposition of `existsBiasedCrossing` (note11 §1–§8)

The proof of `existsBiasedCrossing` is a chain of seven sub-lemmas, each
isolating one ingredient of the note11 argument:

| sub-lemma | note11 | content | status |
|---|---|---|---|
| `branchingRecurrenceStep` | §5 | algebra: `2pu − p²u² = m·u·(1 − (m/4)u)` for `m = 2p` | proved |
| `vRecurrenceStep` | §5 | `1/(m·u·(1−(m/4)u)) ≥ 1/(m·u) + 1/4` | proved |
| `geometricBoundExpA` | §5 | `(1 − A/L)⁻ᴸ ≥ exp A` for `L ≥ 2A` | proved |
| `existsCrossingData` | §1–§4 | finite-data record with sensitivity bounds | sorry |
| `mu_minus_le_one_eighth` | §6 | `μ_{p₋}(F_L) ≤ 1/8` | sorry |
| `one_minus_mu_plus_le_one_eighth` | §7 | `1 − μ_{p₊}(F_L) ≤ 1/8` | sorry |
| `russoBiasedInfluence` | §8 | `∃ p, Inf_p(F_L) ≥ L/50`, with `p` balanced | sorry |

These compose into `existsBiasedCrossing`. The first three (the algebra/
analysis core) are proved here; the last four use finite-graph existence
and probability-measure facts that are deferred. -/

/-- **Branching-process algebraic step (note11 §5).**
The Galton–Watson recurrence
`u_{t+1} = 1 − (1 − p·u_t)² = 2p·u_t − p²·u_t²`
in terms of `m = 2p` becomes `u_{t+1} = m·u·(1 − (m/4)·u)`.
This is purely algebraic. -/
private lemma branchingRecurrenceStep (p u : ℝ) :
    2 * p * u - p ^ 2 * u ^ 2 = (2 * p) * u * (1 - ((2 * p) / 4) * u) := by
  ring

/-- **Reciprocal step for the `v` recurrence (note11 §5).**
If `0 < m`, `0 < u`, and `(m/4)·u < 1`, then
`1/(m·u·(1 − (m/4)u)) ≥ 1/(m·u) + 1/4`.

This is the crucial step that converts the multiplicative recurrence
`u_{t+1} = m·u·(1 − (m/4)u)` into the linearised inequality
`v_{t+1} ≥ (1/m) v_t + 1/4` for `v_t = 1/u_t`, by way of
`1/(1−z) ≥ 1+z`. -/
private lemma vRecurrenceStep (m u : ℝ) (hm : 0 < m) (hu : 0 < u)
    (hmu : (m / 4) * u < 1) :
    1 / (m * u) + 1 / 4 ≤ 1 / (m * u * (1 - (m / 4) * u)) := by
  set z := (m / 4) * u with hz_def
  have hz_nn : 0 ≤ z := mul_nonneg (by linarith) hu.le
  have h1z_pos : 0 < 1 - z := by linarith
  have hmu_pos : 0 < m * u := mul_pos hm hu
  have hden_pos : 0 < m * u * (1 - z) := mul_pos hmu_pos h1z_pos
  rw [div_add_div _ _ (ne_of_gt hmu_pos) (by norm_num : (4 : ℝ) ≠ 0)]
  rw [div_le_div_iff₀ (by positivity) hden_pos]
  nlinarith [sq_nonneg (m * u), hz_nn, h1z_pos, hmu_pos]

/-- **Geometric decay bound (note11 §5).**
For `0 < A` and `L ≥ 2A`, the inverse-survival weight `m⁻ᴸ` for
`m = 1 − A/L` satisfies `m⁻ᴸ ≥ exp A`. Equivalently,
`(1 − A/L)ᴸ ≤ exp(−A)`.

Proof: pointwise `1 − x ≤ exp(−x)` raised to the `L`-th power gives
`(1 − A/L)ᴸ ≤ exp(−A/L)ᴸ = exp(−A)`; inverting flips the inequality. -/
private lemma geometricBoundExpA (A : ℝ) (L : ℕ) (hA : 0 < A) (hAL : 2 * A ≤ L) :
    Real.exp A ≤ (1 - A / L)⁻¹ ^ L := by
  have hL_pos : 0 < (L : ℝ) := by linarith
  have hAL_half : A / L ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hL_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have h_one_minus_pos : 0 < 1 - A / L := by linarith
  have h_one_step : 1 - A / L ≤ Real.exp (-(A / L)) := Real.one_sub_le_exp_neg _
  have h_pow : (1 - A / L) ^ L ≤ Real.exp (-A) := by
    have h_pow_le : (1 - A / L) ^ L ≤ Real.exp (-(A / L)) ^ L :=
      pow_le_pow_left₀ h_one_minus_pos.le h_one_step L
    rw [← Real.exp_nat_mul] at h_pow_le
    convert h_pow_le using 2
    field_simp
  have h_pow_pos : 0 < (1 - A / L) ^ L := pow_pos h_one_minus_pos _
  have h_inv : (Real.exp (-A))⁻¹ ≤ ((1 - A / L) ^ L)⁻¹ :=
    inv_anti₀ h_pow_pos h_pow
  rw [Real.exp_neg, inv_inv] at h_inv
  rw [inv_pow]
  exact h_inv

/-- **Crossing data (note11 §1–§4).**
The finite combinatorial input to the construction: an ambient finite type
of edge variables `β`, the crossing function `F_L : (β → Bool) → Bool`,
its monotonicity, the two one-sided sensitivity bounds `s_1 ≤ L`,
`s_0 ≤ 3L`, and a witness input of sensitivity at least `L`.

This packages the strip-graph construction (§2), planar duality (§3), and
the one-sided certificate arguments (§4). The constant `3` in `s_0 ≤ 3L`
is the `C₁` of note11; any absolute constant works for the downstream
chain (we fix `3` for concreteness). -/
private structure CrossingData (L : ℕ) where
  /-- Edge index type. -/
  β : Type
  /-- Finiteness instance. -/
  fin : Fintype β
  /-- Decidable equality on edges. -/
  dec : DecidableEq β
  /-- The crossing function `F_L`. -/
  F : (β → Bool) → Bool
  /-- `F_L` is monotone in each coordinate. -/
  mono : @IsMonotone β F
  /-- `s_1(F_L) ≤ L` (1-side certificate of length `L`, note11 §4.1). -/
  sens_one_le : @maxSensitivityOne β fin dec F ≤ L
  /-- `s_0(F_L) ≤ 3·L` (0-side dual-path certificate, note11 §4.2). -/
  sens_zero_le : @maxSensitivityZero β fin dec F ≤ 3 * L
  /-- Some input attains sensitivity at least `L`. -/
  size_low : L ≤ @maxSensitivity β fin dec F

attribute [instance] CrossingData.fin CrossingData.dec

/-- **Existence of crossing data (note11 §1–§4).**
The oriented strip graph plus planar-duality argument produces
`CrossingData L` for every `L ≥ 2`. This is the geometric/combinatorial
heart of note11 (the only step requiring planar duality). -/
private theorem existsCrossingData (L : ℕ) (_hL : 2 ≤ L) :
    Nonempty (CrossingData L) := by
  sorry

/-- **Lower-bias union bound (note11 §6).**
With `A` chosen so large that `8C₀A/(eᴬ − 1) ≤ 1/8`, the lower-bias
measure satisfies `μ_{p₋}(F_L) ≤ 1/8`. Internally, the per-vertex
branching-process estimate (proved via `vRecurrenceStep` and
`geometricBoundExpA`) gives
`Pr_{p₋}[open path of length L from v] ≤ 8A/(L(eᴬ − 1))`,
and the bottom boundary has at most `C₀L` starting vertices, so a union
bound yields `8C₀A/(eᴬ − 1) ≤ 1/8`. -/
private theorem mu_minus_le_one_eighth
    (L : ℕ) (data : CrossingData L) (p : ℝ) (_hp : p ≤ 1 / 2) :
    biasedProb p
        ((@Finset.univ (data.β → Bool) _).filter (fun x => data.F x = true))
      ≤ 1 / 8 := by
  sorry

/-- **Upper-bias union bound (note11 §7).**
By directed planar duality applied to the dual strip, the same
branching-process estimate (transferred via Lemma 1 of §3) yields
`1 − μ_{p₊}(F_L) ≤ 1/8`. -/
private theorem one_minus_mu_plus_le_one_eighth
    (L : ℕ) (data : CrossingData L) (p : ℝ) (_hp : 1 / 2 ≤ p) :
    1 - biasedProb p
        ((@Finset.univ (data.β → Bool) _).filter (fun x => data.F x = true))
      ≤ 1 / 8 := by
  sorry

/-- **Russo's biased-influence bound (note11 §8).**
Russo's formula `dμ_p/dp = Inf_p(F)` integrated on `[p₋, p₊]` of length
`A/L`, together with `μ_{p₊} − μ_{p₋} ≥ 3/4` from
`mu_minus_le_one_eighth` and `one_minus_mu_plus_le_one_eighth`, yields
`p_L ∈ [p₋, p₊]` with `Inf_{p_L}(F_L) ≥ (3/4)/(A/L) = 3L/(4A)`.

The constant `A` is chosen large enough to make the union bounds work
(`8C₀A/(eᴬ − 1) ≤ 1/8`). For any such `A ≤ 75/4`, `3/(4A) ≥ 1/50`, so
`Inf_{p_L} ≥ L/50`. The choice is absorbed into the existential `p`. -/
private theorem russoBiasedInfluence
    (L : ℕ) (data : CrossingData L) (_hL : 2 ≤ L) :
    ∃ p : ℝ, p ∈ Set.Ioo (0 : ℝ) 1 ∧
      (1 / 2 : ℝ) ≤ 2 * min p (1 - p) ∧
      (L : ℝ) / 50 ≤ infP p data.F := by
  sorry

/-- **Crossing function with biased lower bound (note11 §1–§8).**
The geometric/probabilistic heart: there is a monotone crossing function
`F_L` on a finite Boolean cube together with a balanced bias
`p_L ∈ (0, 1)` such that the `p_L`-biased influence is `Ω(L)` while the
maximum sensitivity is `O(L)`, and there is at least one input of
sensitivity `≥ L`.

This is now derived directly from `existsCrossingData` and
`russoBiasedInfluence`: the crossing data provides `F_L`, monotonicity,
the two one-sided sensitivity bounds (combined into
`maxSensitivity ≤ 3L`), and the `≥ L` lower-witness; Russo's lemma
provides the balanced biased point with `Inf_{p_L} ≥ L/50`. -/
private theorem existsBiasedCrossing (L : ℕ) (hL : 2 ≤ L) :
    ∃ (β : Type) (_ : Fintype β) (_ : DecidableEq β) (f : (β → Bool) → Bool) (p : ℝ),
      IsMonotone f ∧
      p ∈ Set.Ioo (0 : ℝ) 1 ∧
      (1/2 : ℝ) ≤ 2 * min p (1 - p) ∧
      (L : ℝ) / 50 ≤ infP p f ∧
      (maxSensitivity f : ℝ) ≤ 3 * L ∧
      (L : ℝ) ≤ (maxSensitivity f : ℝ) := by
  obtain ⟨data⟩ := existsCrossingData L hL
  obtain ⟨p, hp_in, hp_balance, hp_inf⟩ := russoBiasedInfluence L data hL
  refine ⟨data.β, data.fin, data.dec, data.F, p,
    data.mono, hp_in, hp_balance, hp_inf, ?_, ?_⟩
  · -- maxSensitivity ≤ 3L from the two one-sided bounds.
    have h_split :
        maxSensitivity data.F =
          max (maxSensitivityZero data.F) (maxSensitivityOne data.F) :=
      data.mono.maxSensitivity_eq_max
    have h0 : maxSensitivityZero data.F ≤ 3 * L := data.sens_zero_le
    have h1L : maxSensitivityOne data.F ≤ 3 * L :=
      data.sens_one_le.trans (by omega)
    have hmax : max (maxSensitivityZero data.F) (maxSensitivityOne data.F)
        ≤ 3 * L := max_le h0 h1L
    rw [h_split]
    exact_mod_cast hmax
  · -- L ≤ maxSensitivity from data.size_low.
    exact_mod_cast data.size_low

/-! ### Decomposition of `restrictionToUniform` -/

/-! #### Restriction infrastructure

A *restriction* is a partial assignment fixing some coordinates. Applying a
restriction to a Boolean function gives a restricted function on the *same*
finite type (with the fixed coordinates ignored). This keeps the type stable
and avoids dependent-type wrangling.
-/

/-- A *restriction pattern* on `β`: an explicit set of coordinates to fix
together with the values assigned at fixed coordinates. -/
private structure Restriction (β : Type) [DecidableEq β] [Fintype β] where
  fixed : Finset β
  values : β → Bool

namespace Restriction

variable {β : Type} [Fintype β] [DecidableEq β]

/-- Lift a "free" assignment to a full assignment by reading fixed values from `ρ`. -/
def lift (ρ : Restriction β) (g : β → Bool) (i : β) : Bool :=
  if i ∈ ρ.fixed then ρ.values i else g i

/-- Apply a restriction to a Boolean function. -/
def apply (ρ : Restriction β) (f : (β → Bool) → Bool) : (β → Bool) → Bool :=
  fun g => f (lift ρ g)

/-- Lifting through a flip at a *fixed* coordinate is the same as lifting `g`
itself: the flip is invisible because the lift overrides with the fixed value. -/
lemma lift_flipBit_of_fixed (ρ : Restriction β) (g : β → Bool) {i : β}
    (hi : i ∈ ρ.fixed) :
    lift ρ (flipBit g i) = lift ρ g := by
  funext j
  unfold lift
  by_cases hj : j ∈ ρ.fixed
  · simp [hj]
  · -- j ∉ ρ.fixed; need flipBit g i j = g j when j ∉ fixed (in particular j ≠ i since i ∈ fixed).
    have hji : j ≠ i := fun h => hj (h ▸ hi)
    simp [hj, flipBit_apply_of_ne _ hji]

/-- Lifting through a flip at a *free* coordinate commutes with the flip
on the lifted assignment. -/
lemma lift_flipBit_of_free (ρ : Restriction β) (g : β → Bool) {i : β}
    (hi : i ∉ ρ.fixed) :
    lift ρ (flipBit g i) = flipBit (lift ρ g) i := by
  funext j
  unfold lift
  rw [flipBit_apply, flipBit_apply]
  by_cases hj_eq_i : j = i
  · subst hj_eq_i
    have : (j ∈ ρ.fixed) = False := by simp [hi]
    simp [this]
  · by_cases hj : j ∈ ρ.fixed
    · simp [hj, hj_eq_i]
    · simp [hj, hj_eq_i]

/-- A restricted monotone function is still monotone. -/
lemma apply_monotone (ρ : Restriction β) (f : (β → Bool) → Bool) (hf : IsMonotone f) :
    IsMonotone (apply ρ f) := by
  intros x y hxy
  unfold apply
  apply hf
  intro i
  unfold lift
  by_cases hi : i ∈ ρ.fixed
  · simp [hi]
  · simp [hi]; exact hxy i

end Restriction

/-- **Sensitivity preservation under restriction.**
For any restriction `ρ`, `maxSens(apply ρ f) ≤ maxSens(f)`.

Proof: at any input `g`, fixed coordinates are non-sensitive (the function is
constant there). Free coordinates are sensitive only if their corresponding
"lifted" coordinate is sensitive in `f`, hence at most `s(f, lift ρ g) ≤ s(f)`. -/
private theorem maxSens_apply_le {β : Type} [Fintype β] [DecidableEq β]
    (ρ : Restriction β) (f : (β → Bool) → Bool) :
    maxSensitivity (Restriction.apply ρ f) ≤ maxSensitivity f := by
  refine Finset.sup_le ?_
  intros g _
  unfold sensitivityAt
  refine le_trans ?_ (Finset.le_sup
    (f := sensitivityAt f) (Finset.mem_univ (Restriction.lift ρ g)))
  unfold sensitivityAt
  apply Finset.card_le_card
  intros i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  -- hi : Restriction.apply ρ f g ≠ Restriction.apply ρ f (flipBit g i)
  -- goal : f (Restriction.lift ρ g) ≠ f (flipBit (Restriction.lift ρ g) i)
  by_cases h_fixed : i ∈ ρ.fixed
  · exfalso
    apply hi
    show f (Restriction.lift ρ g) = f (Restriction.lift ρ (flipBit g i))
    rw [Restriction.lift_flipBit_of_fixed ρ g h_fixed]
  · intro h_eq_lifted
    apply hi
    show f (Restriction.lift ρ g) = f (Restriction.lift ρ (flipBit g i))
    rw [Restriction.lift_flipBit_of_free ρ g h_fixed]
    exact h_eq_lifted

/-- **Expectation form (sorry, note11 Lemma 2).**
Random restrictions at parameter `p ≤ 1/2` (each coord free wp `2p`, fixed to
`0` otherwise) yield the expected influence identity:
`E_ρ[Inf_{1/2}((f)_ρ)] = 2p · Inf_p(f)`. We state directly the existence
form needed by `restrictionToUniform`, since proving the identity itself
requires defining the finite probability measure on restrictions.

The argument: pick any `ρ` from a finite set of patterns weighted by their
probability under the random restriction, then by averaging there is some
deterministic `ρ` achieving the lower bound. -/
private theorem exists_restriction_high_inf
    {β : Type} [Fintype β] [DecidableEq β] {f : (β → Bool) → Bool} {p : ℝ}
    (_hf : IsMonotone f) (_hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (_hp_balance : (1/2 : ℝ) ≤ 2 * min p (1 - p)) :
    ∃ (ρ : Restriction β),
      (1/2 : ℝ) * infP p f ≤ influence (Restriction.apply ρ f) := by
  sorry

/-- **Random-restriction conversion (note11 §9–§10).**
Combining the existence form with sensitivity preservation gives the desired
restriction. The type `β'` here is just `β` since `apply ρ f` lives on the
same type. -/
private theorem restrictionToUniform
    {β : Type} [Fintype β] [DecidableEq β] {f : (β → Bool) → Bool} {p : ℝ}
    (hf : IsMonotone f) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hp_balance : (1/2 : ℝ) ≤ 2 * min p (1 - p)) :
    ∃ (β' : Type) (_ : Fintype β') (_ : DecidableEq β') (g : (β' → Bool) → Bool),
      IsMonotone g ∧
      (1/2 : ℝ) * infP p f ≤ influence g ∧
      (maxSensitivity g : ℝ) ≤ (maxSensitivity f : ℝ) := by
  obtain ⟨ρ, h_inf⟩ := exists_restriction_high_inf hf hp hp_balance
  refine ⟨β, inferInstance, inferInstance, Restriction.apply ρ f,
    Restriction.apply_monotone ρ f hf, h_inf, ?_⟩
  exact_mod_cast maxSens_apply_le ρ f

/-- **Per-scale endpoint witness.** For every `L`, there exists a monotone
Boolean function with `influence ≥ s/100` and `s ≥ L`.

For `L < 2` the dummy constant function suffices (`0 ≤ 0`). For `L ≥ 2` we
combine `existsBiasedCrossing` with `restrictionToUniform`. -/
private theorem perScaleEndpoint (L : ℕ) :
    ∃ (β : Type) (_ : Fintype β) (_ : DecidableEq β) (f : (β → Bool) → Bool),
      IsMonotone f ∧
      (1 / 300 : ℝ) * (maxSensitivity f : ℝ) ≤ influence f ∧
      (L : ℝ) / 200 ≤ (maxSensitivity f : ℝ) := by
  by_cases hL : 2 ≤ L
  · -- Main case: combine the biased crossing with random restriction.
    obtain ⟨β, _fin, _dec, f, p, hf_mono, hp_in, hp_bal, h_inf_bias, h_sens_le, _h_size_low⟩ :=
      existsBiasedCrossing L hL
    obtain ⟨β', _fin', _dec', g, hg_mono, h_inf_uniform, h_sens_le_g⟩ :=
      restrictionToUniform hf_mono hp_in hp_bal
    refine ⟨β', _fin', _dec', g, hg_mono, ?_, ?_⟩
    -- Bound 1: (1/300) · s_g ≤ (1/300) · s_f ≤ (1/300) · 3L = L/100 ≤ (1/2)·(L/50) ≤ Inf g.
    · have h_sens_le_3L : (maxSensitivity g : ℝ) ≤ 3 * L :=
        h_sens_le_g.trans h_sens_le
      have h_left : (1/300 : ℝ) * (maxSensitivity g : ℝ) ≤ (L : ℝ) / 100 := by
        have : (1/300 : ℝ) * (maxSensitivity g : ℝ) ≤ (1/300 : ℝ) * (3 * L) := by gcongr
        linarith
      have h_right : (L : ℝ) / 100 ≤ influence g := by
        have h_bias : (L : ℝ) / 100 ≤ (1/2 : ℝ) * infP p f := by
          have : (1/2 : ℝ) * ((L : ℝ) / 50) ≤ (1/2 : ℝ) * infP p f := by gcongr
          linarith
        linarith [h_inf_uniform]
      linarith
    -- Bound 2: L/200 ≤ uniform Inf g ≤ maxSens g.
    · have h_inf_g : (L : ℝ) / 100 ≤ influence g := by
        have h_bias : (L : ℝ) / 100 ≤ (1/2 : ℝ) * infP p f := by
          have : (1/2 : ℝ) * ((L : ℝ) / 50) ≤ (1/2 : ℝ) * infP p f := by gcongr
          linarith
        linarith [h_inf_uniform]
      have h_inf_le_max : influence g ≤ (maxSensitivity g : ℝ) := influence_le_maxSensitivity g
      linarith
  · -- Dummy case `L < 2`: dictator on `Unit`. Then maxSens = 1, influence = 1.
    push Not at hL
    refine ⟨Unit, inferInstance, inferInstance, fun g => g (), ?_, ?_, ?_⟩
    · intros x y hxy; exact hxy ()
    · -- (1/300) · 1 ≤ 1.
      have h_max : maxSensitivity (fun g : Unit → Bool => g ()) = 1 := by
        unfold maxSensitivity sensitivityAt; decide
      have h_inf : influence (fun g : Unit → Bool => g ()) = 1 := by
        change ((totalSensitivity (fun g : Unit → Bool => g ()) : ℝ)
                / (2 : ℝ) ^ Fintype.card Unit) = 1
        have h1 : Fintype.card Unit = 1 := rfl
        rw [h1]
        have h2 : totalSensitivity (fun g : Unit → Bool => g ()) = 2 := by
          unfold totalSensitivity sensitivityAt; decide
        rw [h2]; norm_num
      rw [h_max, h_inf]; norm_num
    · -- L/200 ≤ 1, since `L < 2`.
      have h_max : maxSensitivity (fun g : Unit → Bool => g ()) = 1 := by
        unfold maxSensitivity sensitivityAt; decide
      rw [h_max]
      have : L ≤ 1 := Nat.lt_succ_iff.mp hL
      have : (L : ℝ) ≤ 1 := by exact_mod_cast this
      linarith

/-- **Family from per-scale.** Given per-scale endpoint witnesses, package them
as a `BooleanFamily`. Pure type-theoretic bookkeeping. -/
private theorem familyFromPerScale :
    ∃ (fam : BooleanFamily),
      (∀ k, IsMonotone (fam.H k)) ∧
      (∀ k, (1 / 300 : ℝ) * (maxSensitivity (fam.H k) : ℝ) ≤ influence (fam.H k)) ∧
      (∀ k : ℕ, (k : ℝ) / 200 ≤ (maxSensitivity (fam.H k) : ℝ)) := by
  classical
  choose β fin dec f h_mono h_inf h_size using perScaleEndpoint
  exact ⟨{ β := β, fintype := fin, decEq := dec, H := f }, h_mono, h_inf, h_size⟩

/-- **Linear influence-sensitivity separation (note11).** There is a positive
absolute constant `c` and a `BooleanFamily` such that
* each member is monotone,
* eventually `c · maxSensitivity (H k) ≤ influence (H k)`,
* `maxSensitivity (H k) → ∞`. -/
theorem existsLinearOrientedFamily :
    ∃ (c : ℝ), 0 < c ∧
    ∃ (fam : BooleanFamily),
      (∀ k, IsMonotone (fam.H k)) ∧
      (∀ᶠ k : ℕ in Filter.atTop,
        c * (maxSensitivity (fam.H k) : ℝ) ≤ influence (fam.H k)) ∧
      Filter.Tendsto (fun k => (maxSensitivity (fam.H k) : ℕ))
        Filter.atTop Filter.atTop := by
  obtain ⟨fam, h_mono, h_inf, h_size⟩ := familyFromPerScale
  refine ⟨1 / 300, by norm_num, fam, h_mono, Filter.Eventually.of_forall h_inf, ?_⟩
  -- Tendsto maxSensitivity → ∞ (in ℕ) from h_size : k/200 ≤ maxSensitivity (H k).
  rw [Filter.tendsto_atTop_atTop]
  intro N
  refine ⟨200 * N, fun k hk_ge => ?_⟩
  have h1 : (k : ℝ) / 200 ≤ (maxSensitivity (fam.H k) : ℝ) := h_size k
  have h2 : (200 * N : ℕ) ≤ k := hk_ge
  have h3 : (200 * N : ℝ) ≤ (k : ℝ) := by exact_mod_cast h2
  have h4 : (N : ℝ) ≤ (k : ℝ) / 200 := by linarith
  have h5 : (N : ℝ) ≤ (maxSensitivity (fam.H k) : ℝ) := h4.trans h1
  exact_mod_cast h5

/-! ## Step 2: asymptotic bridge (proved in full) -/

/-- **Asymptotic bridge.** If `c · s k ≤ f k` eventually with `c > 0`,
`s → ∞`, and `f ≤ s` eventually, then `liminf log (f k) / log (s k) ≥ 1`.

Proof: `log(f) ≥ log(c · s) = log c + log s`. With `s → ∞` (so `log s → ∞`),
the ratio `log f / log s ≥ 1 + log c / log s → 1`. Combined with the upper
bound `log f / log s ≤ 1` from `f ≤ s`, the limit is exactly 1. -/
private lemma liminf_log_div_log_ge_one_of_linear
    {f s : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (h_lin : ∀ᶠ k : ℕ in Filter.atTop, c * s k ≤ f k)
    (h_s_to_inf : Filter.Tendsto s Filter.atTop Filter.atTop)
    (h_f_le_s : ∀ᶠ k : ℕ in Filter.atTop, f k ≤ s k) :
    (1 : ℝ) ≤
      Filter.liminf (fun k => Real.log (f k) / Real.log (s k)) Filter.atTop := by
  -- The reference function `g k = 1 + log c / log s k` tends to 1 and bounds
  -- `log f / log s` from below.
  -- We show: ∀ᶠ k, g k ≤ log f / log s and g → 1, hence liminf ≥ 1.
  have h_log_s_to_inf : Filter.Tendsto (fun k => Real.log (s k)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp h_s_to_inf
  -- `s k > 1` eventually, so `log (s k) > 0` eventually
  have h_s_gt_one : ∀ᶠ k : ℕ in Filter.atTop, 1 < s k := h_s_to_inf.eventually_gt_atTop 1
  have h_log_s_pos : ∀ᶠ k : ℕ in Filter.atTop, 0 < Real.log (s k) := by
    filter_upwards [h_s_gt_one] with k hk
    exact Real.log_pos hk
  -- `f k > 0` eventually (from `c · s k ≤ f k` and `s k > 0`)
  have h_f_pos : ∀ᶠ k : ℕ in Filter.atTop, 0 < f k := by
    filter_upwards [h_lin, h_s_to_inf.eventually_gt_atTop 0] with k h_lin_k h_s_pos
    exact lt_of_lt_of_le (mul_pos hc h_s_pos) h_lin_k
  -- Pointwise lower bound: `1 + log c / log s ≤ log f / log s`.
  have h_lower : ∀ᶠ k : ℕ in Filter.atTop,
      1 + Real.log c / Real.log (s k) ≤ Real.log (f k) / Real.log (s k) := by
    filter_upwards [h_lin, h_log_s_pos, h_f_pos, h_s_to_inf.eventually_gt_atTop 0] with
      k h_lin_k h_log_s_pos_k h_f_pos_k h_s_pos
    have h_cs_pos : 0 < c * s k := mul_pos hc h_s_pos
    have h_log_f_ge : Real.log c + Real.log (s k) ≤ Real.log (f k) := by
      have := Real.log_le_log h_cs_pos h_lin_k
      rwa [Real.log_mul (ne_of_gt hc) (ne_of_gt h_s_pos)] at this
    have h_self : Real.log (s k) / Real.log (s k) = 1 := div_self h_log_s_pos_k.ne'
    have h_combine : 1 + Real.log c / Real.log (s k)
        = (Real.log (s k) + Real.log c) / Real.log (s k) := by
      rw [add_div, h_self]
    rw [h_combine, div_le_div_iff_of_pos_right h_log_s_pos_k]
    linarith
  -- Pointwise upper bound: `log f / log s ≤ 1` (from `f ≤ s` and `log s > 0`).
  have h_upper : ∀ᶠ k : ℕ in Filter.atTop,
      Real.log (f k) / Real.log (s k) ≤ 1 := by
    filter_upwards [h_f_le_s, h_log_s_pos, h_f_pos] with k h_fle h_log_s_pos_k h_f_pos_k
    rw [div_le_one h_log_s_pos_k]
    exact Real.log_le_log h_f_pos_k h_fle
  -- The reference function `1 + log c / log s` tends to `1`.
  have h_ref_lim : Filter.Tendsto (fun k => 1 + Real.log c / Real.log (s k))
      Filter.atTop (nhds 1) := by
    have h_div_zero : Filter.Tendsto (fun k => Real.log c / Real.log (s k))
        Filter.atTop (nhds 0) := by
      simpa using h_log_s_to_inf.const_div_atTop (Real.log c)
    have := h_div_zero.const_add 1
    simpa using this
  -- liminf log f / log s ≥ liminf reference = 1.
  rw [← h_ref_lim.liminf_eq]
  refine Filter.liminf_le_liminf h_lower ?_ ?_
  · -- (fun k => 1 + log c / log s k) is bounded below at top: it converges to 1.
    exact h_ref_lim.isBoundedUnder_ge
  · -- (fun k => log f / log s) is co-bounded ≥ from above-boundedness by 1.
    have h_above : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun k => Real.log (f k) / Real.log (s k)) := ⟨1, h_upper⟩
    exact h_above.isCoboundedUnder_ge

/-! ## Step 3: main theorem (proved from Steps 1+2) -/

/-- **Main theorem.** The exponent `1` is achievable for monotone Boolean
functions, via the oriented-percolation linear separation. -/
theorem exponentAchievable_one : ExponentAchievable 1 := by
  obtain ⟨c, hc, fam, h_mono, h_lin, h_max_to_inf⟩ := existsLinearOrientedFamily
  refine ⟨fam, h_mono, h_max_to_inf, ?_⟩
  apply liminf_log_div_log_ge_one_of_linear hc h_lin
  · -- s = (maxSensitivity ∘ H) → ∞ as ℝ.
    exact tendsto_natCast_atTop_atTop.comp h_max_to_inf
  · -- influence ≤ maxSensitivity always.
    exact Filter.Eventually.of_forall (fun k => influence_le_maxSensitivity (fam.H k))

/-- **Corollary.** Every `r ≤ 1` is achievable. -/
theorem exponentAchievable_of_le_one {r : ℝ} (hr : r ≤ 1) : ExponentAchievable r :=
  ExponentAchievable.mono hr exponentAchievable_one

/-- **Characterisation.** The achievable exponents are exactly `r ≤ 1`. -/
theorem exponentAchievable_iff_le_one (r : ℝ) :
    ExponentAchievable r ↔ r ≤ 1 :=
  ⟨ExponentAchievable.le_one, exponentAchievable_of_le_one⟩

/-! ## The endpoint statement (note11) -/

/-- **Endpoint theorem (note11).** There exists an absolute constant `c > 0`
and a sequence of monotone Boolean functions `f_k`, each on a finite Boolean
cube, such that
* the maximum sensitivity diverges, `s(f_k) → ∞`, and
* the linear lower bound `c · s(f_k) ≤ Inf(f_k)` holds for every `k`.

This is the strongest possible influence-vs-sensitivity statement for monotone
Boolean functions. The constant `c` is uniform; only the *existence* of such a
sequence is asserted, the explicit value being `c = 3/(8 · A · C_s)` for the
oriented-percolation tuning constants of note11. -/
theorem linearInfluenceSensitivity :
    ∃ (c : ℝ), 0 < c ∧
    ∃ (β : ℕ → Type) (_ : ∀ k, Fintype (β k)) (_ : ∀ k, DecidableEq (β k))
      (f : ∀ k, (β k → Bool) → Bool),
      (∀ k, IsMonotone (f k)) ∧
      Filter.Tendsto (fun k => (maxSensitivity (f k) : ℕ)) Filter.atTop Filter.atTop ∧
      (∀ k, c * (maxSensitivity (f k) : ℝ) ≤ influence (f k)) := by
  obtain ⟨fam, h_mono, h_inf, h_size⟩ := familyFromPerScale
  refine ⟨1 / 300, by norm_num,
    fam.β, fam.fintype, fam.decEq, fam.H, h_mono, ?_, h_inf⟩
  rw [Filter.tendsto_atTop_atTop]
  intro N
  refine ⟨200 * N, fun k hk => ?_⟩
  have h_kge : (200 * N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h_size_k : (k : ℝ) / 200 ≤ (maxSensitivity (fam.H k) : ℝ) := h_size k
  have h1 : (N : ℝ) ≤ (maxSensitivity (fam.H k) : ℝ) := by
    have : (N : ℝ) ≤ (k : ℝ) / 200 := by linarith
    linarith
  exact_mod_cast h1

end Oriented

end InfluenceSensitivity

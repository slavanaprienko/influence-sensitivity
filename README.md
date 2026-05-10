# Influence-Sensitivity Tradeoff for Monotone Boolean Functions

Lean 4 formalization of a new best construction for the monotone influence-sensitivity tradeoff, improving the bound of O'Donnell–Servedio (2007).

## Result

We construct a family of monotone Boolean functions `H_k : (β k → Bool) → Bool` such that

```
liminf_{k → ∞}  log Inf(H_k) / log maxSensitivity(H_k)  ≥  2/3
```

where `influence f` is the total influence under the uniform measure on `{0,1}^n` and `maxSensitivity f` is the worst-case sensitivity. The previous best monotone construction, due to O'Donnell–Servedio (2007), achieved exponent ≈ 0.6115. The problem of determining the optimal exponent is listed as open in Filmus, Hatami, Heilman, Mossel, O'Donnell, Sachdeva, Wan, and Wimmer's *Real Analysis in Computer Science: A Collection of Open Problems* (2014), under the heading *Average versus Max Sensitivity for Monotone Functions*, in connection with the Servedio–Tan conjecture (also stated explicitly by Scheder and Tan, 2013).

The main theorem is `twoThirdsExponentAchievable_unconditional` in `InfluenceSensitivity/TwoThirds.lean`. The proof uses no `sorry` and no custom axioms — only Lean's standard `propext`, `Classical.choice`, `Quot.sound`.

The accompanying paper sharpens the construction to a strictly larger explicit exponent `2/3 + η` with `η > 8·10⁻⁴`, via a Poisson-tuned *biased cascade* whose recursion is confined to a fixed sub-interval `[p_-, Λ] = [0.127, 0.2]` bounded away from `0` and `1`. The qualitative `2/3` statement is what is formalized here; the explicit `η` calculation lives in the paper's appendix.

## Approach

The Lean formalization proves the qualitative `2/3` exponent in two files:

- **`InfluenceSensitivity/Basic.lean`** — Boolean-cube infrastructure. Definitions and properties of `sensitivityAt`, `maxSensitivity`, `maxSensitivityOne`, `maxSensitivityZero`, `dual`, `IsMonotone`, `compose`, `compBlock`, `biasedMeasure`, `biasedProb`, `biasedExpectation`, `outputBias`, `infP`, `influence`. Key results: monotone duality identities (`maxSensitivityOne_dual`, `maxSensitivityZero_dual`), composition bounds (`maxSensitivityOne_compose`, `maxSensitivityZero_compose`), the influence-composition identity, and the `composedBlock T B := compose T (dual B)` packaging with `composedBlock_bounds`. The abstract framework lives here: `BooleanFamily`, `ExponentAchievable`, `TwoThirdsExponentAchievable`, and `ExponentAchievable.le_one` (the universal upper bound).

- **`InfluenceSensitivity/TwoThirds.lean`** — the construction. Polynomial-graph DNFs over `ZMod Q × ZMod Q` (where `Q` ranges over primes), their first- and second-moment estimates, the two-gadget pair `TwoGadgetPair`, and the scale-indexed `H_Q` sequence assembled via `composedBlock`. Contains the main theorem `twoThirdsExponentAchievable_unconditional` and the wrapper `achievability_summary`.

The construction proceeds in three layers:

1. **Polynomial-graph DNFs** (`polyGraph`, `polyGraphFamily` in `TwoThirds.lean`; the block itself is `monotoneDNF (polyGraphFamily E d)` using `monotoneDNF` from `Basic.lean`). Over a finite field `F = ZMod Q` with `Q` prime, build a monotone DNF whose terms are the graphs `{(t, P(t)) : t ∈ E}` of polynomials `P` of degree `< d` in `F × F`. First- and second-moment estimates on the number of satisfied graphs (`polyGraphFamily_first_moment_sum`, `polyGraphFamily_second_moment_sharp_le`) give a Paley–Zygmund lower bound `infP_polyGraphDNF_ge_sharp` on the `p`-biased influence, while the affine-cover argument bounds `maxSensitivityZero_polyGraphDNF_le` and the term-size bound gives `maxSensitivityOne_polyGraphDNF_le`. Existence of these blocks across a uniform interval of biases is packaged as `gadget_exists_for_all_biases`.

2. **Two-gadget composition** (`TwoGadgetPair`, `twoGadgetExistsForPrimes_proof`). For each prime `Q`, two polynomial-graph gadgets `B` (tuned at `p = 1/2`) and `T` (tuned at `p = 1 − outputBias B`, lying in `[2/3, 1 − c_B]`) are combined as `composedBlock T B = compose T (dual B)`. The influence-composition identity gives `Inf(composedBlock T B) ≥ c_T · c_B · Q²` and the sensitivity-composition bounds give `maxSensitivity(composedBlock T B) ≤ Q³`. Both are packaged by `composedBlock_bounds` in `Basic.lean` and instantiated by `TwoGadgetPair.composed_bounds`.

3. **Scale-indexed limit** (`HQSequence`, `hQSequenceExists_proof`, `twoThirdsExponentAchievable_of_scale_bounds`). Indexing by an unbounded sequence of primes `Q_k → ∞`, the bounds `c · Q_k² ≤ Inf(H_k)` and `maxSensitivity(H_k) ≤ C · Q_k³` are fed into the analytic core `liminf_log_div_log_ge_of_scale_bounds`, yielding `liminf log Inf / log maxSensitivity ≥ 2/3`. The main theorem `twoThirdsExponentAchievable_unconditional` instantiates the abstract `TwoThirdsExponentAchievable` predicate.

The paper's stronger `2/3 + η` result (η > 8·10⁻⁴) replaces step 2 with a *biased cascade* that retunes the outer block at each level to the actual output bias of the previous level and forces the recursion to live on a fixed interval `[p_-, Λ]` with `Λ = 1/5`, `r_0 = 4/5`, exploiting the smaller affine-cover constant `log(5/4)` available in the high-internal-bias regime. The Lean port of the cascade refinement is not yet included in this repository.

## Building

Requires Lean 4 (toolchain pinned in `lean-toolchain`) and Mathlib. To verify:

```
lake build
```

To inspect axiom usage of the main result:

```
#print axioms InfluenceSensitivity.twoThirdsExponentAchievable_unconditional
```

The output should list only `propext`, `Classical.choice`, and `Quot.sound`.

## References

- Filmus, Yuval, Hamed Hatami, Steven Heilman, Elchanan Mossel, Ryan O'Donnell, Sushant Sachdeva, Andrew Wan, and Karl Wimmer. "Real analysis in computer science: A collection of open problems." Preprint available at https://simons.berkeley.edu/sites/default/files/openprobsmerged.pdf (2014).
- O'Donnell, Ryan, and Rocco A. Servedio. "Learning monotone decision trees in polynomial time." *SIAM Journal on Computing* 37, no. 3 (2007): 827–844.
- Scheder, Dominik, and Li-Yang Tan. "On the average sensitivity and density of k-CNF formulas." In *Approximation, Randomization, and Combinatorial Optimization (APPROX/RANDOM 2013)*, Lecture Notes in Computer Science, vol. 8096, Springer, Berlin, Heidelberg, 2013, pp. 683–698.

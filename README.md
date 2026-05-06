# Influence-Sensitivity Tradeoff for Monotone Boolean Functions

Lean 4 formalization of a new best construction for the monotone influence-sensitivity tradeoff, improving the bound of O'Donnell–Servedio (2007).

## Result

We construct a family of monotone Boolean functions `H_k : {0,1}^{n_k} → {0,1}` such that

```
liminf_{k → ∞}  log Inf(H_k) / log s(H_k)  ≥  2/3
```

where `Inf(f)` is the total influence under the uniform measure and `s(f)` is the maximum sensitivity. The previous best monotone construction, due to O'Donnell–Servedio (2007), achieved exponent ≈ 0.6115. The problem of determining the optimal exponent is listed as open in Filmus, Hatami, Heilman, Mossel, O'Donnell, Sachdeva, Wan, and Wimmer's *Real Analysis in Computer Science: A Collection of Open Problems* (2014), in connection with the Servedio–Tan conjecture.

The main theorem is `twoThirdsExponentAchievable_unconditional` in `InfluenceSensitivity/Basic.lean`. The proof uses no `sorry` and no custom axioms — only Lean's standard `propext`, `Classical.choice`, `Quot.sound`.

The construction can be sharpened to achieve a strictly larger exponent `2/3 + η` for some small but fixed `η > 0`; that strengthening will be added to this repository in a future update.

## Approach

The construction proceeds in three layers:

1. **Polynomial-graph DNFs.** Over a finite field `F = ZMod Q` (Q prime), build a monotone DNF whose terms are the graphs of low-degree polynomials in `F × F`. Sharp first- and second-moment bounds on subset-satisfaction probability give a Paley–Zygmund lower bound on the `p`-biased influence.

2. **Two-gadget composition.** Compose a top gadget `T` with the dual of a bottom gadget `B`, both polynomial-graph DNFs over `ZMod Q × ZMod Q` with biases tuned so that `outputBias(B) = 1 − outputBias(B^*)` matches the `p`-biased influence parameter required by `T`. The composed block satisfies `Inf ≥ c·Q²` and `s ≤ Q³`.

3. **Scale-indexed limit.** Indexing by an unbounded sequence of primes `Q_k → ∞`, the polynomial scale bounds yield `log Inf / log s → 2/3` via the analytic core `liminf_log_div_log_ge_of_scale_bounds`.

## Building

Requires Lean 4 (toolchain pinned in `lean-toolchain`) and Mathlib. To verify:

```
lake build
```

The full proof is in a single file: `InfluenceSensitivity/Basic.lean`.

## References

- Filmus, Yuval, Hamed Hatami, Steven Heilman, Elchanan Mossel, Ryan O'Donnell, Sushant Sachdeva, Andrew Wan, and Karl Wimmer. "Real analysis in computer science: A collection of open problems." Preprint available at https://simons.berkeley.edu/sites/default/files/openprobsmerged.pdf (2014).
- O'Donnell, Ryan, and Rocco A. Servedio. "Learning monotone decision trees in polynomial time." *SIAM Journal on Computing* 37, no. 3 (2007): 827–844.

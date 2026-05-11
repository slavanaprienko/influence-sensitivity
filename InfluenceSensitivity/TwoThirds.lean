import InfluenceSensitivity.Basic

set_option linter.style.nativeDecide false
set_option linter.style.whitespace false

/-!
# The 2/3 exponent: polynomial-graph gadget construction

This file contains the machinery specific to proving
`twoThirdsExponentAchievable_unconditional` via the polynomial-graph DNF gadget
of note2.md. All general-purpose Boolean-cube/sensitivity/composition theory
lives in `InfluenceSensitivity.Basic`.
-/

namespace InfluenceSensitivity

/-- **Polynomial root count in a Finset.** For a non-zero polynomial `P` over a field
`F`, the count of its roots in any Finset `E ⊆ F` is bounded by `P.natDegree`. -/
lemma card_roots_in_finset_le {F : Type*} [Field F] [DecidableEq F]
    {P : Polynomial F} (hP : P ≠ 0) (E : Finset F) :
    (E.filter (fun t => P.eval t = 0)).card ≤ P.natDegree := by
  refine le_trans ?_ (le_trans (Multiset.toFinset_card_le P.roots) P.card_roots')
  apply Finset.card_le_card
  intros t ht
  rw [Finset.mem_filter] at ht
  obtain ⟨_, h_eval⟩ := ht
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
  exact h_eval

/-- **Polynomial-graph (Finset).** The "graph" of a polynomial `P` over a Finset `E`,
as a subset of `F × F`. Each element is `(t, P.eval t)` for `t ∈ E`. -/
def polyGraph {F : Type*} [DecidableEq F] [CommSemiring F]
    (E : Finset F) (P : Polynomial F) : Finset (F × F) :=
  E.image (fun t => (t, P.eval t))

/-- **`polyGraph` size equals `|E|`** (the projection to first coord is injective). -/
lemma polyGraph_card {F : Type*} [DecidableEq F] [CommSemiring F]
    (E : Finset F) (P : Polynomial F) :
    (polyGraph E P).card = E.card := by
  unfold polyGraph
  apply Finset.card_image_of_injective
  intros t1 t2 h
  exact (Prod.mk.inj h).1

/-- **Intersection of two polynomial graphs.** For distinct polynomials `P, R`,
the intersection `polyGraph E P ∩ polyGraph E R` has size ≤ `(P - R).natDegree`. -/
lemma polyGraph_inter_card_le {F : Type*} [Field F] [DecidableEq F]
    (E : Finset F) {P R : Polynomial F} (hPR : P ≠ R) :
    (polyGraph E P ∩ polyGraph E R).card ≤ (P - R).natDegree := by
  refine le_trans ?_ (card_roots_in_finset_le (sub_ne_zero.mpr hPR) E)
  -- polyGraph E P ∩ polyGraph E R ↪ E.filter ((P - R).eval = 0) via projection on first coord.
  apply Finset.card_le_card_of_injOn (fun (p : F × F) => p.1)
  · -- p ∈ inter ⟹ p.1 ∈ E.filter ((P - R).eval = 0)
    intros p hp_coe
    have hp : p ∈ polyGraph E P ∩ polyGraph E R := hp_coe
    obtain ⟨hpP, hpR⟩ := Finset.mem_inter.mp hp
    obtain ⟨t1, ht1_mem, ht1_eq⟩ := Finset.mem_image.mp hpP
    obtain ⟨t2, _, ht2_eq⟩ := Finset.mem_image.mp hpR
    have ht_eq : t1 = t2 := (Prod.mk.inj (ht1_eq.trans ht2_eq.symm)).1
    have hp1_eq : p.1 = t1 := ((Prod.mk.inj ht1_eq).1).symm
    have hP_eval : P.eval t1 = p.2 := (Prod.mk.inj ht1_eq).2
    have hR_eval : R.eval t2 = p.2 := (Prod.mk.inj ht2_eq).2
    change p.1 ∈ E.filter (fun t => (P - R).eval t = 0)
    rw [Finset.mem_filter]
    refine ⟨hp1_eq ▸ ht1_mem, ?_⟩
    rw [Polynomial.eval_sub, hp1_eq, hP_eval]
    rw [show R.eval t1 = p.2 from by rw [ht_eq]; exact hR_eval]
    ring
  · -- Injectivity: distinct points in the intersection have distinct first coords
    intros p hp q hq hpq
    obtain ⟨hpP, _⟩ := Finset.mem_inter.mp hp
    obtain ⟨hqP, _⟩ := Finset.mem_inter.mp hq
    obtain ⟨tp, _, htp_eq⟩ := Finset.mem_image.mp hpP
    obtain ⟨tq, _, htq_eq⟩ := Finset.mem_image.mp hqP
    have htp_tq : tp = tq := by
      rw [(Prod.mk.inj htp_eq).1, (Prod.mk.inj htq_eq).1]; exact hpq
    rw [← htp_eq, ← htq_eq, htp_tq]

/-- **Polynomial from coefficient sequence.** -/
noncomputable def polyOfCoeffs {F : Type*} [Semiring F] {d : ℕ} (c : Fin d → F) :
    Polynomial F :=
  ∑ i : Fin d, Polynomial.monomial (i : ℕ) (c i)

/-- **Polynomial coefficient via `polyOfCoeffs`.** For `i : Fin d`,
`(polyOfCoeffs c).coeff i.val = c i`. -/
lemma polyOfCoeffs_coeff {F : Type*} [Semiring F] {d : ℕ}
    (c : Fin d → F) (i : Fin d) :
    (polyOfCoeffs c).coeff i.val = c i := by
  unfold polyOfCoeffs
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intros j _ hji
    rw [Polynomial.coeff_monomial]
    rw [if_neg (fun h => hji (Fin.ext h))]
  · intros h_not_mem
    exact absurd (Finset.mem_univ i) h_not_mem

/-- **`polyOfCoeffs` is injective.** -/
lemma polyOfCoeffs_injective {F : Type*} [Semiring F] {d : ℕ} :
    Function.Injective (polyOfCoeffs : (Fin d → F) → Polynomial F) := by
  intros c c' h
  funext i
  have h_coeff := congrArg (fun P : Polynomial F => P.coeff i.val) h
  simp at h_coeff
  rw [polyOfCoeffs_coeff, polyOfCoeffs_coeff] at h_coeff
  exact h_coeff

/-- **`polyOfCoeffs` natDegree bound.** For `d > 0`, `(polyOfCoeffs c).natDegree < d`. -/
lemma polyOfCoeffs_natDegree_lt {F : Type*} [Semiring F] {d : ℕ} (hd : 0 < d)
    (c : Fin d → F) : (polyOfCoeffs c).natDegree < d := by
  unfold polyOfCoeffs
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
  rw [Finset.fold_max_lt]
  refine ⟨hd, ?_⟩
  intros i _
  exact lt_of_le_of_lt (Polynomial.natDegree_monomial_le _) i.isLt

/-- **Linearity (sub) of `polyOfCoeffs`.** -/
lemma polyOfCoeffs_sub {F : Type*} [Ring F] {d : ℕ} (c c' : Fin d → F) :
    polyOfCoeffs c - polyOfCoeffs c' = polyOfCoeffs (c - c') := by
  unfold polyOfCoeffs
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intros i _
  rw [← Polynomial.monomial_sub]
  rfl

/-- **Polynomial graph intersection bound for coefficient sequences.**
For distinct `c ≠ c' : Fin d → F` (with `d > 0`), the polynomial graphs
intersect in at most `d - 1` points. -/
lemma polyGraph_inter_card_lt_of_coeffs {F : Type*} [Field F] [DecidableEq F] {d : ℕ}
    (hd : 0 < d) (E : Finset F) {c c' : Fin d → F} (hcc' : c ≠ c') :
    (polyGraph E (polyOfCoeffs c) ∩ polyGraph E (polyOfCoeffs c')).card < d := by
  have h_poly_ne : polyOfCoeffs c ≠ polyOfCoeffs c' :=
    fun h => hcc' (polyOfCoeffs_injective h)
  refine lt_of_le_of_lt (polyGraph_inter_card_le E h_poly_ne) ?_
  rw [polyOfCoeffs_sub]
  exact polyOfCoeffs_natDegree_lt hd _

/-- **Family of polynomial graphs.** All polynomial graphs over `E` for polynomials
of degree < `d`, indexed by coefficient sequences. -/
noncomputable def polyGraphFamily {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (E : Finset F) (d : ℕ) : Finset (Finset (F × F)) :=
  (Finset.univ : Finset (Fin d → F)).image (fun c => polyGraph E (polyOfCoeffs c))

/-- **Every term in the family has size `|E|`.** -/
lemma polyGraphFamily_term_card {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (E : Finset F) (d : ℕ) (S : Finset (F × F)) (hS : S ∈ polyGraphFamily E d) :
    S.card = E.card := by
  unfold polyGraphFamily at hS
  rw [Finset.mem_image] at hS
  obtain ⟨c, _, hc_eq⟩ := hS
  rw [← hc_eq]
  exact polyGraph_card E _

/-- **Family cardinality.** When `|E| ≥ d > 0`, the family has size `|F|^d`. -/
lemma polyGraphFamily_card {F : Type*} [Field F] [DecidableEq F] [Fintype F] {d : ℕ}
    (hd : 0 < d) {E : Finset F} (hE : d ≤ E.card) :
    (polyGraphFamily E d).card = (Fintype.card F) ^ d := by
  unfold polyGraphFamily
  rw [Finset.card_image_of_injOn, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  intros c _ c' _ h_eq
  simp only at h_eq
  by_contra h_ne
  have h_inter := polyGraph_inter_card_lt_of_coeffs hd E h_ne
  have h_inter_eq : polyGraph E (polyOfCoeffs c) ∩ polyGraph E (polyOfCoeffs c') =
                    polyGraph E (polyOfCoeffs c) := by
    rw [h_eq, Finset.inter_self]
  rw [h_inter_eq, polyGraph_card] at h_inter
  omega

/-- **`polyOfCoeffs c = 0 ↔ c = 0`.** -/
lemma polyOfCoeffs_eq_zero_iff {F : Type*} [Semiring F] {d : ℕ} (c : Fin d → F) :
    polyOfCoeffs c = 0 ↔ c = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · funext i
    have := polyOfCoeffs_coeff c i
    rw [h] at this
    simp at this
    change c i = (0 : Fin d → F) i
    rw [Pi.zero_apply, ← this]
  · subst h
    unfold polyOfCoeffs
    simp

/-- **Polynomial of `polyOfCoeffs c` is zero when `T` has too many roots.**
If `d ≤ |T|` and all of `T` are roots of `polyOfCoeffs c`, then `polyOfCoeffs c = 0`. -/
lemma polyOfCoeffs_eq_zero_of_T_subset_roots {F : Type*} [Field F] [DecidableEq F]
    {d : ℕ} (c : Fin d → F) (T : Finset F) (h_card : d ≤ T.card)
    (h_root : ∀ t ∈ T, (polyOfCoeffs c).eval t = 0) :
    polyOfCoeffs c = 0 := by
  by_contra h_ne
  by_cases hd : 0 < d
  · have h_natDeg_lt : (polyOfCoeffs c).natDegree < T.card :=
      (polyOfCoeffs_natDegree_lt hd c).trans_le h_card
    have h_roots_eq := Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
      (fun t ht => h_root t ht) h_natDeg_lt.le h_ne
    have h_card_roots : (polyOfCoeffs c).roots.card = T.card := by
      rw [h_roots_eq]
      rfl
    have h_card_le := (polyOfCoeffs c).card_roots'
    rw [h_card_roots] at h_card_le
    omega
  · push Not at hd
    have hd_eq : d = 0 := by omega
    subst hd_eq
    apply h_ne
    unfold polyOfCoeffs
    simp

/-- **Lagrange uniqueness for `polyOfCoeffs`.** Two coefficient sequences agreeing
on `d` distinct evaluation points are equal. -/
lemma polyOfCoeffs_eq_of_eval_eq_on_card_d
    {F : Type*} [Field F] [DecidableEq F]
    {d : ℕ} (c c' : Fin d → F) (S : Finset F) (hS_card : d ≤ S.card)
    (h_eq : ∀ t ∈ S, (polyOfCoeffs c).eval t = (polyOfCoeffs c').eval t) :
    c = c' := by
  have h_diff_eval : ∀ t ∈ S, (polyOfCoeffs (c - c')).eval t = 0 := by
    intros t ht
    rw [← polyOfCoeffs_sub, Polynomial.eval_sub]
    rw [h_eq t ht]; ring
  have h_diff_zero : polyOfCoeffs (c - c') = 0 :=
    polyOfCoeffs_eq_zero_of_T_subset_roots (c - c') S hS_card h_diff_eval
  have h_cc' : c - c' = 0 := (polyOfCoeffs_eq_zero_iff (c - c')).mp h_diff_zero
  funext i
  have := congrFun h_cc' i
  simp only [Pi.sub_apply, Pi.zero_apply] at this
  linear_combination this

/-- **Existence of an `F`-extension** of size `d`. -/
lemma exists_extension_to_size_d {F : Type*} [Fintype F] [DecidableEq F]
    {d : ℕ} (T : Finset F) (hTd : T.card ≤ d) (hdF : d ≤ Fintype.card F) :
    ∃ S : Finset F, T ⊆ S ∧ S.card = d := by
  obtain ⟨S, hT_sub, _hS_sub, hS_card⟩ := Finset.exists_subsuperset_card_eq
    (T.subset_univ) hTd (by rw [Finset.card_univ]; exact hdF)
  exact ⟨S, hT_sub, hS_card⟩

/-- **Polynomial counting (general `T`, `|T| ≤ d ≤ |F|`).**
For `T : Finset F`, the count of coefficient sequences with `T ⊆ roots` is
bounded by `|F|^(d - |T|)`. -/
lemma card_polyOfCoeffs_with_roots_le_general
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d : ℕ} (T : Finset F) (hTd : T.card ≤ d) (hdF : d ≤ Fintype.card F) :
    ((Finset.univ : Finset (Fin d → F)).filter
      (fun c => ∀ t ∈ T, (polyOfCoeffs c).eval t = 0)).card ≤
    (Fintype.card F) ^ (d - T.card) := by
  obtain ⟨S, hT_sub, hS_card⟩ := exists_extension_to_size_d T hTd hdF
  set f : (Fin d → F) → (↥(S \ T) → F) :=
    fun c s => (polyOfCoeffs c).eval s.val with hf_def
  set Filter := (Finset.univ : Finset (Fin d → F)).filter
    (fun c => ∀ t ∈ T, (polyOfCoeffs c).eval t = 0) with hFilter_def
  have h_inj : Set.InjOn f Filter := by
    intros c hc c' hc' h_eq
    apply polyOfCoeffs_eq_of_eval_eq_on_card_d c c' S (le_of_eq hS_card.symm)
    intros t ht
    by_cases h_in_T : t ∈ T
    · have hc_mem : c ∈ Filter := hc
      have hc'_mem : c' ∈ Filter := hc'
      rw [hFilter_def, Finset.mem_filter] at hc_mem hc'_mem
      rw [hc_mem.2 t h_in_T, hc'_mem.2 t h_in_T]
    · have ht_in : t ∈ S \ T := Finset.mem_sdiff.mpr ⟨ht, h_in_T⟩
      exact congrFun h_eq ⟨t, ht_in⟩
  have h_card_le : Filter.card ≤ (Finset.univ : Finset (↥(S \ T) → F)).card := by
    refine Finset.card_le_card_of_injOn f ?_ h_inj
    intros c _; exact Finset.mem_univ _
  have h_target_card :
      (Finset.univ : Finset (↥(S \ T) → F)).card = (Fintype.card F) ^ (d - T.card) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe]
    have h_diff_card : (S \ T).card = d - T.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hT_sub, hS_card]
    rw [h_diff_card]
  rw [h_target_card] at h_card_le
  exact h_card_le

/-- **Polynomial graph intersection equals the eval-agreement set.** -/
lemma polyGraph_inter_eq {F : Type*} [DecidableEq F] [CommSemiring F]
    (E : Finset F) (P R : Polynomial F) :
    polyGraph E P ∩ polyGraph E R =
    (E.filter (fun t => P.eval t = R.eval t)).image (fun t => (t, P.eval t)) := by
  ext p
  simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter, polyGraph]
  constructor
  · rintro ⟨⟨tP, htP_E, htP_eq⟩, ⟨tR, htR_E, htR_eq⟩⟩
    refine ⟨tP, ⟨htP_E, ?_⟩, htP_eq⟩
    have h1 : tP = p.1 := (Prod.mk.inj htP_eq).1
    have h2 : tR = p.1 := (Prod.mk.inj htR_eq).1
    have h3 : tP = tR := h1.trans h2.symm
    have h4 : P.eval tP = p.2 := (Prod.mk.inj htP_eq).2
    have h5 : R.eval tR = p.2 := (Prod.mk.inj htR_eq).2
    rw [h3, h5, ← h4, h3]
  · rintro ⟨t, ⟨ht_E, ht_eq⟩, ht_pair⟩
    refine ⟨⟨t, ht_E, ht_pair⟩, ⟨t, ht_E, ?_⟩⟩
    rw [← ht_eq, ht_pair]

/-- **Polynomial graph intersection size equals number of agreement points.** -/
lemma polyGraph_inter_card {F : Type*} [DecidableEq F] [CommSemiring F]
    (E : Finset F) (P R : Polynomial F) :
    (polyGraph E P ∩ polyGraph E R).card =
    (E.filter (fun t => P.eval t = R.eval t)).card := by
  rw [polyGraph_inter_eq]
  apply Finset.card_image_of_injective
  intros t1 t2 h
  exact (Prod.mk.inj h).1

/-- **Binomial powerset identity**: `(1+θ)^|s| = ∑ T ⊆ s, θ^|T|`. -/
lemma one_plus_pow_eq_sum_powerset {α : Type*} (s : Finset α) (θ : ℝ) :
    (1 + θ) ^ s.card = ∑ T ∈ s.powerset, θ ^ T.card := by
  have h := Finset.sum_pow_mul_eq_add_pow θ (1 : ℝ) s
  simp only [one_pow, mul_one] at h
  rw [add_comm 1 θ, ← h]

/-- **Sub-powerset characterization**: `T ⊆ E.filter (...) ↔ T ⊆ E ∧ predicate on T`. -/
lemma subset_filter_iff {α : Type*} {E : Finset α} {p : α → Prop} [DecidablePred p]
    {T : Finset α} :
    T ⊆ E.filter p ↔ T ⊆ E ∧ ∀ t ∈ T, p t := by
  constructor
  · intros h
    refine ⟨fun t ht => (Finset.mem_filter.mp (h ht)).1, fun t ht =>
      (Finset.mem_filter.mp (h ht)).2⟩
  · rintro ⟨hTE, hT⟩ t ht
    exact Finset.mem_filter.mpr ⟨hTE ht, hT t ht⟩

/-- **Sum identity (swap)**: For each `c`, `∑_{T ⊆ E∩roots(P_c)} θ^|T| =
∑_{T ⊆ E} (if all of T are roots then θ^|T| else 0)`. -/
lemma sum_powerset_filter_eq_sum_with_indicator {F : Type*} [DecidableEq F] [CommSemiring F]
    {d : ℕ} (E : Finset F) (c : Fin d → F) (θ : ℝ) :
    (∑ T ∈ (E.filter (fun t => (polyOfCoeffs c).eval t = 0)).powerset, θ ^ T.card) =
    ∑ T ∈ E.powerset, (if ∀ t ∈ T, (polyOfCoeffs c).eval t = 0 then θ ^ T.card else 0) := by
  rw [show ((E.filter (fun t => (polyOfCoeffs c).eval t = 0)).powerset) =
        E.powerset.filter (fun T => ∀ t ∈ T, (polyOfCoeffs c).eval t = 0) from ?_]
  · rw [Finset.sum_filter]
  · ext T
    simp only [Finset.mem_powerset, Finset.mem_filter]
    rw [subset_filter_iff]

/-- **Injectivity of the polynomial-graph parametrization.** When `|E| ≥ d > 0`,
distinct coefficient sequences yield distinct polynomial graphs. -/
lemma polyGraph_polyOfCoeffs_injOn {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d : ℕ} (hd : 0 < d) {E : Finset F} (hE : d ≤ E.card) :
    ∀ c ∈ (Finset.univ : Finset (Fin d → F)),
    ∀ c' ∈ (Finset.univ : Finset (Fin d → F)),
      polyGraph E (polyOfCoeffs c) = polyGraph E (polyOfCoeffs c') → c = c' := by
  intros c _ c' _ h_eq
  by_contra h_ne
  have h_inter := polyGraph_inter_card_lt_of_coeffs hd E h_ne
  have h_inter_eq : polyGraph E (polyOfCoeffs c) ∩ polyGraph E (polyOfCoeffs c') =
                    polyGraph E (polyOfCoeffs c) := by
    rw [h_eq, Finset.inter_self]
  rw [h_inter_eq, polyGraph_card] at h_inter
  omega

/-- **Single-sum reformulation**: a sum over `polyGraphFamily E d` equals the corresponding
sum over coefficient sequences `c : Fin d → F`. -/
lemma polyGraphFamily_sum_eq {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d : ℕ} (hd : 0 < d) {E : Finset F} (hE : d ≤ E.card)
    (g : Finset (F × F) → ℝ) :
    (∑ S ∈ polyGraphFamily E d, g S) =
    ∑ c : Fin d → F, g (polyGraph E (polyOfCoeffs c)) := by
  unfold polyGraphFamily
  exact Finset.sum_image (polyGraph_polyOfCoeffs_injOn hd hE)

/-- **Double-sum reformulation**: a double sum over `polyGraphFamily E d` equals the
corresponding double sum over coefficient pairs `(c, c') : (Fin d → F) × (Fin d → F)`. -/
lemma polyGraphFamily_double_sum_eq {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d : ℕ} (hd : 0 < d) {E : Finset F} (hE : d ≤ E.card)
    (g : Finset (F × F) → Finset (F × F) → ℝ) :
    (∑ S ∈ polyGraphFamily E d, ∑ S' ∈ polyGraphFamily E d, g S S') =
    ∑ c : Fin d → F, ∑ c' : Fin d → F,
      g (polyGraph E (polyOfCoeffs c)) (polyGraph E (polyOfCoeffs c')) := by
  rw [polyGraphFamily_sum_eq hd hE]
  apply Finset.sum_congr rfl
  intros c _
  rw [polyGraphFamily_sum_eq hd hE]

/-- **Polynomial graph union/intersection cardinality identity**:
`|polyGraph E P ∪ polyGraph E R| + |E.filter (P = R)| = 2|E|`. -/
lemma polyGraph_union_add_filter_eq_two_card {F : Type*} [DecidableEq F] [CommSemiring F]
    (E : Finset F) (P R : Polynomial F) :
    (polyGraph E P ∪ polyGraph E R).card +
    (E.filter (fun t => P.eval t = R.eval t)).card = 2 * E.card := by
  rw [← polyGraph_inter_card, Finset.card_union_add_card_inter,
      polyGraph_card, polyGraph_card]
  ring

/-- **Pointwise: `p^{|union|} · p^{|filter|} = p^{2|E|}`.** -/
lemma p_pow_polyGraph_union_mul_filter {F : Type*} [DecidableEq F] [CommSemiring F]
    (E : Finset F) (P R : Polynomial F) (p : ℝ) :
    p ^ (polyGraph E P ∪ polyGraph E R).card *
    p ^ (E.filter (fun t => P.eval t = R.eval t)).card = p ^ (2 * E.card) := by
  rw [← pow_add, polyGraph_union_add_filter_eq_two_card]

/-- **Coefficient-pair version**: `p^{|union|} · p^{|filter|} = p^{2|E|}`. -/
lemma p_pow_polyGraph_union_coeffs_mul_filter
    {F : Type*} [Field F] [DecidableEq F]
    (E : Finset F) {d : ℕ} (c c' : Fin d → F) (p : ℝ) :
    p ^ (polyGraph E (polyOfCoeffs c) ∪ polyGraph E (polyOfCoeffs c')).card *
    p ^ (E.filter (fun t => (polyOfCoeffs (c - c')).eval t = 0)).card =
    p ^ (2 * E.card) := by
  rw [show (E.filter (fun t => (polyOfCoeffs (c - c')).eval t = 0)).card =
        (E.filter (fun t => (polyOfCoeffs c).eval t = (polyOfCoeffs c').eval t)).card from ?_]
  · exact p_pow_polyGraph_union_mul_filter E (polyOfCoeffs c) (polyOfCoeffs c') p
  · congr 1
    apply Finset.filter_congr
    intros t _
    rw [show polyOfCoeffs (c - c') = polyOfCoeffs c - polyOfCoeffs c' from
          (polyOfCoeffs_sub c c').symm]
    rw [Polynomial.eval_sub, sub_eq_zero]

/-- **Diagonal: `c = c'` gives `polyGraph_c ∪ polyGraph_c = polyGraph_c`, of size `|E|`.** -/
lemma p_pow_polyGraph_union_diag {F : Type*} [Field F] [DecidableEq F]
    (E : Finset F) {d : ℕ} (c : Fin d → F) (p : ℝ) :
    p ^ (polyGraph E (polyOfCoeffs c) ∪ polyGraph E (polyOfCoeffs c)).card =
    p ^ E.card := by
  rw [Finset.union_idempotent, polyGraph_card]

/-- **Sum bound on the diagonal contribution**: `∑_c p^|polyGraph_c ∪ polyGraph_c| = |F|^d · p^|E|`. -/
lemma sum_diag_p_pow_polyGraph_union {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (E : Finset F) (d : ℕ) (p : ℝ) :
    (∑ c : Fin d → F,
      p ^ (polyGraph E (polyOfCoeffs c) ∪ polyGraph E (polyOfCoeffs c)).card) =
    (Fintype.card F : ℝ) ^ d * p ^ E.card := by
  rw [show (∑ c : Fin d → F,
        p ^ (polyGraph E (polyOfCoeffs c) ∪ polyGraph E (polyOfCoeffs c)).card) =
        ∑ _c : Fin d → F, p ^ E.card from
        Finset.sum_congr rfl (fun c _ => p_pow_polyGraph_union_diag E c p)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- **First-moment sum form for `polyGraphFamily`**: `∑_S p^|S| = |F|^d · p^|E|`. -/
lemma polyGraphFamily_first_moment_sum {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d : ℕ} (hd : 0 < d) {E : Finset F} (hE : d ≤ E.card) (p : ℝ) :
    (∑ S ∈ polyGraphFamily E d, p ^ S.card) =
    (Fintype.card F : ℝ) ^ d * p ^ E.card := by
  rw [show (∑ S ∈ polyGraphFamily E d, p ^ S.card) =
        ∑ S ∈ polyGraphFamily E d, p ^ E.card from
        Finset.sum_congr rfl (fun S hS => by rw [polyGraphFamily_term_card E d S hS])]
  rw [Finset.sum_const, polyGraphFamily_card hd hE, nsmul_eq_mul]
  push_cast; ring

/-- **`s_1`-bound for `monotoneDNF (polyGraphFamily E d)`**: max sensitivity at 1-inputs ≤ |E|. -/
lemma maxSensitivityOne_polyGraphDNF_le {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (E : Finset F) (d : ℕ) :
    maxSensitivityOne (monotoneDNF (polyGraphFamily E d)) ≤ E.card := by
  apply maxSensitivityOne_monotoneDNF_le
  intros S hS
  exact le_of_eq (polyGraphFamily_term_card E d S hS)

/-- **Monotonicity of `monotoneDNF (polyGraphFamily E d)`**. -/
lemma isMonotone_polyGraphDNF {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (E : Finset F) (d : ℕ) :
    IsMonotone (monotoneDNF (polyGraphFamily E d)) :=
  monotoneDNF_isMonotone _

/-- **`s_0`-bound for polyGraphDNF**: trivial bound by # variables = `|F|^2`. -/
lemma maxSensitivityZero_polyGraphDNF_le {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (E : Finset F) (d : ℕ) :
    maxSensitivityZero (monotoneDNF (polyGraphFamily E d)) ≤ Fintype.card F * Fintype.card F := by
  have h := maxSensitivityZero_le_card (monotoneDNF (polyGraphFamily E d))
  rw [show Fintype.card (F × F) = Fintype.card F * Fintype.card F from
        Fintype.card_prod F F] at h
  exact h

/-- **Sub-lemma**: `|F|^{d - |T|}` (nat sub) equals real `|F|^d / |F|^|T|` for `|T| ≤ d`. -/
lemma F_card_pow_sub_eq_real {F : Type*} [Fintype F]
    {d k : ℕ} (hkd : k ≤ d) (hF_pos : 0 < Fintype.card F) :
    ((Fintype.card F : ℝ) ^ (d - k) : ℝ) =
    (Fintype.card F : ℝ) ^ d / (Fintype.card F : ℝ) ^ k := by
  have h_pow_pos : (0 : ℝ) < (Fintype.card F : ℝ) ^ k :=
    pow_pos (by exact_mod_cast hF_pos) k
  rw [eq_div_iff h_pow_pos.ne', ← pow_add]
  congr 1
  omega

/-- (S1) **Sharp 2nd-moment bound**:
`∑_{c ≠ 0} (1+θ)^|E ∩ roots(P_c)| ≤ |F|^d · (1+θ/|F|)^|E|`. -/
lemma sharp_sum_e_ne_zero_one_plus_pow_filter_le
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d : ℕ} (hd : 0 < d) (hdF : d ≤ Fintype.card F)
    (E : Finset F) {θ : ℝ} (hθ : 0 ≤ θ) :
    (∑ c ∈ ((Finset.univ : Finset (Fin d → F)).erase (0 : Fin d → F)),
      (1 + θ) ^ (E.filter (fun t => (polyOfCoeffs c).eval t = 0)).card) ≤
    (Fintype.card F : ℝ) ^ d * (1 + θ / Fintype.card F) ^ E.card := by
  have hF_pos : 0 < Fintype.card F := lt_of_lt_of_le hd hdF
  have hF_pos_real : (0 : ℝ) < Fintype.card F := by exact_mod_cast hF_pos
  have h_step1 :
      (∑ c ∈ ((Finset.univ : Finset (Fin d → F)).erase (0 : Fin d → F)),
        (1 + θ) ^ (E.filter (fun t => (polyOfCoeffs c).eval t = 0)).card) =
      ∑ c ∈ ((Finset.univ : Finset (Fin d → F)).erase (0 : Fin d → F)),
        ∑ T ∈ E.powerset,
          (if ∀ t ∈ T, (polyOfCoeffs c).eval t = 0 then θ ^ T.card else 0) := by
    apply Finset.sum_congr rfl
    intros c _
    rw [one_plus_pow_eq_sum_powerset]
    have h := sum_powerset_filter_eq_sum_with_indicator E c θ
    convert h using 2 with T hT
    congr 1
  have h_step2 :
      (∑ c ∈ ((Finset.univ : Finset (Fin d → F)).erase (0 : Fin d → F)),
        ∑ T ∈ E.powerset,
          (if ∀ t ∈ T, (polyOfCoeffs c).eval t = 0 then θ ^ T.card else 0)) =
      ∑ T ∈ E.powerset,
        ∑ c ∈ ((Finset.univ : Finset (Fin d → F)).erase (0 : Fin d → F)),
          (if ∀ t ∈ T, (polyOfCoeffs c).eval t = 0 then θ ^ T.card else 0) :=
    Finset.sum_comm
  have h_step3 : ∀ T ∈ E.powerset,
      (∑ c ∈ ((Finset.univ : Finset (Fin d → F)).erase (0 : Fin d → F)),
        (if ∀ t ∈ T, (polyOfCoeffs c).eval t = 0 then θ ^ T.card else 0)) =
      θ ^ T.card *
        (((Finset.univ : Finset (Fin d → F)).erase (0 : Fin d → F)).filter
          (fun c => ∀ t ∈ T, (polyOfCoeffs c).eval t = 0)).card := by
    intros T _
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
        mul_comm]
  have h_step4 : ∀ T ∈ E.powerset,
      θ ^ T.card *
        (((Finset.univ : Finset (Fin d → F)).erase (0 : Fin d → F)).filter
          (fun c => ∀ t ∈ T, (polyOfCoeffs c).eval t = 0)).card ≤
      θ ^ T.card * (if T.card < d then ((Fintype.card F : ℝ) ^ (d - T.card)) else 0) := by
    intros T _
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hθ _)
    by_cases h_lt : T.card < d
    · rw [if_pos h_lt]
      have h_card_le : (((Finset.univ : Finset (Fin d → F)).erase (0 : Fin d → F)).filter
            (fun c => ∀ t ∈ T, (polyOfCoeffs c).eval t = 0)).card ≤
          ((Finset.univ : Finset (Fin d → F)).filter
            (fun c => ∀ t ∈ T, (polyOfCoeffs c).eval t = 0)).card :=
        Finset.card_le_card fun c hc =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2⟩
      exact_mod_cast h_card_le.trans (card_polyOfCoeffs_with_roots_le_general T h_lt.le hdF)
    · rw [if_neg h_lt]
      push Not at h_lt
      rw [show (((Finset.univ : Finset (Fin d → F)).erase (0 : Fin d → F)).filter
            (fun c => ∀ t ∈ T, (polyOfCoeffs c).eval t = 0)) = ∅ from by
        rw [Finset.eq_empty_iff_forall_notMem]
        intros c hc
        obtain ⟨⟨hc_ne, _⟩, h_root⟩ := Finset.mem_filter.mp hc |>.imp_left Finset.mem_erase.mp
        exact hc_ne ((polyOfCoeffs_eq_zero_iff c).mp
          (polyOfCoeffs_eq_zero_of_T_subset_roots c T h_lt h_root))]
      simp
  -- Combine steps 1-4.
  rw [h_step1, h_step2, Finset.sum_congr rfl h_step3]
  refine le_trans (Finset.sum_le_sum h_step4) ?_
  have h_real : ∀ T ∈ E.powerset,
      θ ^ T.card * (if T.card < d then ((Fintype.card F : ℝ) ^ (d - T.card)) else 0) ≤
      (Fintype.card F : ℝ) ^ d * (θ / Fintype.card F) ^ T.card := by
    intros T hT
    by_cases h_lt : T.card < d
    · rw [if_pos h_lt]
      apply le_of_eq
      rw [F_card_pow_sub_eq_real (le_of_lt h_lt) hF_pos, div_pow]
      field_simp
    · rw [if_neg h_lt]
      simp only [mul_zero]
      apply mul_nonneg
      · exact pow_nonneg hF_pos_real.le _
      · exact pow_nonneg (div_nonneg hθ hF_pos_real.le) _
  refine le_trans (Finset.sum_le_sum h_real) ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hF_pos_real.le _)
  rw [show ((1 : ℝ) + θ / Fintype.card F) ^ E.card =
        ∑ T ∈ E.powerset, (θ / Fintype.card F) ^ T.card from
        one_plus_pow_eq_sum_powerset E _]

/-- **Substitution `e = c - c'` over `erase`**: for any `f`,
`∑_{c' ≠ c} f(c - c') = ∑_{e ≠ 0} f(e)`. -/
lemma sum_sub_index_eq_erase {α : Type*} [Fintype α] [DecidableEq α] [AddCommGroup α]
    (c : α) (f : α → ℝ) :
    (∑ c' ∈ ((Finset.univ : Finset α).erase c), f (c - c')) =
    ∑ e ∈ ((Finset.univ : Finset α).erase (0 : α)), f e := by
  apply Finset.sum_bij (fun c' _ => c - c')
  · intros c' hc'
    rw [Finset.mem_erase] at hc'
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h_eq_zero
    apply hc'.1
    have : c = c' := by
      have := sub_eq_zero.mp h_eq_zero
      exact this
    exact this.symm
  · intros c1 _ c2 _ h_eq
    -- c - c1 = c - c2 → c1 = c2
    have : c1 = c - (c - c1) := by abel
    rw [this, h_eq]; abel
  · intros e he
    rw [Finset.mem_erase] at he
    refine ⟨c - e, ?_, ?_⟩
    · rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro h_ce
      apply he.1
      have : c - (c - e) = c - c := by rw [h_ce]
      have h_e : e = 0 := by
        have h1 : c - (c - e) = e := by abel
        rw [h1] at this
        rw [show c - c = (0 : α) from sub_self c] at this
        exact this
      exact h_e
    · abel
  · intros c' _; rfl

/-- **Algebraic identity**: for `p > 0` and `θ = 1/p - 1`,
`p^|union(c,c')| = p^{2|E|} · (1+θ)^|filter_eq(c,c')|`. -/
lemma p_pow_polyGraph_union_eq_one_plus_theta
    {F : Type*} [Field F] [DecidableEq F]
    (E : Finset F) {d : ℕ} (c c' : Fin d → F) {p : ℝ} (hp : 0 < p) :
    p ^ (polyGraph E (polyOfCoeffs c) ∪ polyGraph E (polyOfCoeffs c')).card =
    p ^ (2 * E.card) *
      (1 / p) ^ (E.filter (fun t => (polyOfCoeffs (c - c')).eval t = 0)).card := by
  have h := p_pow_polyGraph_union_coeffs_mul_filter E c c' p
  have hpf_ne : (p : ℝ) ^ (E.filter (fun t => (polyOfCoeffs (c - c')).eval t = 0)).card ≠ 0 :=
    pow_ne_zero _ hp.ne'
  rw [show (1 / p) ^ (E.filter (fun t => (polyOfCoeffs (c - c')).eval t = 0)).card =
        1 / p ^ (E.filter (fun t => (polyOfCoeffs (c - c')).eval t = 0)).card from by
      rw [one_div, inv_pow, one_div]]
  rw [mul_one_div, eq_div_iff hpf_ne]
  exact h

/-- **Sharp off-diagonal sum bound**: combining algebraic identity + substitution + S1,
`∑_{c, c' : c ≠ c'} p^|union(c,c')| ≤ p^{2|E|} · |F|^{2d} · (1+(1/p-1)/|F|)^|E|`. -/
lemma sum_off_diag_p_pow_polyGraph_union_le_sharp
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d : ℕ} (hd : 0 < d) (hdF : d ≤ Fintype.card F) (E : Finset F)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∑ c : Fin d → F, ∑ c' ∈ ((Finset.univ : Finset (Fin d → F)).erase c),
      p ^ (polyGraph E (polyOfCoeffs c) ∪ polyGraph E (polyOfCoeffs c')).card) ≤
    p ^ (2 * E.card) * (Fintype.card F : ℝ) ^ (2 * d) *
      (1 + (1/p - 1) / Fintype.card F) ^ E.card := by
  have h_pointwise : ∀ (c c' : Fin d → F),
      p ^ (polyGraph E (polyOfCoeffs c) ∪ polyGraph E (polyOfCoeffs c')).card =
      p ^ (2 * E.card) *
        (1 + (1/p - 1)) ^
          (E.filter (fun t => (polyOfCoeffs (c - c')).eval t = 0)).card := by
    intros c c'
    rw [show (1 + (1/p - 1) : ℝ) = 1/p from by ring]
    exact p_pow_polyGraph_union_eq_one_plus_theta E c c' hp0
  simp_rw [h_pointwise, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun c _ =>
    sum_sub_index_eq_erase c (fun e =>
      (1 + (1/p - 1)) ^ (E.filter (fun t => (polyOfCoeffs e).eval t = 0)).card),
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  have hθ_nonneg : (0 : ℝ) ≤ 1/p - 1 := by
    rw [le_sub_iff_add_le, zero_add, le_div_iff₀ hp0]; linarith
  have h_S1 := sharp_sum_e_ne_zero_one_plus_pow_filter_le hd hdF E hθ_nonneg
  push_cast
  have hp_pow_nonneg : (0 : ℝ) ≤ p ^ (2 * E.card) := pow_nonneg hp0.le _
  have hF_pow_nonneg : (0 : ℝ) ≤ (Fintype.card F : ℝ) ^ d := by positivity
  rw [show (Fintype.card F : ℝ) ^ (2 * d) = (Fintype.card F : ℝ) ^ d * (Fintype.card F : ℝ) ^ d
        from by rw [show (2 * d : ℕ) = d + d from by ring, pow_add]]
  nlinarith [mul_le_mul_of_nonneg_left h_S1 hF_pow_nonneg, hp_pow_nonneg]

/-- **Sharp 2nd-moment for polyGraphFamily** (combining diagonal + sharp off-diagonal):
`∑_{S, S'} p^|S∪S'| ≤ |F|^d · p^|E| + (|F|^d · p^|E|)² · (1+(1/p-1)/|F|)^|E|`. -/
lemma polyGraphFamily_second_moment_sharp_le
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d : ℕ} (hd : 0 < d) {E : Finset F} (hE : d ≤ E.card) (hdF : d ≤ Fintype.card F)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∑ S ∈ polyGraphFamily E d, ∑ S' ∈ polyGraphFamily E d, p ^ (S ∪ S').card) ≤
    (Fintype.card F : ℝ) ^ d * p ^ E.card +
    ((Fintype.card F : ℝ) ^ d * p ^ E.card) ^ 2 *
      (1 + (1/p - 1) / Fintype.card F) ^ E.card := by
  rw [polyGraphFamily_double_sum_eq hd hE]
  -- Split: diagonal + off-diagonal via `Finset.add_sum_erase`.
  have h_split :
      (∑ c : Fin d → F, ∑ c' : Fin d → F,
        p ^ (polyGraph E (polyOfCoeffs c) ∪ polyGraph E (polyOfCoeffs c')).card) =
      (∑ c : Fin d → F,
        p ^ (polyGraph E (polyOfCoeffs c) ∪ polyGraph E (polyOfCoeffs c)).card) +
      ∑ c : Fin d → F, ∑ c' ∈ ((Finset.univ : Finset (Fin d → F)).erase c),
        p ^ (polyGraph E (polyOfCoeffs c) ∪ polyGraph E (polyOfCoeffs c')).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ =>
      (Finset.add_sum_erase _ _ (Finset.mem_univ c)).symm
  rw [h_split, sum_diag_p_pow_polyGraph_union E d p]
  have h_sq_eq : ((Fintype.card F : ℝ) ^ d * p ^ E.card) ^ 2 =
                  p ^ (2 * E.card) * (Fintype.card F : ℝ) ^ (2 * d) := by
    rw [show (2 * E.card : ℕ) = E.card + E.card from by ring,
        show (2 * d : ℕ) = d + d from by ring, pow_add, pow_add]; ring
  linarith [h_sq_eq.symm ▸ sum_off_diag_p_pow_polyGraph_union_le_sharp hd hdF E hp0 hp1]

/-- **Common second-moment-bound helper**: from `polyGraphFamily_second_moment_sharp_le`,
the double sum is bounded by `λ + λ² · D` (where `λ = |F|^d · p^|E|`). -/
private lemma poly_secondMoment_le_lam_plus_lam_sq_D
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d : ℕ} (hd : 0 < d) (hdF : d ≤ Fintype.card F)
    {E : Finset F} (hE : d ≤ E.card) {p D : ℝ}
    (hp_pos : 0 < p) (hp1 : p ≤ 1)
    (hD : (1 + (1/p - 1) / Fintype.card F) ^ E.card ≤ D) :
    (∑ S ∈ polyGraphFamily E d, ∑ S' ∈ polyGraphFamily E d, p ^ (S ∪ S').card) ≤
    (Fintype.card F : ℝ) ^ d * p ^ E.card +
    ((Fintype.card F : ℝ) ^ d * p ^ E.card) ^ 2 * D := by
  have h_sq_nonneg : (0 : ℝ) ≤ ((Fintype.card F : ℝ) ^ d * p ^ E.card) ^ 2 := sq_nonneg _
  have h_scale : ((Fintype.card F : ℝ) ^ d * p ^ E.card) ^ 2 *
                  (1 + (1/p - 1) / Fintype.card F) ^ E.card ≤
                 ((Fintype.card F : ℝ) ^ d * p ^ E.card) ^ 2 * D :=
    mul_le_mul_of_nonneg_left hD h_sq_nonneg
  linarith [polyGraphFamily_second_moment_sharp_le hd hE hdF hp_pos hp1]

/-- **Sharp Inf bound for polyGraphDNF**: using the sharp 2nd moment.
`Inf_p ≥ |E| · (E[Y] - E[Y]² · D)` where `D ≥ (1+(1/p-1)/|F|)^|E|`. -/
lemma infP_polyGraphDNF_ge_sharp
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d : ℕ} (hd : 0 < d) (hdF : d ≤ Fintype.card F)
    {E : Finset F} (hE : d ≤ E.card)
    {p D : ℝ}
    (hp_pos : 0 < p) (hp1 : p ≤ 1)
    (hD : (1 + (1/p - 1) / Fintype.card F) ^ E.card ≤ D) :
    (E.card : ℝ) *
      ((Fintype.card F : ℝ) ^ d * p ^ E.card -
       ((Fintype.card F : ℝ) ^ d * p ^ E.card) ^ 2 * D) ≤
    infP p (monotoneDNF (polyGraphFamily E d)) := by
  have hL : ∀ S ∈ polyGraphFamily E d, E.card ≤ S.card := fun S hS =>
    le_of_eq (polyGraphFamily_term_card E d S hS).symm
  have h_inf := infP_monotoneDNF_ge_first_minus_factorial hp_pos.le hp1
    (polyGraphFamily E d) E.card hL
  rw [biasedExpectation_subsetSatisfiedCount,
      biasedExpectation_subsetSatisfiedCount_factorial,
      polyGraphFamily_first_moment_sum hd hE p] at h_inf
  refine h_inf.trans' (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  linarith [poly_secondMoment_le_lam_plus_lam_sq_D hd hdF hE hp_pos hp1 hD]

/-- **Sharp probability lower bound for polyGraphDNF**: same chain. -/
lemma biasedProb_polyGraphDNF_ge_sharp
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d : ℕ} (hd : 0 < d) (hdF : d ≤ Fintype.card F)
    {E : Finset F} (hE : d ≤ E.card)
    {p D : ℝ}
    (hp_pos : 0 < p) (hp1 : p ≤ 1)
    (hD : (1 + (1/p - 1) / Fintype.card F) ^ E.card ≤ D) :
    ((Fintype.card F : ℝ) ^ d * p ^ E.card -
     ((Fintype.card F : ℝ) ^ d * p ^ E.card) ^ 2 * D) ≤
    biasedProb p (Finset.univ.filter
      (fun x : (F × F) → Bool => monotoneDNF (polyGraphFamily E d) x = true)) := by
  have h_prob := biasedProb_monotoneDNF_ge_first_minus_factorial hp_pos.le hp1
    (polyGraphFamily E d)
  rw [biasedExpectation_subsetSatisfiedCount,
      biasedExpectation_subsetSatisfiedCount_factorial,
      polyGraphFamily_first_moment_sum hd hE p] at h_prob
  linarith [h_prob, poly_secondMoment_le_lam_plus_lam_sq_D hd hdF hE hp_pos hp1 hD]

/-- **Density bound for polyGraphFamily DNF**: `Pr_p[F=1] ≤ |F|^d · p^|E|`. -/
lemma biasedProb_polyGraphDNF_le_first_moment
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {d : ℕ} (hd : 0 < d) {E : Finset F} (hE : d ≤ E.card)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    biasedProb p (Finset.univ.filter
      (fun x : (F × F) → Bool => monotoneDNF (polyGraphFamily E d) x = true)) ≤
    (Fintype.card F : ℝ) ^ d * p ^ E.card := by
  refine le_trans (biasedProb_monotoneDNF_le_first_moment _ hp0 hp1) ?_
  rw [polyGraphFamily_first_moment_sum hd hE]

/-- **Gadget existence per large prime, for all biases in `[a, b]`**:
For each sufficiently large prime `Q`, and any `p ∈ [a, b]`, an explicit
gadget exists with the bounds. Constants are uniform in `p`. -/
def GadgetExistsForAllBiases (a b : ℝ) : Prop :=
  ∃ (c : ℝ) (K : ℕ), 0 < c ∧
    ∀ (Q : ℕ) [Fact Q.Prime], K ≤ Q →
    ∀ p ∈ Set.Icc a b,
      ∃ F : ((ZMod Q × ZMod Q) → Bool) → Bool,
        IsMonotone F ∧
        (maxSensitivityOne F : ℝ) ≤ (Q : ℝ) ∧
        (maxSensitivityZero F : ℝ) ≤ (Q : ℝ) ^ 2 ∧
        c * (Q : ℝ) ≤ infP p F ∧
        c ≤ biasedProb p
          (Finset.univ.filter (fun x : (ZMod Q × ZMod Q) → Bool => F x = true)) ∧
        biasedProb p
          (Finset.univ.filter (fun x : (ZMod Q × ZMod Q) → Bool => F x = true)) ≤ 1/3

/-- **Parameter record** for the polynomial-graph gadget. Bundles all the
hypotheses needed to extract the bounds. -/
structure PolyGraphGadgetParams
    (F : Type*) [Field F] [DecidableEq F] [Fintype F]
    (p c D : ℝ) where
  d : ℕ
  E : Finset F
  hd : 0 < d
  hdF : d ≤ Fintype.card F
  hE : d ≤ E.card
  hE_le_card : (E.card : ℝ) ≤ Fintype.card F
  hp_pos : 0 < p
  hp1 : p ≤ 1
  hD : (1 + (1/p - 1) / Fintype.card F) ^ E.card ≤ D
  h_first_upper : (Fintype.card F : ℝ) ^ d * p ^ E.card ≤ 1 / 3
  h_first_lower : c ≤
    (Fintype.card F : ℝ) ^ d * p ^ E.card -
    ((Fintype.card F : ℝ) ^ d * p ^ E.card) ^ 2 * D
  h_inf_lower : c * (Fintype.card F : ℝ) ≤
    (E.card : ℝ) *
      ((Fintype.card F : ℝ) ^ d * p ^ E.card -
       ((Fintype.card F : ℝ) ^ d * p ^ E.card) ^ 2 * D)

/-- **Elementary extraction**: from `PolyGraphGadgetParams`, build the gadget
satisfying all the bounds required by `GadgetExistsForAllBiases`. -/
lemma gadget_from_polyGraphParams
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {p c D : ℝ}
    (P : PolyGraphGadgetParams F p c D) :
    ∃ G : ((F × F) → Bool) → Bool,
      IsMonotone G ∧
      (maxSensitivityOne G : ℝ) ≤ (Fintype.card F : ℝ) ∧
      (maxSensitivityZero G : ℝ) ≤ (Fintype.card F : ℝ) ^ 2 ∧
      c * (Fintype.card F : ℝ) ≤ infP p G ∧
      c ≤ biasedProb p
        (Finset.univ.filter (fun x : (F × F) → Bool => G x = true)) ∧
      biasedProb p
        (Finset.univ.filter (fun x : (F × F) → Bool => G x = true)) ≤ 1/3 := by
  refine ⟨monotoneDNF (polyGraphFamily P.E P.d), isMonotone_polyGraphDNF P.E P.d,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- s_1 ≤ |F|
    have h_real : (maxSensitivityOne (monotoneDNF (polyGraphFamily P.E P.d)) : ℝ) ≤
                  (P.E.card : ℝ) := by exact_mod_cast maxSensitivityOne_polyGraphDNF_le P.E P.d
    linarith [h_real, P.hE_le_card]
  · -- s_0 ≤ |F|²
    have h_real : (maxSensitivityZero (monotoneDNF (polyGraphFamily P.E P.d)) : ℝ) ≤
                  ((Fintype.card F * Fintype.card F : ℕ) : ℝ) := by
      exact_mod_cast maxSensitivityZero_polyGraphDNF_le P.E P.d
    push_cast at h_real
    nlinarith [h_real, sq_nonneg (Fintype.card F : ℝ)]
  · exact P.h_inf_lower.trans (infP_polyGraphDNF_ge_sharp P.hd P.hdF P.hE P.hp_pos P.hp1 P.hD)
  · exact P.h_first_lower.trans
      (biasedProb_polyGraphDNF_ge_sharp P.hd P.hdF P.hE P.hp_pos P.hp1 P.hD)
  · exact (biasedProb_polyGraphDNF_le_first_moment P.hd P.hE P.hp_pos.le P.hp1).trans
      P.h_first_upper

/-- **Pure-arithmetic parameter record**: bundles all the inequalities needed for
the polynomial-graph gadget without referencing `Field` instances. -/
structure PolyGraphArithmeticParams (Q : ℕ) (p c D : ℝ) where
  d : ℕ
  L : ℕ
  hd : 0 < d
  hLd : d ≤ L
  hLQ : L ≤ Q
  hp_pos : 0 < p
  hp1 : p ≤ 1
  hD : (1 + (1 / p - 1) / (Q : ℝ)) ^ L ≤ D
  h_first_upper : (Q : ℝ) ^ d * p ^ L ≤ 1 / 3
  h_first_lower :
    c ≤ (Q : ℝ) ^ d * p ^ L -
      ((Q : ℝ) ^ d * p ^ L) ^ 2 * D
  h_inf_lower :
    c * (Q : ℝ) ≤
      (L : ℝ) *
        ((Q : ℝ) ^ d * p ^ L -
          ((Q : ℝ) ^ d * p ^ L) ^ 2 * D)

/-- **Conversion**: arithmetic params → `PolyGraphGadgetParams` over `ZMod Q`. -/
lemma arithmeticParams_to_polyGraphParams
    {Q : ℕ} [hQp : Fact Q.Prime]
    {p c D : ℝ}
    (A : PolyGraphArithmeticParams Q p c D) :
    Nonempty (@PolyGraphGadgetParams (ZMod Q) (ZMod.instField Q)
      (ZMod.decidableEq Q) (ZMod.fintype Q) p c D) := by
  haveI : NeZero Q := ⟨hQp.1.pos.ne'⟩
  have hQcard : Fintype.card (ZMod Q) = Q := ZMod.card Q
  -- Choose E ⊆ ZMod Q with |E| = A.L.
  obtain ⟨E, _hsub, hcard⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (ZMod Q)))
      (n := A.L)
      (by rw [Finset.card_univ, hQcard]; exact A.hLQ)
  refine ⟨{
    d := A.d
    E := E
    hd := A.hd
    hdF := by rw [hQcard]; exact le_trans A.hLd A.hLQ
    hE := by rw [hcard]; exact A.hLd
    hE_le_card := by
      rw [hcard, hQcard]
      exact_mod_cast A.hLQ
    hp_pos := A.hp_pos
    hp1 := A.hp1
    hD := by rw [hcard, hQcard]; exact A.hD
    h_first_upper := by rw [hcard, hQcard]; exact A.h_first_upper
    h_first_lower := by rw [hcard, hQcard]; exact A.h_first_lower
    h_inf_lower := by rw [hcard, hQcard]; exact A.h_inf_lower
  }⟩

/-- **Sub-claim**: `(1 + x/Q)^L ≤ exp(x)` for `0 ≤ x`, `0 < Q`, `L ≤ Q`. -/
lemma one_plus_div_pow_le_exp {x : ℝ} (hx : 0 ≤ x) {Q L : ℕ} (hQ : 0 < Q) (hL : L ≤ Q) :
    (1 + x / Q) ^ L ≤ Real.exp x := by
  have hQ_real : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hxQ_nn : 0 ≤ x / Q := div_nonneg hx hQ_real.le
  have h1 : 1 + x / Q ≤ Real.exp (x / Q) := by
    rw [add_comm]; exact Real.add_one_le_exp _
  have h2 : (1 + x / Q) ^ L ≤ (Real.exp (x / Q)) ^ L :=
    pow_le_pow_left₀ (by linarith) h1 _
  rw [show (Real.exp (x / Q)) ^ L = Real.exp ((L : ℝ) * (x / Q)) from
    (Real.exp_nat_mul (x / Q) L).symm] at h2
  refine le_trans h2 ?_
  apply Real.exp_le_exp.mpr
  -- L · x / Q ≤ x. Need L/Q ≤ 1 (since L ≤ Q) and x ≥ 0.
  have hL_le : (L : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hL
  have h_div : (L : ℝ) / Q ≤ 1 := by
    rw [div_le_one hQ_real]; exact hL_le
  calc (L : ℝ) * (x / Q) = ((L : ℝ) / Q) * x := by ring
    _ ≤ 1 * x := by exact mul_le_mul_of_nonneg_right h_div hx
    _ = x := one_mul x

/-- **Sub-claim**: there exists `K` such that `b^K ≤ 1/(8·D)` and `b^K ≤ 1/3`. -/
lemma exists_K_for_polyGraph_bounds {b D : ℝ} (hb_pos : 0 < b) (hb_lt : b < 1)
    (hD_pos : 0 < D) :
    ∃ K : ℕ, b ^ K ≤ 1 / (8 * D) ∧ b ^ K ≤ 1 / 3 := by
  have h_tendsto : Filter.Tendsto (fun k : ℕ => b ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hb_pos.le hb_lt
  have h_pos : (0 : ℝ) < min (1 / (8 * D)) (1 / 3) := by positivity
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp h_tendsto _ h_pos
  have h_dist : dist (b ^ K) 0 < min (1 / (8 * D)) (1 / 3) := hK K (le_refl K)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hb_pos.le _)] at h_dist
  exact ⟨K, le_trans h_dist.le (min_le_left _ _),
         le_trans h_dist.le (min_le_right _ _)⟩

/-- **Helper**: `log(1/p) > 0` for `p ∈ (0, 1)`. -/
lemma log_inv_pos_of_lt_one {p : ℝ} (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    0 < Real.log (1 / p) := by
  apply Real.log_pos
  rw [lt_one_div (by norm_num : (0:ℝ) < 1) hp_pos, one_div_one]
  exact hp_lt_one

/-- **Helper**: `log(1/p)` bounds for `p ∈ [a, b] ⊆ (0, 1)`. -/
lemma log_inv_mem_bounds {a b p : ℝ} (ha : 0 < a) (hab : a < b) (_hb : b < 1)
    (hp : p ∈ Set.Icc a b) :
    Real.log (1 / b) ≤ Real.log (1 / p) ∧ Real.log (1 / p) ≤ Real.log (1 / a) := by
  obtain ⟨hap, hpb⟩ := hp
  have hp_pos : 0 < p := lt_of_lt_of_le ha hap
  have hb_pos : 0 < b := lt_trans ha hab
  refine ⟨Real.log_le_log (by positivity) (one_div_le_one_div_of_le hp_pos hpb),
          Real.log_le_log (by positivity) (one_div_le_one_div_of_le ha hap)⟩

/-- **Helper**: `Nat.floor` bounds. -/
lemma natFloor_bounds {x : ℝ} (hx : 0 ≤ x) :
    (⌊x⌋₊ : ℝ) ≤ x ∧ x - 1 < (⌊x⌋₊ : ℝ) := by
  refine ⟨Nat.floor_le hx, ?_⟩
  have h := Nat.lt_floor_add_one x
  linarith

/-- **Helper**: `Nat.floor` is positive when `x ≥ 1`. -/
lemma natFloor_pos_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 < ⌊x⌋₊ := by
  have h : (1 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  omega

/-- **Helper**: `Nat.ceil` bounds, when `x ≥ 0`. -/
lemma natCeil_bounds {x : ℝ} (hx : 0 ≤ x) :
    x ≤ (⌈x⌉₊ : ℝ) ∧ (⌈x⌉₊ : ℝ) < x + 1 :=
  ⟨Nat.le_ceil x, Nat.ceil_lt_add_one hx⟩

/-- **Predicate**: Q is "large" relative to (a, b, K) — sufficient for the
arithmetic bounds in `exists_dL_for_polyGraphArithmeticParams`. -/
structure LargeQForPolyGraph (a b : ℝ) (K Q : ℕ) : Prop where
  hQ16 : 16 ≤ Q
  hKmargin : 2 * K + 4 ≤ Q
  hAmax_le_half_log : Real.log (1 / a) ≤ Real.log (Q : ℝ) / 2
  hlog_over_Amin_le_quarter :
    Real.log (Q : ℝ) / Real.log (1 / b) ≤ (Q : ℝ) / 4

namespace LargeQForPolyGraph
variable {a b : ℝ} {K Q : ℕ}

/-- `Q` is positive (since `Q ≥ 16`). -/
lemma Q_pos (h : LargeQForPolyGraph a b K Q) : 0 < Q := by have := h.hQ16; omega

/-- `Q` is positive as a real number. -/
lemma Q_pos_real (h : LargeQForPolyGraph a b K Q) : (0 : ℝ) < Q := by
  exact_mod_cast h.Q_pos

/-- `Q ≥ 16` as a real-number bound. -/
lemma Q_ge_16_real (h : LargeQForPolyGraph a b K Q) : (16 : ℝ) ≤ Q := by
  exact_mod_cast h.hQ16

/-- `2K + 4 ≤ Q` as a real-number bound. -/
lemma Kmargin_real (h : LargeQForPolyGraph a b K Q) :
    ((2 * K + 4 : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast h.hKmargin

/-- `Q/2 ≤ Q - K - 2` (real form, half-margin from `2K + 4 ≤ Q`). -/
lemma half_margin (h : LargeQForPolyGraph a b K Q) :
    (Q : ℝ) / 2 ≤ (Q : ℝ) - K - 2 := by
  have := h.Kmargin_real; push_cast at this; linarith

/-- `0 ≤ Q - K - 2` (consequence of `2K + 4 ≤ Q`). -/
lemma nonneg_margin (h : LargeQForPolyGraph a b K Q) :
    (0 : ℝ) ≤ (Q : ℝ) - K - 2 := by
  have := h.Kmargin_real; push_cast at this; linarith

end LargeQForPolyGraph

/-- **Sub-claim (E1)**: for any C, eventually `C ≤ log Q` for `Q : ℕ`. -/
lemma exists_log_atLeast {C : ℝ} :
    ∃ N : ℕ, ∀ Q : ℕ, N ≤ Q → C ≤ Real.log (Q : ℝ) :=
  Filter.eventually_atTop.mp <|
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop C

/-- **Sub-claim (E2)**: for any C > 0, eventually `log Q / Q ≤ C` for `Q : ℕ`. -/
lemma exists_log_div_Q_le {C : ℝ} (hC : 0 < C) :
    ∃ N : ℕ, ∀ Q : ℕ, N ≤ Q → Real.log (Q : ℝ) / (Q : ℝ) ≤ C := by
  have h_isLittleO : Real.log =o[Filter.atTop] (id : ℝ → ℝ) := by
    have := Real.isLittleO_pow_log_id_atTop (n := 1)
    simpa using this
  have h_tendsto_real : Filter.Tendsto (fun x : ℝ => Real.log x / x)
      Filter.atTop (nhds 0) := by
    have := h_isLittleO.tendsto_div_nhds_zero
    simpa using this
  have h_tendsto : Filter.Tendsto (fun Q : ℕ => Real.log (Q : ℝ) / (Q : ℝ))
      Filter.atTop (nhds 0) :=
    h_tendsto_real.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_tendsto C hC
  refine ⟨N, fun Q hQ => ?_⟩
  have h_dist : dist (Real.log (Q : ℝ) / (Q : ℝ)) 0 < C := hN Q hQ
  rw [Real.dist_eq, sub_zero] at h_dist
  have h_le : Real.log (Q : ℝ) / (Q : ℝ) ≤ |Real.log (Q : ℝ) / (Q : ℝ)| := le_abs_self _
  linarith

/-- **Existence**: for any (a, b, K), there's a threshold `N` such that all
`Q ≥ N` are "large" in the sense of `LargeQForPolyGraph`. -/
lemma exists_largeQForPolyGraph
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (K : ℕ) :
    ∃ N : ℕ, ∀ Q : ℕ, N ≤ Q → LargeQForPolyGraph a b K Q := by
  have hb_pos : 0 < b := lt_trans ha hab
  have h_log_inv_a_pos : 0 < Real.log (1 / a) :=
    Real.log_pos (by rw [lt_one_div (by norm_num : (0:ℝ) < 1) ha, one_div_one]; linarith)
  have h_log_inv_b_pos : 0 < Real.log (1 / b) :=
    Real.log_pos (by rw [lt_one_div (by norm_num : (0:ℝ) < 1) hb_pos, one_div_one]; exact hb)
  obtain ⟨N1, hN1⟩ := exists_log_atLeast (C := 2 * Real.log (1 / a))
  obtain ⟨N2, hN2⟩ := exists_log_div_Q_le (C := Real.log (1 / b) / 4) (by positivity)
  refine ⟨max (max 16 (2 * K + 4)) (max N1 N2), fun Q hQ => ?_⟩
  have h16 : 16 ≤ Q := by have := le_max_left 16 (2 * K + 4); omega
  have hKm : 2 * K + 4 ≤ Q := by have := le_max_right 16 (2 * K + 4); omega
  have hN1_le : N1 ≤ Q := by have := le_max_left N1 N2; omega
  have hN2_le : N2 ≤ Q := by have := le_max_right N1 N2; omega
  have hQ_pos : 0 < (Q : ℝ) := by
    have : (16 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast h16
    linarith
  refine ⟨h16, hKm, by linarith [hN1 Q hN1_le], ?_⟩
  rw [div_le_div_iff₀ h_log_inv_b_pos (by norm_num : (0:ℝ) < 4)]
  have h_logQ_div : Real.log (Q : ℝ) / (Q : ℝ) ≤ Real.log (1 / b) / 4 := hN2 Q hN2_le
  have h_mul : Real.log (Q : ℝ) ≤ (Q : ℝ) * (Real.log (1 / b) / 4) := by
    have := mul_le_mul_of_nonneg_right h_logQ_div hQ_pos.le
    have h_eq : Real.log (Q : ℝ) / (Q : ℝ) * (Q : ℝ) = Real.log (Q : ℝ) := by field_simp
    linarith [h_eq ▸ this]
  nlinarith [h_mul]

/-- **lam·D bound**: from `lam ≤ b^K` and `b^K · D ≤ 1/8`, derive `lam · D ≤ 1/8`. -/
lemma lam_D_small {lam b D : ℝ} {K : ℕ}
    (hlam_up : lam ≤ b ^ K) (hK_bD : b ^ K ≤ 1 / (8 * D))
    (hD_pos : 0 < D) : lam * D ≤ 1 / 8 := by
  have h1 := mul_le_mul_of_nonneg_right hlam_up hD_pos.le
  have h2 := mul_le_mul_of_nonneg_right hK_bD hD_pos.le
  have h_eq : 1 / (8 * D) * D = 1 / 8 := by field_simp
  linarith [h_eq ▸ h2]

/-- **Quadratic bracket bound**: with `lam ≥ 0` and `lam · D ≤ 1/8`,
we have `lam - lam² · D ≥ (7/8) * lam`. -/
lemma quadratic_bracket_bound {lam D : ℝ}
    (hlam_nonneg : 0 ≤ lam) (hlamD_small : lam * D ≤ 1 / 8) :
    lam - lam ^ 2 * D ≥ lam * (7 / 8) := by
  have h_sq : lam ^ 2 * D = lam * (lam * D) := by ring
  have h_prod_le : lam * (lam * D) ≤ lam * (1 / 8) :=
    mul_le_mul_of_nonneg_left hlamD_small hlam_nonneg
  have h_lam_8 : lam - lam * (1/8) = lam * (7/8) := by ring
  linarith [h_sq ▸ h_prod_le]

/-- **Quarter bracket bound**: with `lam ≥ a^(K+1) ≥ 0`, `lam · D ≤ 1/8`,
`(1/4) * a^(K+1) ≤ lam - lam² · D`. -/
lemma quarter_bracket_bound {lam a D : ℝ} {K : ℕ}
    (hlam_low : a ^ (K + 1) ≤ lam) (hlam_nonneg : 0 ≤ lam)
    (hlamD_small : lam * D ≤ 1 / 8) :
    (1 / 4 : ℝ) * a ^ (K + 1) ≤ lam - lam ^ 2 * D := by
  have hbracket := quadratic_bracket_bound hlam_nonneg hlamD_small
  have h_lower : a ^ (K + 1) * (7 / 8) ≤ lam * (7 / 8) :=
    mul_le_mul_of_nonneg_right hlam_low (by norm_num)
  linarith

/-- **Half bracket bound**: with `lam ≥ a^(K+1) ≥ 0`, `lam · D ≤ 1/8`,
`(1/2) * a^(K+1) ≤ lam - lam² · D`. -/
lemma half_bracket_bound {lam a D : ℝ} {K : ℕ}
    (hlam_low : a ^ (K + 1) ≤ lam) (hlam_nonneg : 0 ≤ lam)
    (hlamD_small : lam * D ≤ 1 / 8) :
    (1 / 2 : ℝ) * a ^ (K + 1) ≤ lam - lam ^ 2 * D := by
  have hbracket := quadratic_bracket_bound hlam_nonneg hlamD_small
  have h_lower : a ^ (K + 1) * (7 / 8) ≤ lam * (7 / 8) :=
    mul_le_mul_of_nonneg_right hlam_low (by norm_num)
  linarith

/-- **Q to L conversion**: from `Q/2 ≤ L` and `0 ≤ a^(K+1)`,
`(1/4) * a^(K+1) * Q ≤ L * ((1/2) * a^(K+1))`. -/
lemma quarter_Q_le_half_L {a : ℝ} {K Q L : ℕ}
    (hL_ge_halfQ : (Q : ℝ) / 2 ≤ (L : ℝ))
    (hapos : 0 ≤ a ^ (K + 1)) :
    ((1 / 4 : ℝ) * a ^ (K + 1)) * (Q : ℝ) ≤
      (L : ℝ) * ((1 / 2 : ℝ) * a ^ (K + 1)) := by
  have hQ_le_2L : (Q : ℝ) ≤ 2 * (L : ℝ) := by linarith
  calc ((1 / 4 : ℝ) * a ^ (K + 1)) * (Q : ℝ)
      ≤ ((1 / 4 : ℝ) * a ^ (K + 1)) * (2 * (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hQ_le_2L (by positivity)
    _ = (L : ℝ) * ((1 / 2 : ℝ) * a ^ (K + 1)) := by ring

/-- **Lambda bounds via ceiling**: with `L = ⌈d·log Q/A + K⌉₊`, we have
`p^(K+1) ≤ Q^d · p^L ≤ p^K`. -/
lemma lambda_bounds_of_ceil
    {Q p A : ℝ} {d K L : ℕ}
    (hQ_pos : 0 < Q) (hp_pos : 0 < p)
    (hA_def : A = Real.log (1 / p))
    (hA_pos : 0 < A)
    (hL_low : (d : ℝ) * Real.log Q / A + K ≤ (L : ℝ))
    (hL_high : (L : ℝ) ≤ (d : ℝ) * Real.log Q / A + K + 1) :
    p ^ (K + 1) ≤ Q ^ d * p ^ L ∧ Q ^ d * p ^ L ≤ p ^ K := by
  have hlogp : Real.log p = -A := by
    rw [hA_def, Real.log_div one_ne_zero hp_pos.ne', Real.log_one]; ring
  -- Each `n^k = exp(k · log n)` for n > 0:
  have toExp : ∀ (n : ℝ) (hn : 0 < n) (k : ℕ),
      n ^ k = Real.exp ((k : ℝ) * Real.log n) :=
    fun n hn k => by rw [Real.exp_nat_mul, Real.exp_log hn]
  refine ⟨?_, ?_⟩
  · rw [toExp Q hQ_pos d, toExp p hp_pos L, show p ^ (K + 1) =
        Real.exp (((K + 1 : ℕ) : ℝ) * Real.log p) from toExp p hp_pos (K + 1),
      ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [hlogp]
    have h := mul_le_mul_of_nonneg_right hL_high hA_pos.le
    have h_eq : ((d : ℝ) * Real.log Q / A + K + 1) * A =
        (d : ℝ) * Real.log Q + ((K : ℝ) + 1) * A := by field_simp; ring
    push_cast; nlinarith [h_eq ▸ h]
  · rw [toExp Q hQ_pos d, toExp p hp_pos L, toExp p hp_pos K, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [hlogp]
    have h := mul_le_mul_of_nonneg_right hL_low hA_pos.le
    have h_eq : ((d : ℝ) * Real.log Q / A + K) * A =
        (d : ℝ) * Real.log Q + (K : ℝ) * A := by field_simp
    nlinarith [h_eq ▸ h]

/-- (P-step) **For each `Q ≥ K` and `p ∈ [a, b]`, choose `(d, L)` realizing
the gadget bounds** with the chosen constants `c, K, D`. This is the per-`Q`
parameter-selection sub-claim. The proof reduces to 7 explicit inequalities;
each is its own sub-lemma deferred for closure.

The construction (note2): `A := log(1/p)`, `d := ⌊(Q-K-2)·A/log Q⌋`,
`L := ⌊d·log Q/A + K⌋`. The inequalities to verify (with `λ := Q^d · p^L`):
- (i) `0 < d` — since `Q-K-2 ≥ 1` and `A/log Q > 0`.
- (ii) `d ≤ L` — since `K ≥ 1` (or use d ≥ 1 ≤ L).
- (iii) `L ≤ Q` — since L ≈ Q-K-2+K = Q-2.
- (iv) `(1+(1/p-1)/Q)^L ≤ D` — by `one_plus_div_pow_le_exp`.
- (v) `λ ≤ 1/3` — since `λ ≤ b^(K-1) ≤ 1/3` (chosen K).
- (vi) `c ≤ λ - λ²·D` — since `λ ≥ a^K` and `λ²·D ≤ a^K · 1/4`.
- (vii) `c·Q ≤ L · (λ - λ²·D)` — multiplying (vi) by L ≥ Q/2. -/
lemma exists_dL_for_polyGraphArithmeticParams
    {a b c D : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    {K : ℕ}
    (hc_small : c ≤ (1 / 4 : ℝ) * a ^ (K + 1))
    (hD : D = Real.exp (1/a - 1))
    (hK_bD : b ^ K ≤ 1 / (8 * D))
    (hK_b : b ^ K ≤ 1 / 3)
    {Q : ℕ} (hLarge : LargeQForPolyGraph a b K Q)
    {p : ℝ} (hp : p ∈ Set.Icc a b) :
    Nonempty (PolyGraphArithmeticParams Q p c D) := by
  classical
  obtain ⟨ha_p, hb_p⟩ := hp
  have hp_pos : 0 < p := lt_of_lt_of_le ha ha_p
  have hp_lt_one : p < 1 := lt_of_le_of_lt hb_p hb
  have hp_le_one : p ≤ 1 := le_of_lt hp_lt_one
  have hb_pos : 0 < b := lt_trans ha hab
  set A : ℝ := Real.log (1 / p) with hA_def
  have hA_pos : 0 < A := by
    rw [hA_def]; exact log_inv_pos_of_lt_one hp_pos hp_lt_one
  have hA_bounds := log_inv_mem_bounds ha hab hb ⟨ha_p, hb_p⟩
  have hA_lower : Real.log (1 / b) ≤ A := by simpa [hA_def] using hA_bounds.1
  have hA_upper : A ≤ Real.log (1 / a) := by simpa [hA_def] using hA_bounds.2
  have hAmax_pos : 0 < Real.log (1 / a) := log_inv_pos_of_lt_one ha (lt_trans hab hb)
  have hAmin_pos : 0 < Real.log (1 / b) := log_inv_pos_of_lt_one hb_pos hb
  have hlogQ_pos : 0 < Real.log (Q : ℝ) := by
    nlinarith [hLarge.hAmax_le_half_log]
  have hQ_pos_nat : 0 < Q := hLarge.Q_pos
  have hQ_pos_real : (0 : ℝ) < (Q : ℝ) := hLarge.Q_pos_real
  have hlog_div_A_le_quarter : Real.log (Q : ℝ) / A ≤ (Q : ℝ) / 4 := by
    have hden :
        Real.log (Q : ℝ) / A ≤ Real.log (Q : ℝ) / Real.log (1 / b) := by
      apply div_le_div_of_nonneg_left hlogQ_pos.le hAmin_pos hA_lower
    exact le_trans hden hLarge.hlog_over_Amin_le_quarter
  set X : ℝ := ((Q : ℝ) - K - 2) * A / Real.log (Q : ℝ) with hX_def
  let d : ℕ := ⌊X⌋₊
  set Y : ℝ := (d : ℝ) * Real.log (Q : ℝ) / A + K with hY_def
  let L : ℕ := ⌈Y⌉₊
  have hX_nonneg : 0 ≤ X :=
    div_nonneg (mul_nonneg hLarge.nonneg_margin hA_pos.le) hlogQ_pos.le
  have hX_ge_one : 1 ≤ X := by
    have hQ16_real : (16 : ℝ) ≤ Q := hLarge.Q_ge_16_real
    have hmargin : (Q : ℝ) / 2 ≤ (Q : ℝ) - K - 2 := hLarge.half_margin
    have hQ4_pos : 0 < (Q : ℝ) / 4 := by positivity
    have hX_eq : X = ((Q : ℝ) - K - 2) / (Real.log (Q : ℝ) / A) := by
      rw [hX_def]; field_simp
    rw [hX_eq]
    have hden_pos : 0 < Real.log (Q : ℝ) / A := div_pos hlogQ_pos hA_pos
    have hden_le_num : Real.log (Q : ℝ) / A ≤ (Q : ℝ) - K - 2 := by
      have : Real.log (Q : ℝ) / A ≤ (Q : ℝ) / 4 := hlog_div_A_le_quarter
      linarith
    exact (one_le_div hden_pos).mpr hden_le_num
  have hd_pos : 0 < d := natFloor_pos_of_one_le hX_ge_one
  have hd_le_X : (d : ℝ) ≤ X := (natFloor_bounds hX_nonneg).1
  have hX_minus_one_lt_d : X - 1 < (d : ℝ) := (natFloor_bounds hX_nonneg).2
  have hY_nonneg : 0 ≤ Y := by
    rw [hY_def]
    positivity
  have hY_low : Y ≤ (L : ℝ) := (natCeil_bounds hY_nonneg).1
  have hL_high : (L : ℝ) ≤ Y + 1 := le_of_lt (natCeil_bounds hY_nonneg).2
  have hLd : d ≤ L := by
    have hratio_ge_two : 2 ≤ Real.log (Q : ℝ) / A := by
      have hA_le : A ≤ Real.log (Q : ℝ) / 2 :=
        le_trans hA_upper hLarge.hAmax_le_half_log
      rw [le_div_iff₀ hA_pos]; nlinarith
    have hY_ge_d : (d : ℝ) ≤ Y := by
      have h_mul : (d : ℝ) * 2 ≤ (d : ℝ) * Real.log (Q : ℝ) / A := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hratio_ge_two (by positivity)
      rw [hY_def]; linarith [Nat.cast_nonneg (α := ℝ) K]
    exact_mod_cast hY_ge_d.trans hY_low
  have hY_le_Q : Y ≤ (Q : ℝ) := by
    have h_dlog_le : (d : ℝ) * Real.log (Q : ℝ) / A ≤ (Q : ℝ) - K - 2 := by
      have h1 := mul_le_mul_of_nonneg_right hd_le_X hlogQ_pos.le
      rw [hX_def] at h1
      field_simp at h1 ⊢
      nlinarith
    rw [hY_def]; nlinarith
  have hLQ : L ≤ Q := Nat.ceil_le.mpr hY_le_Q
  have hL_ge_halfQ : (Q : ℝ) / 2 ≤ (L : ℝ) := by
    have h_dlog_lower :
        ((Q : ℝ) - K - 2) - Real.log (Q : ℝ) / A <
          (d : ℝ) * Real.log (Q : ℝ) / A := by
      have h1 : X - 1 < (d : ℝ) := hX_minus_one_lt_d
      rw [hX_def] at h1
      have h2 := mul_lt_mul_of_pos_right h1 hlogQ_pos
      field_simp at h2 ⊢
      nlinarith
    have hkmargin : ((2 * K + 4 : ℕ) : ℝ) ≤ (Q : ℝ) := hLarge.Kmargin_real
    push_cast at hkmargin
    have hY_lower : (Q : ℝ) / 2 < Y := by
      rw [hY_def]; linarith [hLarge.Q_ge_16_real, hlog_div_A_le_quarter]
    exact le_of_lt (lt_of_lt_of_le hY_lower hY_low)
  have hlam_bounds :
      p ^ (K + 1) ≤ (Q : ℝ) ^ d * p ^ L ∧
      (Q : ℝ) ^ d * p ^ L ≤ p ^ K :=
    lambda_bounds_of_ceil hQ_pos_real hp_pos hA_def hA_pos hY_low hL_high
  -- Common lower-bound facts shared by `h_first_lower` and `h_inf_lower`:
  have hlam_low : a ^ (K + 1) ≤ (Q : ℝ) ^ d * p ^ L :=
    le_trans (pow_le_pow_left₀ ha.le ha_p (K + 1)) hlam_bounds.1
  have hlam_up : (Q : ℝ) ^ d * p ^ L ≤ b ^ K :=
    le_trans hlam_bounds.2 (pow_le_pow_left₀ hp_pos.le hb_p K)
  have hlam_nonneg : 0 ≤ (Q : ℝ) ^ d * p ^ L :=
    mul_nonneg (pow_nonneg hQ_pos_real.le _) (pow_nonneg hp_pos.le _)
  have hD_pos : 0 < D := by rw [hD]; exact Real.exp_pos _
  have hlamD_small := lam_D_small hlam_up hK_bD hD_pos
  refine ⟨d, L, hd_pos, hLd, hLQ, hp_pos, hp_le_one, ?_, ?_, ?_, ?_⟩
  · -- hD_ineq
    have hx_nonneg : 0 ≤ 1 / p - 1 := by
      have : 1 ≤ 1 / p := by rw [le_div_iff₀ hp_pos]; linarith
      linarith
    have hx_le : 1 / p - 1 ≤ 1 / a - 1 := by
      have h_inv : 1 / p ≤ 1 / a := one_div_le_one_div_of_le ha ha_p
      linarith
    calc (1 + (1 / p - 1) / (Q : ℝ)) ^ L
        ≤ Real.exp (1 / p - 1) :=
          one_plus_div_pow_le_exp hx_nonneg hQ_pos_nat hLQ
      _ ≤ D := by rw [hD]; exact Real.exp_le_exp.mpr hx_le
  · -- h_first_upper: Q^d * p^L ≤ p^K ≤ b^K ≤ 1/3.
    exact hlam_bounds.2.trans ((pow_le_pow_left₀ hp_pos.le hb_p K).trans hK_b)
  · -- h_first_lower
    exact hc_small.trans (quarter_bracket_bound hlam_low hlam_nonneg hlamD_small)
  · -- h_inf_lower
    have hcQ_le : c * (Q : ℝ) ≤ ((1 / 4 : ℝ) * a ^ (K + 1)) * (Q : ℝ) :=
      mul_le_mul_of_nonneg_right hc_small hQ_pos_real.le
    have hhalf := quarter_Q_le_half_L (a := a) (K := K) hL_ge_halfQ (pow_nonneg ha.le _)
    exact hcQ_le.trans (hhalf.trans (mul_le_mul_of_nonneg_left
      (half_bracket_bound hlam_low hlam_nonneg hlamD_small) (by positivity)))

/-- **Pure-arithmetic existence theorem**: there exist `c, K, D > 0` such that
for every prime `Q ≥ K` and every `p ∈ [a, b]`, valid `PolyGraphArithmeticParams`
exist. **Decomposition**: pick concrete `D` and `K`, then apply the per-`Q`
sub-claim `exists_dL_for_polyGraphArithmeticParams`. -/
theorem polyGraphArithmeticParams_exists_uniform
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ (c : ℝ) (K : ℕ) (D : ℝ), 0 < c ∧ 0 < D ∧
    ∀ (Q : ℕ), K ≤ Q →
    ∀ p ∈ Set.Icc a b,
      Nonempty (PolyGraphArithmeticParams Q p c D) := by
  set D : ℝ := Real.exp (1/a - 1) with hD_def
  have hD_pos : 0 < D := Real.exp_pos _
  have hb_pos : (0 : ℝ) < b := lt_trans ha hab
  obtain ⟨K0, hK_bD, hK_b⟩ := exists_K_for_polyGraph_bounds hb_pos hb hD_pos
  set c : ℝ := (1 / 4 : ℝ) * a ^ (K0 + 1) with hc_def
  have hc_pos : 0 < c := by rw [hc_def]; positivity
  obtain ⟨N, hN⟩ := exists_largeQForPolyGraph ha hab hb K0
  refine ⟨c, N, D, hc_pos, hD_pos, ?_⟩
  intros Q hNQ p hp
  have hLarge : LargeQForPolyGraph a b K0 Q := hN Q hNQ
  have hc_small : c ≤ (1 / 4 : ℝ) * a ^ (K0 + 1) := by rw [hc_def]
  exact exists_dL_for_polyGraphArithmeticParams ha hab hb hc_small hD_def hK_bD hK_b hLarge hp

/-- **Parameter-selection existence** (assembled from the arithmetic existence
+ the conversion). For `[a, b] ⊆ (0, 1)`, uniform constants `c, K, D > 0`
exist such that for every prime `Q ≥ K` and every `p ∈ [a, b]`, valid
`PolyGraphGadgetParams` exist. -/
theorem polyGraphParams_exists_uniform
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ (c : ℝ) (K : ℕ) (D : ℝ), 0 < c ∧ 0 < D ∧
    ∀ (Q : ℕ) (_hQp : Fact Q.Prime), K ≤ Q →
    ∀ p ∈ Set.Icc a b,
      Nonempty (@PolyGraphGadgetParams (ZMod Q) (ZMod.instField Q)
        (ZMod.decidableEq Q) (ZMod.fintype Q) p c D) := by
  obtain ⟨c, K, D, hc, hD, hA⟩ := polyGraphArithmeticParams_exists_uniform ha hab hb
  refine ⟨c, K, D, hc, hD, ?_⟩
  intros Q hQp hKQ p hp
  haveI : Fact Q.Prime := hQp
  obtain ⟨A⟩ := hA Q hKQ p hp
  exact arithmeticParams_to_polyGraphParams A

/-- (S3a) **Gadget existence**: provided by the polyGraph DNF construction
for `[a, b] ⊆ (0, 1)`. Closes via the arithmetic parameter-selection theorem
+ the elementary extraction. -/
theorem gadget_exists_for_all_biases {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    GadgetExistsForAllBiases a b := by
  obtain ⟨c, K, D, hc, _hDpos, hparams⟩ :=
    polyGraphParams_exists_uniform ha hab hb
  refine ⟨c, K, hc, ?_⟩
  intros Q hQprime hKQ p hp
  haveI : Fact Q.Prime := hQprime
  obtain ⟨P⟩ := hparams Q hQprime hKQ p hp
  obtain ⟨G, hmono, hs1, hs0, hinf, hprob_low, hprob_up⟩ :=
    gadget_from_polyGraphParams P
  have hcard : (Fintype.card (ZMod Q) : ℝ) = (Q : ℝ) := by rw [ZMod.card]
  refine ⟨G, hmono, ?_, ?_, ?_, hprob_low, hprob_up⟩
  · rw [← hcard]; exact hs1
  · rw [← hcard]; exact hs0
  · rw [← hcard]; exact hinf

/-- A scale-indexed sequence of monotone Boolean functions `H_k` with bounds
in terms of an arbitrary scale function `M : ℕ → ℝ` tending to infinity. -/
structure HQSequence where
  β : ℕ → Type
  fintype : ∀ k, Fintype (β k)
  decEq : ∀ k, DecidableEq (β k)
  H : ∀ k, (β k → Bool) → Bool
  M : ℕ → ℝ
  c : ℝ
  C : ℝ
  hc : 0 < c
  hC : 0 < C
  hM : Filter.Tendsto M Filter.atTop Filter.atTop
  mono : ∀ k, IsMonotone (H k)
  infLower : ∀ᶠ k : ℕ in Filter.atTop, c * (M k) ^ 2 ≤ influence (H k)
  sensUpper : ∀ᶠ k : ℕ in Filter.atTop, (maxSensitivity (H k) : ℝ) ≤ C * (M k) ^ 3
  sensGt : ∀ᶠ k : ℕ in Filter.atTop, 1 < (maxSensitivity (H k) : ℝ)

attribute [instance] HQSequence.fintype HQSequence.decEq

/-- **H_Q sequence existence (scale-indexed)**: avoids needing prime-gap bounds. -/
def HQSequenceExists : Prop := Nonempty HQSequence
/-- A two-gadget pair `(B, T)` over `ZMod Q × ZMod Q` with the bounds needed
to compose `T ∘ B^*` into an `H_Q` realizing the `2/3` exponent. -/
structure TwoGadgetPair (Q : ℕ) [NeZero Q] (cB cT : ℝ) where
  B : ((ZMod Q × ZMod Q) → Bool) → Bool
  T : ((ZMod Q × ZMod Q) → Bool) → Bool
  Bmono : IsMonotone B
  Tmono : IsMonotone T
  Bs1 : (maxSensitivityOne B : ℝ) ≤ (Q : ℝ)
  Bs0 : (maxSensitivityZero B : ℝ) ≤ (Q : ℝ) ^ 2
  Ts1 : (maxSensitivityOne T : ℝ) ≤ (Q : ℝ)
  Ts0 : (maxSensitivityZero T : ℝ) ≤ (Q : ℝ) ^ 2
  Binf : cB * (Q : ℝ) ≤ infP (1 / 2 : ℝ) B
  Tinf : cT * (Q : ℝ) ≤ infP (1 - outputBias B) T

/-- Composed-block bounds for the gadget pair: `Inf(T∘B^*) ≥ cT·cB·Q²` and
`s(T∘B^*) ≤ Q³`. -/
lemma TwoGadgetPair.composed_bounds {Q : ℕ} [NeZero Q] {cB cT : ℝ}
    (P : TwoGadgetPair Q cB cT) (hcB : 0 ≤ cB) (hcT : 0 ≤ cT) :
    cT * cB * (Q : ℝ) ^ 2 ≤ influence (composedBlock P.T P.B) ∧
    (maxSensitivity (composedBlock P.T P.B) : ℝ) ≤ (Q : ℝ) ^ 3 :=
  composedBlock_bounds P.Tmono P.Bmono P.Tinf P.Binf
    P.Ts1 P.Ts0 P.Bs1 P.Bs0 hcT hcB (by positivity)

/-- (S3b.1) **Combined two-gadget existence**: gadget pair `(B_Q, T_Q)` over
the SAME `ZMod Q × ZMod Q`, with B at p=1/2 and T at p = 1 - outputBias B,
both satisfying note2's bounds. -/
def TwoGadgetExistsForPrimes : Prop :=
  ∃ (cB cT : ℝ) (KB KT : ℕ),
    0 < cB ∧ 0 < cT ∧
    ∀ (Q : ℕ) [hQp : Fact Q.Prime], max KB KT ≤ Q →
      haveI : NeZero Q := ⟨hQp.1.pos.ne'⟩
      Nonempty (TwoGadgetPair Q cB cT)

/-- (S3b.1) Provided by applying `gadget_exists_for_all_biases` twice. -/
theorem twoGadgetExistsForPrimes_proof : TwoGadgetExistsForPrimes := by
  classical
  obtain ⟨cB, KB, hcB, hBexists⟩ :=
    gadget_exists_for_all_biases (a := 1/2) (b := 2/3)
      (by norm_num) (by norm_num) (by norm_num)
  set cB' : ℝ := min cB (1/6) with hcB'_def
  have hcB' : 0 < cB' := lt_min hcB (by norm_num)
  have hcB'_le_cB : cB' ≤ cB := min_le_left _ _
  have hcB'_le_sixth : cB' ≤ 1/6 := min_le_right _ _
  obtain ⟨cT, KT, hcT, hTexists⟩ :=
    gadget_exists_for_all_biases (a := 2/3) (b := 1 - cB')
      (by norm_num) (by linarith) (by linarith)
  refine ⟨cB, cT, KB, KT, hcB, hcT, ?_⟩
  intros Q hQp hk
  have hKBk : KB ≤ Q := le_trans (le_max_left _ _) hk
  have hKTk : KT ≤ Q := le_trans (le_max_right _ _) hk
  haveI : NeZero Q := ⟨hQp.1.pos.ne'⟩
  obtain ⟨B, hBmono, hBs1, hBs0, hBinf, hBprob_low, hBprob_up⟩ :=
    hBexists Q hKBk (1/2) ⟨le_refl _, by norm_num⟩
  have h_ob_low : cB ≤ outputBias B := hBprob_low
  have h_ob_up : outputBias B ≤ 1/3 := hBprob_up
  have hq_mem : (1 - outputBias B : ℝ) ∈ Set.Icc (2/3 : ℝ) (1 - cB') :=
    ⟨by linarith, by linarith⟩
  obtain ⟨T, hTmono, hTs1, hTs0, hTinf, _, _⟩ :=
    hTexists Q hKTk (1 - outputBias B) hq_mem
  exact ⟨{ B, T, Bmono := hBmono, Tmono := hTmono,
           Bs1 := hBs1, Bs0 := hBs0, Ts1 := hTs1, Ts0 := hTs0,
           Binf := hBinf, Tinf := hTinf }⟩

/-- (S3b) **H_Q sequence existence**: assemble using `TwoGadgetExistsForPrimes`,
prime sequence, and `composedBlock_bounds`. -/
theorem hQSequenceExists_proof : HQSequenceExists := by
  classical
  obtain ⟨cB, cT, KB, KT, hcB, hcT, h_pair⟩ := twoGadgetExistsForPrimes_proof
  obtain ⟨Qseq, hQprime, hQtop, _hQge⟩ := exists_prime_seq_atTop
  haveI hQp_inst : ∀ k, Fact (Qseq k).Prime := fun k => ⟨hQprime k⟩
  haveI hNZ : ∀ k, NeZero (Qseq k) := fun k => ⟨(hQprime k).pos.ne'⟩
  -- For each k with Qseq k ≥ max KB KT, choose a TwoGadgetPair witness.
  let pair : ∀ k, max KB KT ≤ Qseq k → TwoGadgetPair (Qseq k) cB cT :=
    fun k hk => (h_pair (Qseq k) hk).some
  -- Composed block bounds at each valid k.
  have h_bds : ∀ k (hk : max KB KT ≤ Qseq k),
      cT * cB * (Qseq k : ℝ) ^ 2 ≤ influence (composedBlock (pair k hk).T (pair k hk).B) ∧
      (maxSensitivity (composedBlock (pair k hk).T (pair k hk).B) : ℝ) ≤ (Qseq k : ℝ) ^ 3 :=
    fun k hk => (pair k hk).composed_bounds hcB.le hcT.le
  -- Define H k: composedBlock(T, B) when valid; dummy otherwise.
  let H : ∀ k,
      ((ZMod (Qseq k) × ZMod (Qseq k)) × (ZMod (Qseq k) × ZMod (Qseq k)) → Bool) → Bool :=
    fun k =>
      if hk : max KB KT ≤ Qseq k then composedBlock (pair k hk).T (pair k hk).B
      else fun _ => false
  have hH_eq : ∀ k (hk : max KB KT ≤ Qseq k),
      H k = composedBlock (pair k hk).T (pair k hk).B :=
    fun _ hk => dif_pos hk
  refine ⟨{
    β := fun k => (ZMod (Qseq k) × ZMod (Qseq k)) × (ZMod (Qseq k) × ZMod (Qseq k))
    fintype := fun _ => inferInstance
    decEq := fun _ => inferInstance
    H := H
    M := fun k => (Qseq k : ℝ)
    c := cT * cB
    C := 1
    hc := mul_pos hcT hcB
    hC := by norm_num
    hM := tendsto_natCast_atTop_atTop.comp hQtop
    mono := ?_
    infLower := ?_
    sensUpper := ?_
    sensGt := ?_ }⟩
  · intro k
    by_cases hk : max KB KT ≤ Qseq k
    · rw [hH_eq k hk]; exact (pair k hk).Tmono.compose (pair k hk).Bmono.dual
    · simp only [H, dif_neg hk]; intros _ _ _; rfl
  · filter_upwards [hQtop.eventually_ge_atTop (max KB KT)] with k hk
    rw [hH_eq k hk]
    exact (h_bds k hk).1
  · filter_upwards [hQtop.eventually_ge_atTop (max KB KT)] with k hk
    rw [one_mul, hH_eq k hk]
    exact (h_bds k hk).2
  · have hQ_to_inf : Filter.Tendsto (fun k : ℕ => (Qseq k : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp hQtop
    have h_big : ∀ᶠ k : ℕ in Filter.atTop, 1 < cT * cB * (Qseq k : ℝ) ^ 2 :=
      (Filter.Tendsto.const_mul_atTop (mul_pos hcT hcB)
        ((Filter.tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hQ_to_inf)).eventually_gt_atTop 1
    filter_upwards [hQtop.eventually_ge_atTop (max KB KT), h_big] with k hk h_b
    rw [hH_eq k hk]
    linarith [(h_bds k hk).1,
      influence_le_maxSensitivity (composedBlock (pair k hk).T (pair k hk).B)]

/-- **Scale version**: for `M : ℕ → ℝ` with `M → ∞`,
`log(c·M^a)/log(C·M^b) → a/b`. -/
lemma tendsto_log_ratio_pow_scale {a b : ℕ} {c C : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hC : 0 < C)
    {M : ℕ → ℝ} (hM : Filter.Tendsto M Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun k : ℕ => Real.log (c * (M k) ^ a) / Real.log (C * (M k) ^ b))
      Filter.atTop (nhds ((a : ℝ) / b)) := by
  have h_logM : Filter.Tendsto (fun k : ℕ => Real.log (M k)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hM
  have hM_pos := hM.eventually_gt_atTop 0
  -- Step 1: rewrite log(c · M^a)/log(C · M^b) = (log c + a · log M)/(log C + b · log M).
  have h_log_split : ∀ᶠ k : ℕ in Filter.atTop,
      Real.log (c * (M k) ^ a) / Real.log (C * (M k) ^ b) =
      (Real.log c + (a : ℝ) * Real.log (M k)) /
        (Real.log C + (b : ℝ) * Real.log (M k)) := by
    filter_upwards [hM_pos] with k hMk_pos
    rw [Real.log_mul hc.ne' (pow_pos hMk_pos _).ne',
        Real.log_mul hC.ne' (pow_pos hMk_pos _).ne', Real.log_pow, Real.log_pow]
  -- Step 2: divide numerator and denominator by log M (eventually nonzero).
  have h_alt : ∀ᶠ k : ℕ in Filter.atTop,
      (Real.log c + (a : ℝ) * Real.log (M k)) /
        (Real.log C + (b : ℝ) * Real.log (M k)) =
      (Real.log c / Real.log (M k) + (a : ℝ)) /
        (Real.log C / Real.log (M k) + (b : ℝ)) := by
    filter_upwards [h_logM.eventually_gt_atTop 0] with k h_logM_pos
    field_simp
  rw [Filter.tendsto_congr' h_log_split, Filter.tendsto_congr' h_alt]
  -- Step 3: numerator → 0+a, denominator → 0+b, ratio → a/b.
  have tend_aux : ∀ x : ℝ, ∀ y : ℕ,
      Filter.Tendsto (fun k : ℕ => x / Real.log (M k) + (y : ℝ))
        Filter.atTop (nhds (0 + (y : ℝ))) := fun x y =>
    Filter.Tendsto.add (tendsto_const_nhds.div_atTop h_logM) tendsto_const_nhds
  have h_b_ne : (0 + (b : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < b := by exact_mod_cast hb
    linarith
  convert (tend_aux (Real.log c) a).div (tend_aux (Real.log C) b) h_b_ne using 1
  simp

/-- Analytic core of the scale-bounds theorem: under polynomial scale bounds
`c·M^2 ≤ f` and `s ≤ C·M^3` and `f ≤ s` eventually, the liminf of `log f / log s`
is at least `2/3`. -/
private lemma liminf_log_div_log_ge_of_scale_bounds
    {f s : ℕ → ℝ} {M : ℕ → ℝ} {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hM : Filter.Tendsto M Filter.atTop Filter.atTop)
    (h_f : ∀ᶠ k : ℕ in Filter.atTop, c * (M k) ^ 2 ≤ f k)
    (h_s : ∀ᶠ k : ℕ in Filter.atTop, s k ≤ C * (M k) ^ 3)
    (h_s_gt : ∀ᶠ k : ℕ in Filter.atTop, 1 < s k)
    (h_f_le_s : ∀ᶠ k : ℕ in Filter.atTop, f k ≤ s k) :
    (2 / 3 : ℝ) ≤
      Filter.liminf (fun k => Real.log (f k) / Real.log (s k)) Filter.atTop := by
  have h_cM2_to_inf : Filter.Tendsto (fun k : ℕ => c * (M k) ^ 2) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc ((Filter.tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hM)
  have h_cM2_gt_1 : ∀ᶠ k : ℕ in Filter.atTop, (1 : ℝ) < c * (M k) ^ 2 :=
    h_cM2_to_inf.eventually_gt_atTop 1
  have hM_pos : ∀ᶠ k : ℕ in Filter.atTop, (0 : ℝ) < M k := hM.eventually_gt_atTop 0
  have h_pointwise : ∀ᶠ k : ℕ in Filter.atTop,
      Real.log (c * (M k) ^ 2) / Real.log (C * (M k) ^ 3) ≤
      Real.log (f k) / Real.log (s k) := by
    filter_upwards [h_f, h_s, h_s_gt, h_cM2_gt_1, hM_pos] with k
      h_f_k h_s_k h_s_gt_k h_cM2_gt_1_k hMk_pos
    have h_cMa_pos : (0 : ℝ) < c * (M k) ^ 2 := mul_pos hc (pow_pos hMk_pos _)
    have h_log_cMa_pos : 0 < Real.log (c * (M k) ^ 2) := Real.log_pos h_cM2_gt_1_k
    have h_log_sk_pos : 0 < Real.log (s k) := Real.log_pos h_s_gt_k
    have h_sk_pos : (0 : ℝ) < s k := lt_trans Real.zero_lt_one h_s_gt_k
    calc Real.log (c * (M k) ^ 2) / Real.log (C * (M k) ^ 3)
        ≤ Real.log (c * (M k) ^ 2) / Real.log (s k) :=
          div_le_div_of_nonneg_left h_log_cMa_pos.le h_log_sk_pos
            (Real.log_le_log h_sk_pos h_s_k)
      _ ≤ Real.log (f k) / Real.log (s k) :=
          div_le_div_of_nonneg_right (Real.log_le_log h_cMa_pos h_f_k) h_log_sk_pos.le
  have h_F_le_one : ∀ᶠ k : ℕ in Filter.atTop,
      Real.log (f k) / Real.log (s k) ≤ 1 := by
    filter_upwards [h_s_gt, h_f, h_cM2_gt_1, h_f_le_s] with k h_s_gt_k h_f_k h_cM2_gt_1_k h_fs_k
    have h_cMa_pos : (0 : ℝ) < c * (M k) ^ 2 := lt_trans Real.zero_lt_one h_cM2_gt_1_k
    rw [div_le_one (Real.log_pos h_s_gt_k)]
    exact Real.log_le_log (lt_of_lt_of_le h_cMa_pos h_f_k) h_fs_k
  have h_poly_lim := tendsto_log_ratio_pow_scale (a := 2) (b := 3) (by norm_num) hc hC hM
  rw [show (2 / 3 : ℝ) = ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) from by norm_num,
      ← h_poly_lim.liminf_eq]
  refine Filter.liminf_le_liminf h_pointwise h_poly_lim.isBoundedUnder_ge ⟨1, ?_⟩
  intro L hL
  rw [Filter.eventually_map] at hL
  rcases (hL.and h_F_le_one).exists with ⟨_, hLF, hF1⟩
  exact hLF.trans hF1

/-- (Scale-indexed plugin) **scale-indexed achievability**: a sequence with
bounds `c·M^2 ≤ Inf(H_k)`, `s ≤ C·M^3`, `s > 1`, and `M → ∞` realizes
`TwoThirdsExponentAchievable`. Avoids prime-gap bounds. -/
theorem twoThirdsExponentAchievable_of_scale_bounds
    {β : ℕ → Type} [∀ k, Fintype (β k)] [∀ k, DecidableEq (β k)]
    (H : ∀ k, (β k → Bool) → Bool)
    {M : ℕ → ℝ} {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hM : Filter.Tendsto M Filter.atTop Filter.atTop)
    (h_mono : ∀ k, IsMonotone (H k))
    (h_inf : ∀ᶠ k : ℕ in Filter.atTop, c * (M k) ^ 2 ≤ influence (H k))
    (h_s : ∀ᶠ k : ℕ in Filter.atTop, (maxSensitivity (H k) : ℝ) ≤ C * (M k) ^ 3)
    (h_s_gt : ∀ᶠ k : ℕ in Filter.atTop, 1 < (maxSensitivity (H k) : ℝ)) :
    TwoThirdsExponentAchievable := by
  have h_cM2_to_inf : Filter.Tendsto (fun k : ℕ => c * (M k) ^ 2) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc ((Filter.tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hM)
  refine ⟨{ β, fintype := fun _ => inferInstance, decEq := fun _ => inferInstance, H }, h_mono,
    ?_, ?_⟩
  · rw [Filter.tendsto_atTop_atTop]
    intro N
    rw [← Filter.eventually_atTop]
    filter_upwards [h_cM2_to_inf.eventually_ge_atTop (N : ℝ), h_inf] with k hkN hk_inf
    exact_mod_cast hkN.trans (hk_inf.trans (influence_le_maxSensitivity _))
  · exact liminf_log_div_log_ge_of_scale_bounds hc hC hM h_inf h_s h_s_gt
      (Filter.Eventually.of_forall (fun k => influence_le_maxSensitivity (H k)))

/-- **The main unconditional theorem**: assembled from the H_Q sequence via
the scale-indexed wrapper. -/
theorem twoThirdsExponentAchievable_unconditional : TwoThirdsExponentAchievable := by
  obtain ⟨S⟩ := hQSequenceExists_proof
  exact twoThirdsExponentAchievable_of_scale_bounds S.H S.hc S.hC S.hM S.mono
    S.infLower S.sensUpper S.sensGt

/-- **Achievability summary.** For every `r ≤ 2/3`, the exponent `r` is achievable.
Also, every achievable exponent satisfies the trivial upper bound `r ≤ 1`. -/
theorem achievability_summary :
    (∀ r : ℝ, r ≤ (2 / 3 : ℝ) → ExponentAchievable r) ∧
    (∀ r : ℝ, ExponentAchievable r → r ≤ 1) :=
  ⟨fun _ hr => ExponentAchievable.mono hr twoThirdsExponentAchievable_unconditional,
   fun _ hr => hr.le_one⟩


end InfluenceSensitivity

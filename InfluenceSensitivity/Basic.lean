import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots

set_option linter.style.nativeDecide false
set_option linter.style.whitespace false

/-!
# Influence vs. sensitivity for monotone Boolean functions

Boolean functions are modelled as `(α → Bool) → Bool` for a finite index `α`,
identifying `false ↔ -1` and `true ↔ +1` so that `false < true` matches
`-1 < 1`.
-/

namespace InfluenceSensitivity

/-- The Boolean cube on `α`: functions `α → Bool` represent points of `{0,1}^α`. -/
abbrev Cube (α : Type*) : Type _ := α → Bool

/-- A Boolean function on `Cube α`. -/
abbrev BoolFun (α : Type*) : Type _ := Cube α → Bool

/-- The cardinality of the Boolean cube on a finite type `α` is `2 ^ |α|`. -/
lemma card_cube (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (Cube α) = 2 ^ Fintype.card α := by
  rw [Fintype.card_fun, Fintype.card_bool]

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Flip the `i`-th coordinate of `x`. -/
def flipBit (x : α → Bool) (i : α) : α → Bool :=
  Function.update x i !(x i)

/-- Pointwise sensitivity at `x`: the number of coordinates whose flip
changes `f x`. -/
def sensitivityAt (f : (α → Bool) → Bool) (x : α → Bool) : ℕ :=
  (Finset.univ.filter fun i : α => f x ≠ f (flipBit x i)).card

/-- Maximum (global) sensitivity of `f`. -/
def maxSensitivity (f : (α → Bool) → Bool) : ℕ :=
  Finset.univ.sup (sensitivityAt f)

/-- Sum of pointwise sensitivities over the cube. Equals `2^|α| · influence f`. -/
def totalSensitivity (f : (α → Bool) → Bool) : ℕ :=
  ∑ x : α → Bool, sensitivityAt f x

/-- Total influence of `f` under the uniform measure on `{-1,1}^α`,
equivalently the average pointwise sensitivity. -/
noncomputable def influence (f : (α → Bool) → Bool) : ℝ :=
  (totalSensitivity f : ℝ) / (2 : ℝ) ^ Fintype.card α

/-- Bitwise complement of `x`. -/
def cmpl (x : α → Bool) : α → Bool := fun i => !(x i)

/-- A function is self-dual if complementing the input flips the output. -/
def IsSelfDual (f : (α → Bool) → Bool) : Prop := ∀ x, f (cmpl x) = !(f x)

/-- A Boolean function is monotone if it preserves the pointwise order on
the cube (`false ≤ true`, matching `-1 < 1`). -/
def IsMonotone (f : (α → Bool) → Bool) : Prop :=
  ∀ ⦃x y : α → Bool⦄, x ≤ y → f x ≤ f y

omit [Fintype α] [DecidableEq α] in
/-- **`cmpl` evaluation rule.** -/
@[simp] lemma cmpl_apply (x : α → Bool) (i : α) : cmpl x i = !(x i) := rfl

omit [Fintype α] [DecidableEq α] in
/-- **`cmpl` is involutive.** -/
@[simp] lemma cmpl_cmpl (x : α → Bool) : cmpl (cmpl x) = x := by
  funext i; simp [cmpl]

omit [Fintype α] [DecidableEq α] in
/-- **`cmpl` is injective.** -/
lemma cmpl_injective : Function.Injective (cmpl : (α → Bool) → (α → Bool)) :=
  fun x y h => by rw [← cmpl_cmpl x, h, cmpl_cmpl]

omit [Fintype α] in
/-- **`flipBit` evaluation rule.** -/
lemma flipBit_apply (x : α → Bool) (i j : α) :
    flipBit x i j = if j = i then !(x i) else x j := by
  unfold flipBit
  by_cases h : j = i
  · subst h; simp
  · rw [Function.update_of_ne h, if_neg h]

omit [Fintype α] in
/-- **`flipBit` evaluation at an unflipped coordinate.** -/
lemma flipBit_apply_of_ne (x : α → Bool) {i j : α} (h : j ≠ i) :
    flipBit x i j = x j := by
  rw [flipBit_apply, if_neg h]

omit [Fintype α] in
/-- **`flipBit` is involutive.** -/
@[simp] lemma flipBit_flipBit (x : α → Bool) (i : α) :
    flipBit (flipBit x i) i = x := by
  funext j; simp [flipBit_apply]; by_cases hji : j = i <;> simp [hji]

omit [Fintype α] in
/-- **`flipBit` commutes with `cmpl`.** -/
lemma flipBit_cmpl (x : α → Bool) (i : α) :
    flipBit (cmpl x) i = cmpl (flipBit x i) := by
  funext j; simp [flipBit_apply, cmpl]; by_cases hji : j = i <;> simp [hji]

/-- Bijection `(β → Bool) × (Fin n → β → Bool)` with `Fin (n+1) → β → Bool`. -/
private def consPiEquiv {β : Type*} (n : ℕ) :
    (β × (Fin n → β)) ≃ (Fin (n + 1) → β) where
  toFun bg := Fin.cons bg.1 bg.2
  invFun g := (g 0, fun k => g k.succ)
  left_inv := by
    rintro ⟨b, g⟩
    refine Prod.ext ?_ ?_
    · simp [Fin.cons]
    · funext k; simp [Fin.cons]
  right_inv g := by
    funext k; refine Fin.cases ?_ ?_ k
    · simp [Fin.cons]
    · intro k; simp [Fin.cons]

/-- Sum over `Fin (n+1) → β` splits along the head index. -/
private lemma sum_pi_fin_succ_cons {β : Type*} [Fintype β]
    (n : ℕ) {γ : Type*} [AddCommMonoid γ] (F : (Fin (n + 1) → β) → γ) :
    ∑ g : Fin (n + 1) → β, F g =
    ∑ b : β, ∑ g_rest : Fin n → β, F (Fin.cons b g_rest) := by
  rw [Fintype.sum_equiv (consPiEquiv n).symm F (fun bg => F (Fin.cons bg.1 bg.2)) ?_]
  · exact Fintype.sum_prod_type _
  · intro g_full
    change F g_full = F (Fin.cons (g_full 0) (fun k => g_full k.succ))
    congr 1
    funext k; refine Fin.cases ?_ ?_ k
    · simp [Fin.cons]
    · intro k; simp [Fin.cons]

/-- Bijection between `(Fin (t+1) → Fin m) → Bool` (the cube at depth `t+1`)
and `Fin m → ((Fin t → Fin m) → Bool)` (the m blocks of depth-`t` cubes). -/
private def blockEquiv (m t : ℕ) :
    ((Fin (t + 1) → Fin m) → Bool) ≃ (Fin m → ((Fin t → Fin m) → Bool)) where
  toFun x := fun j p => x (Fin.cons j p)
  invFun g := fun i => g (i 0) (fun k => i k.succ)
  left_inv x := by
    funext i
    change x (Fin.cons (i 0) (fun k => i k.succ)) = x i
    congr 1
    funext k
    refine Fin.cases ?_ ?_ k
    · simp [Fin.cons]
    · intro k; simp [Fin.cons]
  right_inv := by
    rintro g
    funext j p
    change g ((Fin.cons j p : Fin (t + 1) → Fin m) 0)
            (fun k : Fin t => (Fin.cons j p : Fin (t + 1) → Fin m) k.succ) = g j p
    simp [Fin.cons]

/-- Pointwise 1-sensitivity at `x`: the number of coordinates `i` with `x i = true`
whose flip changes `f x` (downward-pivotal). -/
def sensitivityAtOne (f : (α → Bool) → Bool) (x : α → Bool) : ℕ :=
  (Finset.univ.filter fun i : α => x i = true ∧ f x ≠ f (flipBit x i)).card

/-- Pointwise 0-sensitivity at `x`: the number of coordinates `i` with `x i = false`
whose flip changes `f x` (upward-pivotal). -/
def sensitivityAtZero (f : (α → Bool) → Bool) (x : α → Bool) : ℕ :=
  (Finset.univ.filter fun i : α => x i = false ∧ f x ≠ f (flipBit x i)).card

/-- Maximum 1-sensitivity over all 1-inputs. -/
def maxSensitivityOne (f : (α → Bool) → Bool) : ℕ :=
  (Finset.univ.filter (fun x => f x = true)).sup (sensitivityAtOne f)

/-- Maximum 0-sensitivity over all 0-inputs. -/
def maxSensitivityZero (f : (α → Bool) → Bool) : ℕ :=
  (Finset.univ.filter (fun x => f x = false)).sup (sensitivityAtZero f)

/-- The dual of a Boolean function: `dual f x = ¬ f (cmpl x)`. -/
def dual (f : (α → Bool) → Bool) : (α → Bool) → Bool := fun x => !f (cmpl x)

/-- Pointwise sensitivity decomposes by sign of flip. -/
lemma sensitivityAt_eq_zero_add_one (f : (α → Bool) → Bool) (x : α → Bool) :
    sensitivityAt f x = sensitivityAtZero f x + sensitivityAtOne f x := by
  unfold sensitivityAt sensitivityAtZero sensitivityAtOne
  rw [← Finset.card_union_of_disjoint, Finset.filter_union_right]
  · congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases x i <;> tauto
  · rw [Finset.disjoint_filter]
    rintro i _ ⟨hxi, _⟩ ⟨hxi', _⟩
    rw [hxi] at hxi'; simp at hxi'

/-- For a monotone function at a `1`-input, no upward (`0→1`) flip is sensitive. -/
lemma IsMonotone.sensitivityAtZero_eq_zero (hf : IsMonotone f) {x : α → Bool}
    (hx : f x = true) : sensitivityAtZero f x = 0 := by
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  rintro i _ ⟨hxi, hd⟩
  have h_flip_false : f (flipBit x i) = false := by
    cases hcase : f (flipBit x i)
    · rfl
    · exact absurd (hx.trans hcase.symm) hd
  have h_le : x ≤ flipBit x i := fun k => by
    rw [flipBit_apply]; by_cases hk : k = i <;> simp [hk, hxi]
  exact absurd (hf h_le) (by rw [hx, h_flip_false]; decide)

/-- For a monotone function at a `0`-input, no downward (`1→0`) flip is sensitive. -/
lemma IsMonotone.sensitivityAtOne_eq_zero (hf : IsMonotone f) {x : α → Bool}
    (hx : f x = false) : sensitivityAtOne f x = 0 := by
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  rintro i _ ⟨hxi, hd⟩
  have h_flip_true : f (flipBit x i) = true := by
    cases hcase : f (flipBit x i)
    · exact absurd (hx.trans hcase.symm) hd
    · rfl
  have h_le : flipBit x i ≤ x := fun k => by
    rw [flipBit_apply]; by_cases hk : k = i <;> simp [hk, hxi]
  exact absurd (hf h_le) (by rw [hx, h_flip_true]; decide)

/-- For monotone `f`, the global max sensitivity is the max of one-sided maxima. -/
lemma IsMonotone.maxSensitivity_eq_max {f : (α → Bool) → Bool} (hf : IsMonotone f) :
    maxSensitivity f = max (maxSensitivityZero f) (maxSensitivityOne f) := by
  apply le_antisymm
  · refine Finset.sup_le ?_
    intros x _
    cases hfx : f x with
    | false =>
      have hsens : sensitivityAt f x = sensitivityAtZero f x := by
        rw [sensitivityAt_eq_zero_add_one, hf.sensitivityAtOne_eq_zero hfx, Nat.add_zero]
      rw [hsens]
      apply le_max_of_le_left
      unfold maxSensitivityZero
      exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hfx⟩)
    | true =>
      have hsens : sensitivityAt f x = sensitivityAtOne f x := by
        rw [sensitivityAt_eq_zero_add_one, hf.sensitivityAtZero_eq_zero hfx, Nat.zero_add]
      rw [hsens]
      apply le_max_of_le_right
      unfold maxSensitivityOne
      exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hfx⟩)
  · refine max_le ?_ ?_ <;>
    · refine Finset.sup_le fun x _ => ?_
      refine LE.le.trans ?_ (Finset.le_sup (Finset.mem_univ x))
      rw [sensitivityAt_eq_zero_add_one]; omega

omit [Fintype α] [DecidableEq α] in
/-- Dual is involutive. -/
@[simp] lemma dual_dual (f : (α → Bool) → Bool) : dual (dual f) = f := by
  funext x
  simp [dual, cmpl_cmpl]

omit [Fintype α] [DecidableEq α] in
/-- Duality preserves monotonicity. -/
lemma IsMonotone.dual {f : (α → Bool) → Bool} (hf : IsMonotone f) :
    IsMonotone (InfluenceSensitivity.dual f) := by
  intros x y hxy
  have hcmpl : cmpl y ≤ cmpl x := fun i => by
    have := hxy i
    cases hxi : x i <;> cases hyi : y i <;> simp_all [cmpl]
  have hfle : f (cmpl y) ≤ f (cmpl x) := hf hcmpl
  unfold InfluenceSensitivity.dual
  cases hcx : f (cmpl x) <;> cases hcy : f (cmpl y) <;> simp_all

/-- Sensitivity at the dual of a complemented input swaps `s_1`/`s_0`. -/
lemma sensitivityAtOne_dual_cmpl (f : (α → Bool) → Bool) (y : α → Bool) :
    sensitivityAtOne (InfluenceSensitivity.dual f) (cmpl y) = sensitivityAtZero f y := by
  unfold sensitivityAtOne sensitivityAtZero InfluenceSensitivity.dual
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, cmpl_apply,
    flipBit_cmpl, cmpl_cmpl]
  cases hyi : y i <;> cases hfy : f y <;>
    cases hfx : f (flipBit y i) <;> simp_all

/-- Duality swaps `maxSensitivityOne` and `maxSensitivityZero`. -/
lemma maxSensitivityOne_dual (f : (α → Bool) → Bool) :
    maxSensitivityOne (InfluenceSensitivity.dual f) = maxSensitivityZero f := by
  unfold maxSensitivityOne maxSensitivityZero
  have h_filter_eq :
      Finset.univ.filter (fun x : α → Bool => InfluenceSensitivity.dual f x = true) =
      (Finset.univ.filter (fun y : α → Bool => f y = false)).image cmpl := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    refine ⟨fun hx => ⟨cmpl x, ?_, cmpl_cmpl x⟩, ?_⟩
    · unfold InfluenceSensitivity.dual at hx
      cases hfx : f (cmpl x) <;> simp [hfx] at hx ⊢
    · rintro ⟨y, hy, rfl⟩
      unfold InfluenceSensitivity.dual
      rw [cmpl_cmpl]
      cases hfy : f y <;> simp [hfy] at hy ⊢
  rw [h_filter_eq, Finset.sup_image]
  apply Finset.sup_congr rfl
  intros y _
  exact sensitivityAtOne_dual_cmpl f y

/-- Duality swaps `maxSensitivityZero` and `maxSensitivityOne`. -/
lemma maxSensitivityZero_dual (f : (α → Bool) → Bool) :
    maxSensitivityZero (InfluenceSensitivity.dual f) = maxSensitivityOne f := by
  have h := maxSensitivityOne_dual (InfluenceSensitivity.dual f)
  rw [dual_dual] at h
  exact h.symm

omit [Fintype α] [DecidableEq α] in
/-- A self-dual function equals its own dual. -/
lemma IsSelfDual.dual_eq {f : (α → Bool) → Bool} (hsd : IsSelfDual f) :
    InfluenceSensitivity.dual f = f := by
  funext x
  unfold InfluenceSensitivity.dual
  rw [hsd]
  simp

/-- The `i`-th block of an input `x : (β × α) → Bool`. -/
def compBlock {α β : Type*} (i : β) (x : (β × α) → Bool) : α → Bool :=
  fun j => x (i, j)

/-- **`compBlock` evaluation rule.** -/
@[simp] lemma compBlock_apply {α β : Type*} (i : β)
    (x : (β × α) → Bool) (j : α) : compBlock i x j = x (i, j) := rfl

/-- Block composition `F ∘ G`: replace each input of `F` with an independent
copy of `G`. The result is a function on `β × α → Bool`. -/
def compose {α β : Type*} (F : (β → Bool) → Bool) (G : (α → Bool) → Bool) :
    ((β × α) → Bool) → Bool :=
  fun x => F (fun i => G (compBlock i x))

/-- Block composition preserves monotonicity. -/
lemma IsMonotone.compose {α β : Type*}
    {F : (β → Bool) → Bool} {G : (α → Bool) → Bool}
    (hF : IsMonotone F) (hG : IsMonotone G) :
    IsMonotone (InfluenceSensitivity.compose F G) := by
  intros x y hxy
  apply hF
  intro i
  apply hG
  intro j
  exact hxy (i, j)

/-- Block of a flipped input: flipping `x` at `(i₀, j₀)` changes only block `i₀`. -/
lemma compBlock_flipBit_self {α β : Type*} [DecidableEq α] [DecidableEq β]
    (x : (β × α) → Bool) (i₀ : β) (j₀ : α) :
    compBlock i₀ (flipBit x (i₀, j₀)) = flipBit (compBlock i₀ x) j₀ := by
  funext j
  unfold compBlock flipBit
  by_cases hj : j = j₀
  · subst hj; simp
  · have hpne : ((i₀, j) : β × α) ≠ (i₀, j₀) := by simp [hj]
    rw [Function.update_of_ne hpne, Function.update_of_ne hj]

lemma compBlock_flipBit_other {α β : Type*} [DecidableEq α] [DecidableEq β]
    (x : (β × α) → Bool) (i₀ i : β) (j₀ : α) (hi : i ≠ i₀) :
    compBlock i (flipBit x (i₀, j₀)) = compBlock i x := by
  funext j
  unfold compBlock flipBit
  have hpne : ((i, j) : β × α) ≠ (i₀, j₀) := by simp [hi]
  rw [Function.update_of_ne hpne]

/-- Block of a complemented input equals the complement of the block. -/
lemma compBlock_cmpl {α β : Type*} (x : (β × α) → Bool) (i : β) :
    compBlock i (cmpl x) = cmpl (compBlock i x) := by
  funext j
  rfl

/-- Duality distributes over composition: `(F ∘ G)^† = F^† ∘ G^†`. -/
lemma dual_compose {α β : Type*} (F : (β → Bool) → Bool) (G : (α → Bool) → Bool) :
    InfluenceSensitivity.dual (InfluenceSensitivity.compose F G) =
    InfluenceSensitivity.compose (InfluenceSensitivity.dual F)
      (InfluenceSensitivity.dual G) := by
  funext x
  unfold InfluenceSensitivity.dual InfluenceSensitivity.compose
  congr 1
  congr 1
  funext i
  rw [compBlock_cmpl]
  unfold cmpl
  simp

/-- After flipping `x` at `(i, j)`, the composition equals `F` applied to the
child-output vector with index `i` updated to `G (flipBit (compBlock i x) j)`. -/
lemma compose_flipBit_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : (β → Bool) → Bool) (G : (α → Bool) → Bool)
    (x : (β × α) → Bool) (i : β) (j : α) :
    InfluenceSensitivity.compose F G (flipBit x (i, j)) =
    F (Function.update (fun k => G (compBlock k x)) i
        (G (flipBit (compBlock i x) j))) := by
  unfold InfluenceSensitivity.compose
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk
    rw [compBlock_flipBit_self, Function.update_self]
  · rw [compBlock_flipBit_other _ _ _ _ hk, Function.update_of_ne hk]

/-- **Pointwise sensitivity decomposition of compose.** For any `x`, the count
of 1-sensitive coordinates in `F ∘ G` factors over the block index. -/
lemma sensitivityAtOne_compose {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (F : (β → Bool) → Bool) (G : (α → Bool) → Bool) (x : (β × α) → Bool) :
    sensitivityAtOne (InfluenceSensitivity.compose F G) x =
    ∑ i : β, (if F (fun k => G (compBlock k x)) ≠
              F (flipBit (fun k => G (compBlock k x)) i) then (1:ℕ) else 0) *
              sensitivityAtOne G (compBlock i x) := by
  unfold sensitivityAtOne
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show InfluenceSensitivity.compose F G x = F (fun k => G (compBlock k x)) from rfl]
  rw [compose_flipBit_eq]
  set y : β → Bool := fun k => G (compBlock k x) with hy_def
  cases hxij : x (i, j) with
  | false =>
    simp [hxij]
  | true =>
    by_cases h_G_change : G (compBlock i x) = G (flipBit (compBlock i x) j)
    · have h_update_eq : Function.update y i (G (flipBit (compBlock i x) j)) = y := by
        rw [show G (flipBit (compBlock i x) j) = y i from h_G_change.symm,
          Function.update_eq_self]
      rw [h_update_eq]
      simp [hxij, h_G_change]
    · have h_update_eq : Function.update y i (G (flipBit (compBlock i x) j)) =
                          flipBit y i := by
        show Function.update y i _ = Function.update y i !(y i)
        congr 1
        cases hy : G (compBlock i x) <;>
          cases hz : G (flipBit (compBlock i x) j) <;> simp_all
      rw [h_update_eq]
      simp [hxij, h_G_change]

/-- For monotone `F` at a `1`-input `top`, the indicator `F top ≠ F (flipBit top i)`
forces `top i = true`. -/
lemma IsMonotone.flip_change_at_one
    {β : Type*} [DecidableEq β]
    {F : (β → Bool) → Bool} (hF : IsMonotone F) {top : β → Bool}
    (hFtop : F top = true) {i : β} (hch : F top ≠ F (flipBit top i)) :
    top i = true := by
  have hFflip : F (flipBit top i) = false := by
    cases hcase : F (flipBit top i)
    · rfl
    · exact absurd (hFtop.trans hcase.symm) hch
  cases htopi : top i
  · -- top i = false: flipBit makes it true → flipBit top i ≥ top → F flip ≥ F top
    have h_le : top ≤ flipBit top i := fun k => by
      rw [flipBit_apply]; by_cases hk : k = i <;> simp [hk, htopi]
    have h_fle : F top ≤ F (flipBit top i) := hF h_le
    rw [hFtop, hFflip] at h_fle
    exact absurd h_fle (by decide)
  · rfl

/-- **Block composition: upper bound for `s_1`.** For monotone `F`, `G`,
`s_1(F ∘ G) ≤ s_1(F) · s_1(G)`. -/
lemma maxSensitivityOne_compose_le {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {F : (β → Bool) → Bool} {G : (α → Bool) → Bool}
    (hF : IsMonotone F) (_hG : IsMonotone G) :
    maxSensitivityOne (InfluenceSensitivity.compose F G) ≤
    maxSensitivityOne F * maxSensitivityOne G := by
  unfold maxSensitivityOne
  refine Finset.sup_le ?_
  intros x hx
  obtain ⟨_, hFGx⟩ := Finset.mem_filter.mp hx
  rw [sensitivityAtOne_compose]
  set top : β → Bool := fun k => G (compBlock k x)
  have hFtop : F top = true := hFGx
  -- Each summand is `ind · sensitivityAtOne G(...) ≤ ind · maxSensitivityOne G`.
  have h_inner : ∀ i : β,
      (if F top ≠ F (flipBit top i) then (1:ℕ) else 0) * sensitivityAtOne G (compBlock i x) ≤
      (if F top ≠ F (flipBit top i) then (1:ℕ) else 0) * maxSensitivityOne G := fun i => by
    by_cases hch : F top ≠ F (flipBit top i)
    · rw [if_pos hch, one_mul, one_mul]
      exact Finset.le_sup (f := sensitivityAtOne G) (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hF.flip_change_at_one hFtop hch⟩)
    · rw [if_neg hch, zero_mul, zero_mul]
  -- The sum of indicators is `sensitivityAtOne F top` because monotone forces `top i = true`.
  have h_indicator_eq :
      (∑ i : β, (if F top ≠ F (flipBit top i) then (1:ℕ) else 0)) = sensitivityAtOne F top := by
    rw [sensitivityAtOne, Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hch : F top ≠ F (flipBit top i)
    · simp [hF.flip_change_at_one hFtop hch, hch]
    · simp [hch]
  calc ∑ i : β, (if F top ≠ F (flipBit top i) then (1:ℕ) else 0) *
                sensitivityAtOne G (compBlock i x)
      ≤ ∑ i : β, (if F top ≠ F (flipBit top i) then (1:ℕ) else 0) * maxSensitivityOne G :=
        Finset.sum_le_sum (fun i _ => h_inner i)
    _ = sensitivityAtOne F top * maxSensitivityOne G := by
        rw [← Finset.sum_mul, h_indicator_eq]
    _ ≤ maxSensitivityOne F * maxSensitivityOne G :=
        Nat.mul_le_mul_right _ <|
          Finset.le_sup (f := sensitivityAtOne F)
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFtop⟩)

/-- **Block composition: lower bound for `s_1` (witness construction).**
Given a 1-input `y` of `F` and witnesses `z₁ : α → Bool` (1-input of `G`)
and `z₀ : α → Bool` (0-input of `G`), build `x = z(y(·))` and bound
`s_1(F ∘ G)` from below by `(s_1 F y) · (s_1 G z₁)`. -/
lemma le_maxSensitivityOne_compose_witness
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (F : (β → Bool) → Bool) (G : (α → Bool) → Bool)
    {y : β → Bool} (hFy : F y = true)
    {z₁ : α → Bool} (hGz1 : G z₁ = true)
    {z₀ : α → Bool} (hGz0 : G z₀ = false) :
    sensitivityAtOne F y * sensitivityAtOne G z₁ ≤
    maxSensitivityOne (InfluenceSensitivity.compose F G) := by
  let x : (β × α) → Bool := fun p => if y p.1 = true then z₁ p.2 else z₀ p.2
  have hcompBlock : ∀ i : β,
      compBlock i x = (fun j => if y i = true then z₁ j else z₀ j) := by
    intro i; funext j; rfl
  have hcompBlock_true : ∀ i : β, y i = true → compBlock i x = z₁ := by
    intros i hi; funext j; simp [compBlock, x, hi]
  have hcompBlock_false : ∀ i : β, y i = false → compBlock i x = z₀ := by
    intros i hi; funext j; simp [compBlock, x, hi]
  have htop : (fun k => G (compBlock k x)) = y := by
    funext i; cases hyi : y i
    · rw [hcompBlock_false i hyi, hGz0]
    · rw [hcompBlock_true i hyi, hGz1]
  have hFGx : InfluenceSensitivity.compose F G x = true := by
    unfold InfluenceSensitivity.compose; rw [htop]; exact hFy
  -- Pointwise lower bound: drop terms where y i = false
  have h_le : sensitivityAtOne F y * sensitivityAtOne G z₁ ≤
              sensitivityAtOne (InfluenceSensitivity.compose F G) x := by
    rw [sensitivityAtOne_compose, htop]
    -- the sum = ∑ i, (if F y ≠ F flipBit y i then 1 else 0) · sensAtOne G (compBlock i x)
    have h_split :
        sensitivityAtOne F y * sensitivityAtOne G z₁ =
        ∑ i : β, (if y i = true ∧ F y ≠ F (flipBit y i) then (1 : ℕ) else 0) *
                  sensitivityAtOne G z₁ := by
      unfold sensitivityAtOne
      rw [Finset.card_filter, Finset.sum_mul]
    rw [h_split]
    refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases hyi : y i = true
    · rw [hcompBlock_true i hyi]
      by_cases hch : F y ≠ F (flipBit y i)
      · simp [hyi, hch]
      · simp [hch]
    · simp [hyi]
  exact h_le.trans (Finset.le_sup (f := sensitivityAtOne (InfluenceSensitivity.compose F G))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFGx⟩))

/-- **Multiplicativity of `s_1` for monotone composition.** -/
lemma maxSensitivityOne_compose {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {F : (β → Bool) → Bool} {G : (α → Bool) → Bool}
    (hF : IsMonotone F) (hG : IsMonotone G) :
    maxSensitivityOne (InfluenceSensitivity.compose F G) =
    maxSensitivityOne F * maxSensitivityOne G := by
  refine le_antisymm (maxSensitivityOne_compose_le hF hG) ?_
  by_cases hF_zero : maxSensitivityOne F = 0
  · simp [hF_zero]
  by_cases hG_zero : maxSensitivityOne G = 0
  · simp [hG_zero]
  -- Both nonzero ⇒ filters nonempty ⇒ pick witnesses
  have hF_ne : (Finset.univ.filter (fun x : β → Bool => F x = true)).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun h =>
      hF_zero (by unfold maxSensitivityOne; rw [h]; rfl)
  have hG_ne : (Finset.univ.filter (fun x : α → Bool => G x = true)).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun h =>
      hG_zero (by unfold maxSensitivityOne; rw [h]; rfl)
  obtain ⟨y, hy_in, hy_eq⟩ := Finset.exists_mem_eq_sup _ hF_ne (sensitivityAtOne F)
  obtain ⟨_, hFy⟩ := Finset.mem_filter.mp hy_in
  obtain ⟨z₁, hz1_in, hz1_eq⟩ := Finset.exists_mem_eq_sup _ hG_ne (sensitivityAtOne G)
  obtain ⟨_, hGz1⟩ := Finset.mem_filter.mp hz1_in
  -- maxSens G > 0 ⇒ sensAtOne G z₁ > 0 ⇒ ∃ j with G changes at z₁
  have h_inner_pos : 0 < sensitivityAtOne G z₁ :=
    hz1_eq.symm ▸ Nat.pos_of_ne_zero hG_zero
  rw [sensitivityAtOne, Finset.card_pos] at h_inner_pos
  obtain ⟨j, hj⟩ := h_inner_pos
  obtain ⟨_, _, hG_change⟩ := Finset.mem_filter.mp hj
  have hGz0 : G (flipBit z₁ j) = false := by
    cases hG_z0 : G (flipBit z₁ j)
    · rfl
    · exact absurd (hGz1.trans hG_z0.symm) hG_change
  calc maxSensitivityOne F * maxSensitivityOne G
      = sensitivityAtOne F y * sensitivityAtOne G z₁ := by
        unfold maxSensitivityOne; rw [hy_eq, hz1_eq]
    _ ≤ maxSensitivityOne (InfluenceSensitivity.compose F G) :=
        le_maxSensitivityOne_compose_witness F G hFy hGz1 hGz0

/-- **Multiplicativity of `s_0` for monotone composition.**
By duality from `s_1`. -/
lemma maxSensitivityZero_compose {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {F : (β → Bool) → Bool} {G : (α → Bool) → Bool}
    (hF : IsMonotone F) (hG : IsMonotone G) :
    maxSensitivityZero (InfluenceSensitivity.compose F G) =
    maxSensitivityZero F * maxSensitivityZero G := by
  have h := maxSensitivityOne_compose hF.dual hG.dual
  rw [← dual_compose] at h
  rw [maxSensitivityOne_dual, maxSensitivityOne_dual, maxSensitivityOne_dual] at h
  exact h

/-- **Total max-sensitivity of a monotone composition.** Combines the one-sided
multiplicativity formulas: `s(F∘G) = max(s_0(F)·s_0(G), s_1(F)·s_1(G))`. -/
lemma maxSensitivity_compose {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {F : (β → Bool) → Bool} {G : (α → Bool) → Bool}
    (hF : IsMonotone F) (hG : IsMonotone G) :
    maxSensitivity (InfluenceSensitivity.compose F G) =
    max (maxSensitivityZero F * maxSensitivityZero G)
        (maxSensitivityOne F * maxSensitivityOne G) := by
  rw [(hF.compose hG).maxSensitivity_eq_max,
      maxSensitivityZero_compose hF hG, maxSensitivityOne_compose hF hG]

/-- **Pointwise full sensitivity decomposition of compose.** For any input `x`,
the sensitivity at `x` of `F ∘ G` factors as a sum over the block index `i`
of (whether `F` changes at coord `i` in the top vector) times (the sensitivity
of `G` at the `i`-th block). This is the building block for influence
multiplicativity. -/
lemma sensitivityAt_compose {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (F : (β → Bool) → Bool) (G : (α → Bool) → Bool) (x : (β × α) → Bool) :
    sensitivityAt (InfluenceSensitivity.compose F G) x =
    ∑ i : β, (if F (fun k => G (compBlock k x)) ≠
              F (flipBit (fun k => G (compBlock k x)) i) then (1:ℕ) else 0) *
              sensitivityAt G (compBlock i x) := by
  unfold sensitivityAt
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show InfluenceSensitivity.compose F G x = F (fun k => G (compBlock k x)) from rfl]
  rw [compose_flipBit_eq]
  set y : β → Bool := fun k => G (compBlock k x) with hy_def
  by_cases h_G_change : G (compBlock i x) = G (flipBit (compBlock i x) j)
  · -- G doesn't change → top doesn't change → F doesn't change
    have h_update_eq : Function.update y i (G (flipBit (compBlock i x) j)) = y := by
      rw [show G (flipBit (compBlock i x) j) = y i from h_G_change.symm,
        Function.update_eq_self]
    rw [h_update_eq]
    simp [h_G_change]
  · -- G changes → top toggles at i, F change indicator survives
    have h_update_eq : Function.update y i (G (flipBit (compBlock i x) j)) = flipBit y i := by
      show Function.update y i _ = Function.update y i !(y i)
      congr 1
      cases hy : G (compBlock i x) <;>
        cases hz : G (flipBit (compBlock i x) j) <;> simp_all
    rw [h_update_eq]
    simp [h_G_change]

/-- **Total sensitivity of a composition, re-indexed.** Sum the pointwise
decomposition over `x : (β × α) → Bool` and re-index via currying
`(β × α → Bool) ≃ β → (α → Bool)`. This is the integer-form bookkeeping
identity feeding into influence multiplicativity. -/
lemma totalSensitivity_compose_eq_sum {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (F : (β → Bool) → Bool) (G : (α → Bool) → Bool) :
    totalSensitivity (InfluenceSensitivity.compose F G) =
    ∑ g : β → (α → Bool), ∑ i : β,
      (if F (fun k => G (g k)) ≠ F (flipBit (fun k => G (g k)) i) then (1:ℕ) else 0) *
      sensitivityAt G (g i) := by
  unfold totalSensitivity
  simp_rw [sensitivityAt_compose F G]
  -- Re-index x ≃ g via currying
  refine Fintype.sum_equiv (Equiv.curry β α Bool) _ _ (fun x => ?_)
  rfl

/-- **Self-duality is preserved under composition.** If both `F` and `G` are
self-dual, so is `F ∘ G`. -/
lemma IsSelfDual.compose {α β : Type*}
    {F : (β → Bool) → Bool} (hF : IsSelfDual F)
    {G : (α → Bool) → Bool} (hG : IsSelfDual G) :
    IsSelfDual (InfluenceSensitivity.compose F G) := by
  intro x
  unfold InfluenceSensitivity.compose
  have h_inner : (fun k => G (compBlock k (cmpl x))) =
                 cmpl (fun k => G (compBlock k x)) := by
    funext k; rw [compBlock_cmpl, hG (compBlock k x)]; rfl
  rw [h_inner, hF]

/-- **Weighted total sensitivity** of `F` with `Bool`-indexed nonneg weights.
The factor `∏_k w (t_k)` weights each input vector `t : β → Bool`. Setting
`w = fun _ => 1` recovers `totalSensitivity` (after the inner sum-over-i
swap). Setting `w(b) = (number of `α → Bool` mapping to `b` under some `G`)`
gives the combinatorial form of q-biased total sensitivity, where
`q = w(true) / (w(true) + w(false))`. -/
def weightedTotalSensitivity {β : Type*} [Fintype β] [DecidableEq β]
    (F : (β → Bool) → Bool) (w : Bool → ℕ) : ℕ :=
  ∑ i : β, ∑ t : β → Bool,
    (∏ k : β, w (t k)) * (if F t ≠ F (flipBit t i) then (1 : ℕ) else 0)

/-- **Sensitivity at a point under dual.** For any `f`,
`sensitivityAt (dual f) x = sensitivityAt f (cmpl x)`. The cmpl-bijection
between input space and itself preserves sensitivity by duality. -/
lemma sensitivityAt_dual {α : Type*} [Fintype α] [DecidableEq α]
    (f : (α → Bool) → Bool) (x : α → Bool) :
    sensitivityAt (InfluenceSensitivity.dual f) x = sensitivityAt f (cmpl x) := by
  unfold sensitivityAt
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold InfluenceSensitivity.dual
  rw [flipBit_cmpl]
  cases hf1 : f (cmpl x) <;> cases hf2 : f (flipBit (cmpl x) i) <;> simp_all

/-- **Total sensitivity is preserved by duality.** `totalSens(dual f) = totalSens f`. -/
lemma totalSensitivity_dual {α : Type*} [Fintype α] [DecidableEq α]
    (f : (α → Bool) → Bool) :
    totalSensitivity (InfluenceSensitivity.dual f) = totalSensitivity f := by
  unfold totalSensitivity
  simp_rw [sensitivityAt_dual]
  exact Fintype.sum_equiv ⟨cmpl, cmpl, cmpl_cmpl, cmpl_cmpl⟩ _ _ fun _ => rfl

/-- **Influence is preserved by duality.** `influence(dual f) = influence f`. -/
lemma influence_dual {α : Type*} [Fintype α] [DecidableEq α]
    (f : (α → Bool) → Bool) :
    influence (InfluenceSensitivity.dual f) = influence f := by
  unfold influence
  rw [totalSensitivity_dual]

/-- The "F changes at coord i" indicator is invariant under flipping coord `i`.
This invariance is essential for factoring sums over `g : β → α → Bool` in
the general (non-self-dual) compose total-sensitivity formula. -/
lemma change_indicator_flipBit_self {β : Type*} [DecidableEq β]
    (F : (β → Bool) → Bool) (i : β) (t : β → Bool) :
    (if F (flipBit t i) ≠ F (flipBit (flipBit t i) i) then (1 : ℕ) else 0) =
      (if F t ≠ F (flipBit t i) then (1 : ℕ) else 0) := by
  rw [flipBit_flipBit]
  congr 1
  exact propext ne_comm

/-- The "F changes at coord i" indicator does not depend on the value of `t i`.
For any `b : Bool`, replacing `t i` with `b` leaves the indicator unchanged. -/
lemma change_indicator_update_self {β : Type*} [DecidableEq β]
    (F : (β → Bool) → Bool) (i : β) (t : β → Bool) (b : Bool) :
    (if F (Function.update t i b) ≠
          F (flipBit (Function.update t i b) i) then (1 : ℕ) else 0) =
      (if F t ≠ F (flipBit t i) then (1 : ℕ) else 0) := by
  by_cases h : b = t i
  · rw [h, Function.update_eq_self]
  · have hb : b = !(t i) := by
      cases ht : t i <;> cases hb' : b <;> simp_all
    rw [show Function.update t i b = flipBit t i from by rw [hb]; rfl]
    exact change_indicator_flipBit_self F i t

/-- **Sum splitting at a coordinate.** Sums over `β → Bool` split into
sums over `Bool × ({j // j ≠ i} → Bool)` via the `funSplitAt` equiv. -/
lemma sum_pi_split_at {β : Type*} [Fintype β] [DecidableEq β]
    {γ : Type*} [AddCommMonoid γ] (i : β) (f : (β → Bool) → γ) :
    ∑ t : β → Bool, f t =
      ∑ b : Bool, ∑ t_other : { j : β // j ≠ i } → Bool,
        f ((Equiv.funSplitAt i Bool).symm (b, t_other)) := by
  rw [show (∑ t : β → Bool, f t) =
        ∑ p : Bool × ({ j : β // j ≠ i } → Bool),
          f ((Equiv.funSplitAt i Bool).symm p) from
        Fintype.sum_equiv (Equiv.funSplitAt i Bool) _ _ (fun t => by
          rw [Equiv.symm_apply_apply])]
  rw [Fintype.sum_prod_type]

/-- **Sum splitting at a coordinate, general codomain.** Sums over functions
`β → α` split into sums over `α × ({j // j ≠ i} → α)` via `funSplitAt`. -/
lemma sum_pi_split_at_general {β : Type*} [Fintype β] [DecidableEq β]
    {α : Type*} [Fintype α]
    {γ : Type*} [AddCommMonoid γ] (i : β) (f : (β → α) → γ) :
    ∑ t : β → α, f t =
      ∑ b : α, ∑ t_other : { j : β // j ≠ i } → α,
        f ((Equiv.funSplitAt i α).symm (b, t_other)) := by
  rw [show (∑ t : β → α, f t) =
        ∑ p : α × ({ j : β // j ≠ i } → α),
          f ((Equiv.funSplitAt i α).symm p) from
        Fintype.sum_equiv (Equiv.funSplitAt i α) _ _ (fun t => by
          rw [Equiv.symm_apply_apply])]
  rw [Fintype.sum_prod_type]

/-- The number of `g : β → α → Bool` mapping under `G` componentwise to a given
target `t : β → Bool` equals the product over `k` of the preimage cardinalities
`|{x : α → Bool // G x = t k}|`. -/
lemma card_preimage_compose_eq {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (G : (α → Bool) → Bool) (t : β → Bool) :
    ((Finset.univ : Finset (β → α → Bool)).filter
        (fun g => (fun k => G (g k)) = t)).card =
    ∏ k : β, (Finset.univ.filter (fun x : α → Bool => G x = t k)).card := by
  rw [show (Finset.univ : Finset (β → α → Bool)).filter
            (fun g => (fun k => G (g k)) = t) =
            Fintype.piFinset (fun k : β =>
              (Finset.univ : Finset (α → Bool)).filter (fun x => G x = t k)) from ?_]
  · exact Fintype.card_piFinset _
  · ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hg k; exact congrFun hg k
    · intro hg; funext k; exact hg k

/-- **Pushforward sum identity.** For `h : (β → Bool) → ℕ`, summing
`h(G ∘ g)` over all `g : β → α → Bool` equals summing over `t : β → Bool`
weighted by the number of preimages: `(∏_k |G^{-1}(t k)|) · h t`. -/
lemma sum_compose_G {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (G : (α → Bool) → Bool) (h : (β → Bool) → ℕ) :
    ∑ g : β → α → Bool, h (fun k => G (g k)) =
    ∑ t : β → Bool,
      (∏ k : β, (Finset.univ.filter (fun x : α → Bool => G x = t k)).card) * h t := by
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (β → α → Bool))
        (fun g : β → α → Bool => fun k => G (g k))
        (fun g => h (fun k => G (g k)))]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  -- ∑ g ∈ Finset.univ with (fun k => G (g k)) = t, h (fun k => G (g k))
  --   = card · h t = (∏_k N_{t k}) · h t.
  have h_inner_eq : ∀ g ∈ Finset.univ.filter
      (fun g : β → α → Bool => (fun k => G (g k)) = t),
      h (fun k => G (g k)) = h t := fun g hg => by
    rw [Finset.mem_filter] at hg
    rw [hg.2]
  rw [Finset.sum_congr rfl h_inner_eq, Finset.sum_const, smul_eq_mul,
      card_preimage_compose_eq]

/-- **Naturality of `funSplitAt` under `G`.** Composing `G` with the
reconstructed function from `(g_i, g_other)` equals reconstructing
`(G g_i, k ↦ G (g_other k))` directly. -/
lemma compose_G_funSplitAt {α β : Type*} [DecidableEq β]
    (G : (α → Bool) → Bool) (i : β) (g_i : α → Bool)
    (g_other : { j : β // j ≠ i } → α → Bool) :
    (fun k : β => G ((Equiv.funSplitAt i (α → Bool)).symm (g_i, g_other) k)) =
    (Equiv.funSplitAt i Bool).symm (G g_i, fun k => G (g_other k)) := by
  funext k
  simp only [Equiv.funSplitAt_symm_apply]
  by_cases hk : k = i <;> simp [hk]

/-- The reconstructed function `funSplitAt.symm (b, t_other)` equals
`funSplitAt.symm (false, t_other)` updated at `i` with `b`. -/
lemma funSplitAt_symm_eq_update {β : Type*} [DecidableEq β]
    (i : β) (b : Bool) (t_other : { j : β // j ≠ i } → Bool) :
    (Equiv.funSplitAt i Bool).symm (b, t_other) =
      Function.update ((Equiv.funSplitAt i Bool).symm (false, t_other)) i b := by
  funext k
  simp only [Equiv.funSplitAt_symm_apply, Function.update_apply]
  by_cases hk : k = i <;> simp [hk]

/-- After the `funSplitAt` split, the change indicator at coord `i` is
independent of the `b`-component. Combines `funSplitAt_symm_eq_update` and
`change_indicator_update_self`. -/
lemma change_indicator_funSplitAt_independent {β : Type*} [DecidableEq β]
    (F : (β → Bool) → Bool) (i : β) (b : Bool)
    (t_other : { j : β // j ≠ i } → Bool) :
    (if F ((Equiv.funSplitAt i Bool).symm (b, t_other)) ≠
          F (flipBit ((Equiv.funSplitAt i Bool).symm (b, t_other)) i)
        then (1 : ℕ) else 0) =
      (if F ((Equiv.funSplitAt i Bool).symm (false, t_other)) ≠
            F (flipBit ((Equiv.funSplitAt i Bool).symm (false, t_other)) i)
          then (1 : ℕ) else 0) := by
  rw [funSplitAt_symm_eq_update]
  exact change_indicator_update_self F i
    ((Equiv.funSplitAt i Bool).symm (false, t_other)) b

/-- The product `∏_{k : β} w(funSplitAt.symm (b, t_other) k)` factors as
`w b · ∏_{k : {j // j ≠ i}} w(t_other k)`. -/
lemma prod_funSplitAt_symm {β : Type*} [Fintype β] [DecidableEq β]
    (i : β) (w : Bool → ℕ) (b : Bool) (t_other : { j : β // j ≠ i } → Bool) :
    ∏ k : β, w ((Equiv.funSplitAt i Bool).symm (b, t_other) k) =
    w b * ∏ k : { j : β // j ≠ i }, w (t_other k) := by
  rw [← Finset.mul_prod_erase Finset.univ
        (fun k => w ((Equiv.funSplitAt i Bool).symm (b, t_other) k))
        (Finset.mem_univ i)]
  congr 1
  · rw [Equiv.funSplitAt_symm_apply, dif_pos rfl]
  · -- ∏_{k ∈ erase i} w(funSplit k) = ∏_{k : Subtype (· ≠ i)} w(t_other k)
    rw [Finset.prod_subtype (Finset.univ.erase i)
          (p := fun j => j ≠ i)
          (h := fun x => by rw [Finset.mem_erase]; simp)
          (f := fun k => w ((Equiv.funSplitAt i Bool).symm (b, t_other) k))]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [Equiv.funSplitAt_symm_apply]
    simp [k.property]

/-- **Weighted-sensitivity factorization.** The sum `∑_t (∏_k w(t k)) ·
indicator(F changes at i in t)` factors as `(w true + w false) · (sum
over t_other)`, isolating the coordinate `i`. -/
lemma weighted_change_sum_factor {β : Type*} [Fintype β] [DecidableEq β]
    (F : (β → Bool) → Bool) (i : β) (w : Bool → ℕ) :
    ∑ t : β → Bool, (∏ k : β, w (t k)) *
        (if F t ≠ F (flipBit t i) then (1 : ℕ) else 0) =
    (w true + w false) *
      ∑ t_other : { j : β // j ≠ i } → Bool,
        (∏ k : { j : β // j ≠ i }, w (t_other k)) *
        (if F ((Equiv.funSplitAt i Bool).symm (false, t_other)) ≠
              F (flipBit ((Equiv.funSplitAt i Bool).symm (false, t_other)) i)
            then (1 : ℕ) else 0) := by
  rw [sum_pi_split_at i]
  -- Rewrite each term using the product/indicator factorizations
  have h_inner : ∀ (b : Bool) (t_other : { j : β // j ≠ i } → Bool),
      (∏ k : β, w ((Equiv.funSplitAt i Bool).symm (b, t_other) k)) *
      (if F ((Equiv.funSplitAt i Bool).symm (b, t_other)) ≠
            F (flipBit ((Equiv.funSplitAt i Bool).symm (b, t_other)) i)
          then (1 : ℕ) else 0) =
      w b * ((∏ k : { j : β // j ≠ i }, w (t_other k)) *
             (if F ((Equiv.funSplitAt i Bool).symm (false, t_other)) ≠
                   F (flipBit ((Equiv.funSplitAt i Bool).symm (false, t_other)) i)
                 then (1 : ℕ) else 0)) := by
    intros b t_other
    rw [prod_funSplitAt_symm, change_indicator_funSplitAt_independent]
    ring
  simp_rw [h_inner, ← Finset.mul_sum, ← Finset.sum_mul, Fintype.sum_bool]

/-- **Per-`i` compose factorization.** For each fixed `i`, the sum
`∑_g indicator(F changes at i in G ∘ g) · sensitivityAt G(g i)` factors
as `totalSensitivity G · (weighted sum over t_-i)`. -/
lemma sum_compose_per_i_factor {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (F : (β → Bool) → Bool) (G : (α → Bool) → Bool) (i : β) :
    ∑ g : β → α → Bool,
      (if F (fun k => G (g k)) ≠
            F (flipBit (fun k => G (g k)) i) then (1 : ℕ) else 0) *
      sensitivityAt G (g i) =
    totalSensitivity G *
      ∑ t_other : { j : β // j ≠ i } → Bool,
        (∏ k : { j : β // j ≠ i },
          (Finset.univ.filter (fun x : α → Bool => G x = t_other k)).card) *
        (if F ((Equiv.funSplitAt i Bool).symm (false, t_other)) ≠
              F (flipBit ((Equiv.funSplitAt i Bool).symm (false, t_other)) i)
            then (1 : ℕ) else 0) := by
  rw [sum_pi_split_at_general i]
  -- the indicator's independence of the i-coord value.
  have h_inner : ∀ (g_i : α → Bool) (g_other : { j : β // j ≠ i } → α → Bool),
      ((if F (fun k => G ((Equiv.funSplitAt i (α → Bool)).symm (g_i, g_other) k)) ≠
            F (flipBit (fun k => G ((Equiv.funSplitAt i (α → Bool)).symm
                (g_i, g_other) k)) i) then (1 : ℕ) else 0) *
       sensitivityAt G
          ((Equiv.funSplitAt i (α → Bool)).symm (g_i, g_other) i)) =
      sensitivityAt G g_i *
      (if F ((Equiv.funSplitAt i Bool).symm
              (false, fun k : { j : β // j ≠ i } => G (g_other k))) ≠
            F (flipBit ((Equiv.funSplitAt i Bool).symm
              (false, fun k : { j : β // j ≠ i } => G (g_other k))) i)
          then (1 : ℕ) else 0) := by
    intros g_i g_other
    have h_at_i : (Equiv.funSplitAt i (α → Bool)).symm (g_i, g_other) i = g_i := by
      rw [Equiv.funSplitAt_symm_apply, dif_pos rfl]
    rw [h_at_i, compose_G_funSplitAt G i g_i g_other,
        change_indicator_funSplitAt_independent F i (G g_i)
          (fun k : { j : β // j ≠ i } => G (g_other k))]
    ring
  simp_rw [h_inner]
  rw [← Finset.sum_mul_sum]
  congr 1
  exact sum_compose_G (β := { j : β // j ≠ i }) G
    (fun t => if F ((Equiv.funSplitAt i Bool).symm (false, t)) ≠
              F (flipBit ((Equiv.funSplitAt i Bool).symm (false, t)) i)
            then (1 : ℕ) else 0)

/-- **Partition by output value**: `|{G=true}| + |{G=false}| = 2^|α|`. -/
lemma countAt_partition_sum {α : Type*} [Fintype α] [DecidableEq α]
    (G : (α → Bool) → Bool) :
    (Finset.univ.filter (fun x : α → Bool => G x = true)).card +
    (Finset.univ.filter (fun x : α → Bool => G x = false)).card =
    Fintype.card (α → Bool) := by
  have h_part : (Finset.univ : Finset (α → Bool)) =
      ((Finset.univ : Finset (α → Bool)).filter (fun x => G x = true)) ∪
      ((Finset.univ : Finset (α → Bool)).filter (fun x => G x = false)) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases G x <;> simp
  have h_disj : Disjoint
      ((Finset.univ : Finset (α → Bool)).filter (fun x => G x = true))
      ((Finset.univ : Finset (α → Bool)).filter (fun x => G x = false)) := by
    rw [Finset.disjoint_filter]
    intros x _ h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
  rw [← Finset.card_union_of_disjoint h_disj, ← h_part, Finset.card_univ]

/-- **General total-sensitivity compose formula.** For arbitrary monotone or
non-monotone, self-dual or not, `F` and `G`,
`card(α → Bool) · totalSens(F ∘ G) = totalSens G · weightedTotalSens F w`
where `w b = |G^{-1}(b)|`. Generalizes `IsSelfDual.totalSensitivity_compose`. -/
theorem totalSensitivity_compose_general {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (F : (β → Bool) → Bool) (G : (α → Bool) → Bool) :
    Fintype.card (α → Bool) *
      totalSensitivity (InfluenceSensitivity.compose F G) =
    totalSensitivity G *
      weightedTotalSensitivity F
        (fun b => (Finset.univ.filter (fun x : α → Bool => G x = b)).card) := by
  -- Per-`i`: card · ∑_g (indicator · sensAt G(g i)) = totalSens G · ∑_t (∏N) · indicator(F at t).
  have h_card_sum : Fintype.card (α → Bool) =
      (Finset.univ.filter (fun x : α → Bool => G x = true)).card +
      (Finset.univ.filter (fun x : α → Bool => G x = false)).card :=
    (countAt_partition_sum G).symm
  have h_per_i : ∀ i : β,
      Fintype.card (α → Bool) *
        ∑ g : β → α → Bool,
          (if F (fun k => G (g k)) ≠
                F (flipBit (fun k => G (g k)) i) then (1 : ℕ) else 0) *
          sensitivityAt G (g i) =
      totalSensitivity G *
        ∑ t : β → Bool,
          (∏ k : β,
            (Finset.univ.filter (fun x : α → Bool => G x = t k)).card) *
          (if F t ≠ F (flipBit t i) then (1 : ℕ) else 0) := by
    intro i
    rw [sum_compose_per_i_factor F G i, h_card_sum]
    rw [weighted_change_sum_factor F i
        (fun b => (Finset.univ.filter (fun x : α → Bool => G x = b)).card)]
    ring
  -- Now assemble: distribute, swap, apply h_per_i, factor.
  rw [totalSensitivity_compose_eq_sum, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl
    (fun i _ => (Finset.mul_sum _ _ _).symm.trans (h_per_i i)), ← Finset.mul_sum]
  rfl

/-- **q-biased influence.** The weighted total sensitivity divided by the
total weight raised to `|β|`. With `w(b) = countAt G b`, this equals the
q-biased influence at parameter `q = w true / (w true + w false)`. -/
noncomputable def biasedInfluence {β : Type*} [Fintype β] [DecidableEq β]
    (F : (β → Bool) → Bool) (w : Bool → ℕ) : ℝ :=
  (weightedTotalSensitivity F w : ℝ) /
    ((w true + w false : ℕ) : ℝ) ^ Fintype.card β

/-- **Influence multiplicativity for arbitrary `G` (real form).**
`influence(F ∘ G) = influence G · biasedInfluence F (countAt G)`. Generalizes
`IsSelfDual.influence_compose` to arbitrary `G`. -/
theorem influence_compose_general {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (F : (β → Bool) → Bool) (G : (α → Bool) → Bool) :
    influence (InfluenceSensitivity.compose F G) =
    influence G * biasedInfluence F
      (fun b => (Finset.univ.filter (fun x : α → Bool => G x = b)).card) := by
  -- Cast totalSensitivity_compose_general to ℝ and rearrange.
  have h_int := totalSensitivity_compose_general F G
  have h_int_ℝ : (Fintype.card (α → Bool) : ℝ) *
      (totalSensitivity (InfluenceSensitivity.compose F G) : ℝ) =
      (totalSensitivity G : ℝ) *
      (weightedTotalSensitivity F
        (fun b => (Finset.univ.filter (fun x : α → Bool => G x = b)).card) : ℝ) := by
    exact_mod_cast h_int
  -- Set up: card (α → Bool) = 2^|α| and card (β × α) = |β| · |α|.
  have h_card_αBool : (Fintype.card (α → Bool) : ℝ) = (2 : ℝ) ^ Fintype.card α := by
    rw [Fintype.card_fun, Fintype.card_bool]; push_cast; rfl
  have h_card_sum :
      ((Finset.univ.filter (fun x : α → Bool => G x = true)).card : ℝ) +
      ((Finset.univ.filter (fun x : α → Bool => G x = false)).card : ℝ) =
      (Fintype.card (α → Bool) : ℝ) := by exact_mod_cast countAt_partition_sum G
  -- Now compute influence(F∘G) = totalSens(F∘G) / 2^|β×α|.
  unfold influence biasedInfluence
  rw [Fintype.card_prod]
  push_cast
  rw [show (((Finset.univ.filter (fun x : α → Bool => G x = true)).card : ℝ) +
          ((Finset.univ.filter (fun x : α → Bool => G x = false)).card : ℝ)) ^ Fintype.card β =
        (Fintype.card (α → Bool) : ℝ) ^ Fintype.card β from by rw [h_card_sum],
      h_card_αBool, ← pow_mul,
      show Fintype.card α * Fintype.card β = Fintype.card β * Fintype.card α from by ring]
  rw [h_card_αBool] at h_int_ℝ
  field_simp
  linear_combination h_int_ℝ

/-- **Self-dual collapse:** for self-dual `f`, `compose (dual f) f = compose f f`. -/
lemma IsSelfDual.compose_dual_eq_self_compose {α : Type*}
    {f : (α → Bool) → Bool} (hsd : IsSelfDual f) :
    InfluenceSensitivity.compose (InfluenceSensitivity.dual f) f =
    InfluenceSensitivity.compose f f := by
  rw [hsd.dual_eq]

/-- For self-dual `f`, the construction `f^* ∘ f` is itself self-dual. -/
lemma IsSelfDual.compose_dual_self {α : Type*}
    {f : (α → Bool) → Bool} (hsd : IsSelfDual f) :
    IsSelfDual (InfluenceSensitivity.compose (InfluenceSensitivity.dual f) f) := by
  rw [hsd.compose_dual_eq_self_compose]; exact hsd.compose hsd

/-- For self-dual `f`, the construction `f ∘ f^*` is also self-dual. -/
lemma IsSelfDual.compose_self_dual {α : Type*}
    {f : (α → Bool) → Bool} (hsd : IsSelfDual f) :
    IsSelfDual (InfluenceSensitivity.compose f (InfluenceSensitivity.dual f)) := by
  rw [hsd.dual_eq]; exact hsd.compose hsd

/-- **Monotonicity of `f^* ∘ f`:** if `f` is monotone, so is `compose (dual f) f`. -/
lemma IsMonotone.compose_dual_self {α : Type*}
    {f : (α → Bool) → Bool} (hmono : IsMonotone f) :
    IsMonotone (InfluenceSensitivity.compose (InfluenceSensitivity.dual f) f) :=
  hmono.dual.compose hmono

/-- **Monotonicity of `f ∘ f^*`:** symmetric companion of
`IsMonotone.compose_dual_self`. -/
lemma IsMonotone.compose_self_dual {α : Type*}
    {f : (α → Bool) → Bool} (hmono : IsMonotone f) :
    IsMonotone (InfluenceSensitivity.compose f (InfluenceSensitivity.dual f)) :=
  hmono.compose hmono.dual

/-- **Influence is bounded by max sensitivity.** Holds for any Boolean function:
since `influence = E[sensitivityAt f X]` and `sensitivityAt f X ≤ maxSensitivity f`. -/
lemma influence_le_maxSensitivity {α : Type*} [Fintype α] [DecidableEq α]
    (f : (α → Bool) → Bool) :
    influence f ≤ (maxSensitivity f : ℝ) := by
  unfold influence
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ Fintype.card α)]
  have h_total_le : totalSensitivity f ≤ maxSensitivity f * (2 ^ Fintype.card α) := by
    unfold totalSensitivity
    calc (∑ x : α → Bool, sensitivityAt f x)
        ≤ ∑ _x : α → Bool, maxSensitivity f :=
          Finset.sum_le_sum fun x _ => Finset.le_sup (Finset.mem_univ x)
      _ = maxSensitivity f * 2 ^ Fintype.card α := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]; simp; ring
  exact_mod_cast h_total_le

/-- A sequence of monotone Boolean functions on varying finite domains. -/
structure BooleanFamily where
  β : ℕ → Type
  fintype : ∀ k, Fintype (β k)
  decEq : ∀ k, DecidableEq (β k)
  H : ∀ k, (β k → Bool) → Bool

attribute [instance] BooleanFamily.fintype BooleanFamily.decEq

/-- **Generic exponent achievability.** A `BooleanFamily` whose `liminf
log(Inf)/log(s) ≥ r` and whose maxSensitivity tends to infinity. -/
def ExponentAchievable (r : ℝ) : Prop :=
  ∃ fam : BooleanFamily,
    (∀ k, IsMonotone (fam.H k)) ∧
    Filter.Tendsto (fun k => (maxSensitivity (fam.H k) : ℕ)) Filter.atTop Filter.atTop ∧
    r ≤ Filter.liminf (fun k =>
      Real.log (influence (fam.H k)) / Real.log (maxSensitivity (fam.H k) : ℝ))
      Filter.atTop

/-- Achievability is monotone: bigger exponents are harder. -/
lemma ExponentAchievable.mono {r s : ℝ} (h : r ≤ s) (hs : ExponentAchievable s) :
    ExponentAchievable r := by
  rcases hs with ⟨fam, h_mono, h_max, h_α⟩
  exact ⟨fam, h_mono, h_max, h.trans h_α⟩

/-- **Achievability upper bound.** Every achievable exponent satisfies `r ≤ 1`.
This follows from `Inf ≤ s` for monotone Boolean functions (giving
`log(Inf)/log(s) ≤ 1` eventually as `s > 1`). -/
theorem ExponentAchievable.le_one {r : ℝ} (hr : ExponentAchievable r) : r ≤ 1 := by
  rcases hr with ⟨fam, _h_mono, h_max, h_α⟩
  refine h_α.trans ?_
  set F := fun k : ℕ =>
    Real.log (influence (fam.H k)) / Real.log (maxSensitivity (fam.H k) : ℝ)
  have h_s_gt_one : ∀ᶠ k : ℕ in Filter.atTop, (1 : ℝ) < (maxSensitivity (fam.H k) : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp h_max).eventually_gt_atTop 1
  have h_F_le_1 : ∀ᶠ k : ℕ in Filter.atTop, F k ≤ 1 := by
    filter_upwards [h_s_gt_one] with k hsk
    have h_log_s_pos : 0 < Real.log (maxSensitivity (fam.H k) : ℝ) := Real.log_pos hsk
    rw [show F k = _ from rfl, div_le_one h_log_s_pos]
    have h_Inf_le_s := influence_le_maxSensitivity (fam.H k)
    have h_nonneg : (0 : ℝ) ≤ influence (fam.H k) := by unfold influence; positivity
    rcases lt_or_eq_of_le h_nonneg with h_pos | h_zero
    · exact Real.log_le_log h_pos h_Inf_le_s
    · rw [← h_zero, Real.log_zero]; exact h_log_s_pos.le
  rw [Filter.liminf_eq]
  by_cases hS : ({a | ∀ᶠ k in Filter.atTop, a ≤ F k} : Set ℝ).Nonempty
  · refine csSup_le hS fun a ha => ?_
    rcases (ha.and h_F_le_1).exists with ⟨_, hak, h1k⟩
    exact hak.trans h1k
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, Real.sSup_empty]; exact zero_le_one

/-- Achievability of the `2/3` exponent: a monotone family with
`liminf log(Inf)/log(s) ≥ 2/3` and maxSensitivity → ∞. -/
def TwoThirdsExponentAchievable : Prop := ExponentAchievable (2 / 3 : ℝ)

/-! ## Probability infrastructure: `p`-biased measures -/

/-- **`p`-biased product measure** on `α → Bool`: independent coordinates each
take value `true` with probability `p`. -/
noncomputable def biasedMeasure {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (x : α → Bool) : ℝ :=
  ∏ i : α, (if x i = true then p else 1 - p)

/-- **`p`-biased probability** of an event `S : Finset (α → Bool)`. -/
noncomputable def biasedProb {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (S : Finset (α → Bool)) : ℝ :=
  ∑ x ∈ S, biasedMeasure p x

/-- **`p`-biased expectation** of a function `f : (α → Bool) → ℝ`. -/
noncomputable def biasedExpectation {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (f : (α → Bool) → ℝ) : ℝ :=
  ∑ x : α → Bool, biasedMeasure p x * f x

/-- **Biased measure is non-negative for `p ∈ [0, 1]`.** -/
lemma biasedMeasure_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : α → Bool) :
    0 ≤ biasedMeasure p x :=
  Finset.prod_nonneg fun _ _ => by split_ifs <;> linarith

/-- **Biased measure as a product** (definitional). -/
lemma biasedMeasure_eq_prod {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (x : α → Bool) :
    biasedMeasure p x = ∏ i : α, (if x i = true then p else (1 - p)) := rfl

/-- **Biased probability is non-negative for `p ∈ [0, 1]`.** -/
lemma biasedProb_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (α → Bool)) :
    0 ≤ biasedProb p S := by
  unfold biasedProb
  exact Finset.sum_nonneg (fun x _ => biasedMeasure_nonneg hp0 hp1 x)

/-- **Biased expectation of a non-negative function is non-negative for `p ∈ [0, 1]`.** -/
lemma biasedExpectation_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f : (α → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ biasedExpectation p f := by
  unfold biasedExpectation
  exact Finset.sum_nonneg
    (fun x _ => mul_nonneg (biasedMeasure_nonneg hp0 hp1 x) (hf x))

/-- **Linearity (subtraction) of biased expectation.** `E_p[f - g] = E_p[f] - E_p[g]`. -/
lemma biasedExpectation_sub {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (f g : (α → Bool) → ℝ) :
    biasedExpectation p (fun x => f x - g x) =
    biasedExpectation p f - biasedExpectation p g := by
  unfold biasedExpectation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intros x _; ring

/-- **Biased expectation of indicator equals biased probability.**
The indicator `1_S x = if x ∈ S then 1 else 0` integrates to `biasedProb p S`. -/
lemma biasedExpectation_indicator {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (S : Finset (α → Bool)) :
    biasedExpectation p (fun x => if x ∈ S then (1 : ℝ) else 0) =
    biasedProb p S := by
  unfold biasedExpectation biasedProb
  rw [show (∑ x : α → Bool, biasedMeasure p x *
              (if x ∈ S then (1 : ℝ) else 0)) =
        ∑ x : α → Bool, (if x ∈ S then biasedMeasure p x else 0) from
        Finset.sum_congr rfl fun x _ => by by_cases h : x ∈ S <;> simp [h],
      Finset.sum_ite_mem]
  congr 1; ext x; simp

/-- **Biased expectation respects pointwise ≤.** -/
lemma biasedExpectation_le_of_le {α : Type*} [Fintype α] [DecidableEq α]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : (α → Bool) → ℝ} (h : ∀ x, f x ≤ g x) :
    biasedExpectation p f ≤ biasedExpectation p g := by
  unfold biasedExpectation
  apply Finset.sum_le_sum
  intros x _
  exact mul_le_mul_of_nonneg_left (h x) (biasedMeasure_nonneg hp0 hp1 x)

/-- **Linearity-of-sum: biasedExpectation distributes over a Finset sum.** -/
lemma biasedExpectation_finset_sum {α β : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (s : Finset β) (f : β → (α → Bool) → ℝ) :
    biasedExpectation p (fun x => ∑ i ∈ s, f i x) =
    ∑ i ∈ s, biasedExpectation p (f i) := by
  unfold biasedExpectation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intros i _
  rw [Finset.mul_sum]

/-- Generic product expectation under the biased measure: separable products
factor across coordinates. -/
lemma biasedExpectation_prod_local {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (φ : α → Bool → ℝ) :
    biasedExpectation p (fun x : α → Bool => ∏ i : α, φ i (x i)) =
      ∏ i : α, ∑ b : Bool, (if b = true then p else 1 - p) * φ i b := by
  unfold biasedExpectation
  simp_rw [fun x => show biasedMeasure p x * (∏ i : α, φ i (x i)) =
      ∏ i : α, ((if x i = true then p else (1 - p)) * φ i (x i))
    from by rw [biasedMeasure_eq_prod, Finset.prod_mul_distrib]]
  exact (Fintype.prod_sum (fun i b => (if b = true then p else 1 - p) * φ i b)).symm

/-- **Biased expectation of a subset indicator (containment event).**
`E_p[∏_{i ∈ S} 1_{x_i = true}] = p^|S|`. This is the probability that the
random support contains `S` under the `p`-biased product measure. -/
lemma biasedExpectation_subset_indicator {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (S : Finset α) :
    biasedExpectation p
      (fun x : α → Bool => ∏ i ∈ S, (if x i = true then (1 : ℝ) else 0)) =
    p ^ S.card := by
  classical
  let φ : α → Bool → ℝ := fun i b => if i ∈ S then (if b = true then 1 else 0) else 1
  have hfull : (fun x : α → Bool => ∏ i ∈ S, (if x i = true then (1 : ℝ) else 0)) =
      (fun x : α → Bool => ∏ i : α, φ i (x i)) := by
    funext x
    rw [show (∏ i : α, φ i (x i)) =
        ∏ i : α, (if i ∈ S then (if x i = true then (1 : ℝ) else 0) else 1) from rfl,
        Finset.prod_ite (s := (Finset.univ : Finset α)) (p := (· ∈ S))
          (fun j => if x j = true then (1 : ℝ) else 0) (fun _ => 1),
        Finset.prod_const_one, mul_one]
    congr 1; ext k; simp
  rw [hfull, biasedExpectation_prod_local p φ]
  have hmarg : ∀ i : α,
      (∑ b : Bool, (if b = true then p else 1 - p) * φ i b) = if i ∈ S then p else 1 :=
    fun i => by by_cases hi : i ∈ S <;> simp [φ, hi]
  simp_rw [hmarg]
  rw [show (∏ i : α, (if i ∈ S then p else (1 : ℝ))) = ∏ i ∈ S, p from by
        rw [Finset.prod_ite (s := (Finset.univ : Finset α)) (p := (· ∈ S))
            (fun _ => p) (fun _ => 1), Finset.prod_const_one, mul_one]
        congr 1; ext k; simp,
      Finset.prod_const]

/-! ## Polynomial-graph gadget

We build the deterministic monotone DNF `F = OR over T of (T ⊆ supp(x))` and derive
sensitivity / influence bounds. -/

/-- **Generic monotone DNF.** Given a family `T : Finset (Finset α)` of terms,
`monotoneDNF T x = true` iff some term `S ∈ T` is contained in `supp(x)` (i.e.,
all coordinates of `S` are `true`). -/
def monotoneDNF {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset (Finset α)) (x : α → Bool) : Bool :=
  decide (∃ S ∈ T, ∀ i ∈ S, x i = true)

/-- **Characterization of `monotoneDNF`.** -/
lemma monotoneDNF_eq_true_iff {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset (Finset α)) (x : α → Bool) :
    monotoneDNF T x = true ↔ ∃ S ∈ T, ∀ i ∈ S, x i = true := by
  unfold monotoneDNF
  exact decide_eq_true_iff

/-- **`monotoneDNF` is monotone in `x`** (in the Boolean order `false ≤ true`). -/
lemma monotoneDNF_isMonotone {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset (Finset α)) : IsMonotone (monotoneDNF T) := by
  intros x y hxy
  cases h_x_val : monotoneDNF T x with
  | false => exact Bool.false_le _
  | true =>
    obtain ⟨S, hS_mem, hS⟩ := (monotoneDNF_eq_true_iff T x).mp h_x_val
    rw [(monotoneDNF_eq_true_iff T y).mpr ⟨S, hS_mem, fun i hi => by
      have h_le : x i ≤ y i := hxy i
      rw [hS i hi] at h_le
      cases hyi : y i
      · rw [hyi] at h_le; exact absurd h_le (by decide)
      · rfl⟩]

/-- **`s_0` is always bounded by `|α|`** (trivial, just from `Finset.univ` being the
filter superset). -/
lemma maxSensitivityZero_le_card {α : Type*} [Fintype α] [DecidableEq α]
    (f : (α → Bool) → Bool) :
    maxSensitivityZero f ≤ Fintype.card α := by
  refine Finset.sup_le ?_
  intros x _
  unfold sensitivityAtZero
  rw [← Finset.card_univ]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- **`s_1(monotoneDNF T) ≤ L`** when all terms have size `≤ L`. At any 1-input,
the 1-pivotal coordinates lie inside some satisfied term `S`. -/
lemma maxSensitivityOne_monotoneDNF_le {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset (Finset α)) (L : ℕ)
    (hL : ∀ S ∈ T, S.card ≤ L) :
    maxSensitivityOne (monotoneDNF T) ≤ L := by
  refine Finset.sup_le ?_
  intros x hx_filter
  rw [Finset.mem_filter] at hx_filter
  obtain ⟨_, h_val⟩ := hx_filter
  -- f x = true, so we have a witness S
  have hx_exists := (monotoneDNF_eq_true_iff T x).mp h_val
  obtain ⟨S, hS_mem, hS⟩ := hx_exists
  unfold sensitivityAtOne
  refine le_trans ?_ (hL S hS_mem)
  refine Finset.card_le_card ?_
  intros i hi
  rw [Finset.mem_filter] at hi
  obtain ⟨_, hxi, hne⟩ := hi
  by_contra h_i_not_in_S
  apply hne
  have h_S_in_flipped : ∀ j ∈ S, (flipBit x i) j = true := fun j hj => by
    have hji : j ≠ i := fun h => h_i_not_in_S (h ▸ hj)
    rw [flipBit_apply_of_ne _ hji]; exact hS j hj
  have h_flip_true : monotoneDNF T (flipBit x i) = true :=
    (monotoneDNF_eq_true_iff T _).mpr ⟨S, hS_mem, h_S_in_flipped⟩
  rw [h_val, h_flip_true]

/-- **Product of two subset-indicators is the union-indicator.**
The pointwise identity used for the second-moment cross-term computation. -/
lemma prod_two_subset_indicator_eq_union {α : Type*} [DecidableEq α]
    (S T : Finset α) (x : α → Bool) :
    (∏ i ∈ S, (if x i = true then (1 : ℝ) else 0)) *
    (∏ i ∈ T, (if x i = true then (1 : ℝ) else 0)) =
    ∏ i ∈ S ∪ T, (if x i = true then (1 : ℝ) else 0) := by
  by_cases h : ∀ i ∈ S ∪ T, x i = true
  · have hS : ∀ i ∈ S, x i = true := fun i hi => h i (Finset.mem_union_left T hi)
    have hT : ∀ i ∈ T, x i = true := fun i hi => h i (Finset.mem_union_right S hi)
    rw [Finset.prod_eq_one (fun i hi => by simp [hS i hi])]
    rw [Finset.prod_eq_one (fun i hi => by simp [hT i hi])]
    rw [Finset.prod_eq_one (fun i hi => by simp [h i hi])]
    ring
  · push Not at h
    obtain ⟨i, hi_mem, hi_false⟩ := h
    have h_zero_union :
        (∏ j ∈ S ∪ T, (if x j = true then (1 : ℝ) else 0)) = 0 :=
      Finset.prod_eq_zero hi_mem (by simp [hi_false])
    rw [h_zero_union]
    rw [Finset.mem_union] at hi_mem
    cases hi_mem with
    | inl hS =>
      rw [show (∏ i ∈ S, (if x i = true then (1 : ℝ) else 0)) = 0 from
          Finset.prod_eq_zero hS (by simp [hi_false]), zero_mul]
    | inr hT =>
      rw [show (∏ i ∈ T, (if x i = true then (1 : ℝ) else 0)) = 0 from
          Finset.prod_eq_zero hT (by simp [hi_false]), mul_zero]

/-- **Two-subset containment expectation.** `E_p[1_{S ⊆ supp} · 1_{T ⊆ supp}] = p^|S ∪ T|`.
The product of two containment events equals containment of the union. -/
lemma biasedExpectation_two_subset_indicator {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (S T : Finset α) :
    biasedExpectation p
      (fun x : α → Bool => (∏ i ∈ S, (if x i = true then (1 : ℝ) else 0)) *
                            (∏ i ∈ T, (if x i = true then (1 : ℝ) else 0))) =
    p ^ (S ∪ T).card := by
  rw [show (fun x : α → Bool =>
        (∏ i ∈ S, (if x i = true then (1 : ℝ) else 0)) *
        (∏ i ∈ T, (if x i = true then (1 : ℝ) else 0))) =
        (fun x : α → Bool =>
          ∏ i ∈ S ∪ T, (if x i = true then (1 : ℝ) else 0)) from
        funext (prod_two_subset_indicator_eq_union S T)]
  exact biasedExpectation_subset_indicator p (S ∪ T)

/-- **First moment of `Y = #{S ∈ T : S ⊆ supp(x)}`.** `E_p[Y] = ∑_{S ∈ T} p^|S|`. -/
lemma biasedExpectation_sum_subset_indicator {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (T : Finset (Finset α)) :
    biasedExpectation p (fun x : α → Bool =>
      ∑ S ∈ T, (∏ i ∈ S, (if x i = true then (1 : ℝ) else 0))) =
    ∑ S ∈ T, p ^ S.card := by
  rw [biasedExpectation_finset_sum]
  apply Finset.sum_congr rfl
  intros S _
  exact biasedExpectation_subset_indicator p S

/-- **Second moment of `Y`.** `E_p[Y²] = ∑_{S, S' ∈ T} p^|S ∪ S'|`. -/
lemma biasedExpectation_sum_subset_indicator_sq {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (T : Finset (Finset α)) :
    biasedExpectation p (fun x : α → Bool =>
      (∑ S ∈ T, (∏ i ∈ S, (if x i = true then (1 : ℝ) else 0)))^2) =
    ∑ S ∈ T, ∑ S' ∈ T, p ^ (S ∪ S').card := by
  have h_sq : ∀ x : α → Bool,
      (∑ S ∈ T, (∏ i ∈ S, (if x i = true then (1 : ℝ) else 0)))^2 =
      ∑ S ∈ T, ∑ S' ∈ T,
        (∏ i ∈ S, (if x i = true then (1 : ℝ) else 0)) *
        (∏ i ∈ S', (if x i = true then (1 : ℝ) else 0)) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
  simp_rw [h_sq]
  rw [biasedExpectation_finset_sum]
  apply Finset.sum_congr rfl
  intros S _
  rw [biasedExpectation_finset_sum]
  apply Finset.sum_congr rfl
  intros S' _
  exact biasedExpectation_two_subset_indicator p S S'

/-- **`p`-biased influence**: expected sensitivity under the `p`-biased product measure.
At `p = 1/2`, this matches the file's existing `influence`. -/
noncomputable def infP {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (f : (α → Bool) → Bool) : ℝ :=
  biasedExpectation p (fun x => (sensitivityAt f x : ℝ))

/-- **`infP` is non-negative for `p ∈ [0, 1]`.** -/
lemma infP_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (α → Bool) → Bool) :
    0 ≤ infP p f := by
  unfold infP
  exact biasedExpectation_nonneg hp0 hp1 (fun x => Nat.cast_nonneg _)

/-- **Uniform biased measure is constant `1/2^|α|`.** -/
lemma biasedMeasure_half {α : Type*} [Fintype α] [DecidableEq α] (x : α → Bool) :
    biasedMeasure (1/2 : ℝ) x = (1/2 : ℝ) ^ Fintype.card α := by
  unfold biasedMeasure
  rw [show (fun i : α => if x i = true then (1/2 : ℝ) else 1 - 1/2) =
        fun _ : α => (1/2 : ℝ) from by funext i; split_ifs <;> norm_num,
      Finset.prod_const, Finset.card_univ]

/-- **`infP (1/2) f = influence f`**: the `1/2`-biased influence is the uniform influence. -/
lemma infP_half_eq_influence {α : Type*} [Fintype α] [DecidableEq α]
    (f : (α → Bool) → Bool) :
    infP (1/2 : ℝ) f = influence f := by
  unfold infP biasedExpectation influence totalSensitivity
  rw [show (∑ x : α → Bool, biasedMeasure (1/2 : ℝ) x * (sensitivityAt f x : ℝ)) =
        ∑ x : α → Bool, (1/2 : ℝ) ^ Fintype.card α * (sensitivityAt f x : ℝ) from
        Finset.sum_congr rfl (fun x _ => by rw [biasedMeasure_half])]
  rw [← Finset.mul_sum]
  rw [show ((1/2 : ℝ) ^ Fintype.card α) = 1 / (2 : ℝ) ^ Fintype.card α from by
        rw [one_div, one_div, inv_pow]]
  rw [div_mul_eq_mul_div, one_mul]
  push_cast
  rfl

/-- **Number of satisfied terms** at input `x`: how many `S ∈ T` are contained
in the support of `x`. -/
def subsetSatisfiedCount {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset (Finset α)) (x : α → Bool) : ℕ :=
  (T.filter (fun S => ∀ i ∈ S, x i = true)).card

/-- **Sharper pointwise PZ:** `Y - Y(Y-1) ≤ 1_{Y = 1}` for nonneg integer `Y`.
For Y = 0: 0 ≤ 0. For Y = 1: 1 ≤ 1. For Y ≥ 2: Y - Y(Y-1) = -Y(Y-2) ≤ 0. -/
lemma subsetSatisfiedCount_paley_zygmund_unique {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset (Finset α)) (x : α → Bool) :
    (subsetSatisfiedCount T x : ℝ) -
    (subsetSatisfiedCount T x : ℝ) * ((subsetSatisfiedCount T x : ℝ) - 1) ≤
    (if subsetSatisfiedCount T x = 1 then (1 : ℝ) else 0) := by
  set y := subsetSatisfiedCount T x with hy
  by_cases hy0 : y = 0
  · rw [hy0]; simp
  · by_cases hy1 : y = 1
    · rw [hy1]; simp
    · -- y ≥ 2
      have hy_ge : 2 ≤ y := by omega
      rw [if_neg hy1]
      have hy_real_ge_2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy_ge
      nlinarith [hy_real_ge_2]

/-- **Pointwise Paley-Zygmund-style inequality.** For our `Y = subsetSatisfiedCount`:
`Y - Y(Y-1) ≤ 1_{monotoneDNF T = true}`. The key fact is that `Y` is a non-negative
integer, so `Y - Y(Y-1) ≤ 1` (via `(Y-1)² ≥ 0`), and `Y - Y(Y-1) = 0` when `Y = 0`. -/
lemma subsetSatisfiedCount_paley_zygmund {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset (Finset α)) (x : α → Bool) :
    (subsetSatisfiedCount T x : ℝ) -
    (subsetSatisfiedCount T x : ℝ) * ((subsetSatisfiedCount T x : ℝ) - 1) ≤
    (if monotoneDNF T x = true then (1 : ℝ) else 0) := by
  cases h : monotoneDNF T x with
  | false =>
    have h_count : subsetSatisfiedCount T x = 0 := by
      unfold subsetSatisfiedCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intros S hS h_all
      have h_exists : ∃ S ∈ T, ∀ i ∈ S, x i = true := ⟨S, hS, h_all⟩
      have h_true := (monotoneDNF_eq_true_iff T x).mpr h_exists
      rw [h] at h_true
      exact absurd h_true (by decide)
    rw [h_count]; simp
  | true =>
    have h_exists := (monotoneDNF_eq_true_iff T x).mp h
    have h_count_ge : 1 ≤ subsetSatisfiedCount T x := by
      unfold subsetSatisfiedCount
      rw [Nat.one_le_iff_ne_zero]
      intro h_zero
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h_zero
      obtain ⟨S, hS, h_all⟩ := h_exists
      exact h_zero hS h_all
    have h_real_ge : (1 : ℝ) ≤ (subsetSatisfiedCount T x : ℝ) := by exact_mod_cast h_count_ge
    change (subsetSatisfiedCount T x : ℝ) -
         (subsetSatisfiedCount T x : ℝ) * ((subsetSatisfiedCount T x : ℝ) - 1) ≤
         (if true = true then (1 : ℝ) else 0)
    rw [if_pos rfl]
    nlinarith [sq_nonneg ((subsetSatisfiedCount T x : ℝ) - 1)]

/-- **Bridge: integer count equals real-valued indicator sum.** -/
lemma subsetSatisfiedCount_cast {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset (Finset α)) (x : α → Bool) :
    (subsetSatisfiedCount T x : ℝ) =
    ∑ S ∈ T, ∏ i ∈ S, (if x i = true then (1 : ℝ) else 0) := by
  unfold subsetSatisfiedCount
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h : ∀ i ∈ S, x i = true
  · rw [if_pos h, Finset.prod_eq_one fun i hi => if_pos (h i hi)]
  · push Not at h
    obtain ⟨i, hi_mem, hi_ne⟩ := h
    rw [if_neg (fun hall => hi_ne (hall i hi_mem)),
      Finset.prod_eq_zero hi_mem (if_neg hi_ne)]

/-- **Sensitivity lower bound at a unique-witness input.** If exactly one term `S ∈ T`
is satisfied at `x` (i.e., `subsetSatisfiedCount T x = 1`), then every coordinate of
that unique `S` is 1-pivotal, so `sensitivityAt (monotoneDNF T) x ≥ L` for any `L ≤ |S|`. -/
lemma sensitivityAt_monotoneDNF_ge_of_unique {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset (Finset α)) (L : ℕ) (hL : ∀ S ∈ T, L ≤ S.card)
    (x : α → Bool) (h_unique : subsetSatisfiedCount T x = 1) :
    L ≤ sensitivityAt (monotoneDNF T) x := by
  obtain ⟨S, hS_eq⟩ := Finset.card_eq_one.mp h_unique
  have hS_in_filter : S ∈ T.filter (fun S' => ∀ i ∈ S', x i = true) := by
    rw [hS_eq]; exact Finset.mem_singleton.mpr rfl
  obtain ⟨hS_mem, hS_supp⟩ := Finset.mem_filter.mp hS_in_filter
  have h_x_true : monotoneDNF T x = true :=
    (monotoneDNF_eq_true_iff T x).mpr ⟨S, hS_mem, hS_supp⟩
  unfold sensitivityAt
  refine le_trans (hL S hS_mem) (Finset.card_le_card fun i hi => ?_)
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ i, ?_⟩
  have hxi : x i = true := hS_supp i hi
  rw [h_x_true]
  cases h_flip : monotoneDNF T (flipBit x i) with
  | false => decide
  | true =>
    exfalso
    obtain ⟨S', hS'_mem, hS'_supp⟩ := (monotoneDNF_eq_true_iff T _).mp h_flip
    -- S' satisfied at flipBit x i: every j ∈ S' has x j = true (since flipping at i would
    -- contradict hxi when j = i, otherwise flipBit acts as identity).
    have hS'_supp_x : ∀ j ∈ S', x j = true := fun j hj => by
      have hxj_flip := hS'_supp j hj
      by_cases hji : j = i
      · subst hji; rw [flipBit, Function.update_self, hxi] at hxj_flip
        exact absurd hxj_flip (by decide)
      · rwa [flipBit_apply_of_ne _ hji] at hxj_flip
    have hS'_in : S' ∈ T.filter (fun S => ∀ i ∈ S, x i = true) :=
      Finset.mem_filter.mpr ⟨hS'_mem, hS'_supp_x⟩
    rw [hS_eq, Finset.mem_singleton] at hS'_in
    subst hS'_in
    have hxi_flip := hS'_supp i hi
    rw [flipBit, Function.update_self, hxi] at hxi_flip
    exact absurd hxi_flip (by decide)

/-- **Influence lower bound via the unique-witness event.**
`infP p (monotoneDNF T) ≥ L · Pr_p[Y = 1]` when all terms have size ≥ L. -/
lemma infP_monotoneDNF_ge_unique_prob {α : Type*} [Fintype α] [DecidableEq α]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T : Finset (Finset α)) (L : ℕ)
    (hL : ∀ S ∈ T, L ≤ S.card) :
    (L : ℝ) * biasedProb p
        (Finset.univ.filter (fun x : α → Bool => subsetSatisfiedCount T x = 1)) ≤
    infP p (monotoneDNF T) := by
  unfold infP biasedProb
  rw [Finset.mul_sum]
  unfold biasedExpectation
  apply le_trans (b := ∑ x ∈ Finset.univ.filter
        (fun x : α → Bool => subsetSatisfiedCount T x = 1),
      biasedMeasure p x * (sensitivityAt (monotoneDNF T) x : ℝ))
  · -- L · ∑_{x : Y(x) = 1} μ(x) ≤ ∑_{x : Y(x) = 1} μ(x) · sensitivityAt
    apply Finset.sum_le_sum
    intros x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨_, hY⟩ := hx
    have h_sens := sensitivityAt_monotoneDNF_ge_of_unique T L hL x hY
    have h_sens_real : (L : ℝ) ≤ (sensitivityAt (monotoneDNF T) x : ℝ) := by
      exact_mod_cast h_sens
    -- biasedMeasure x ≥ 0
    have h_meas : 0 ≤ biasedMeasure p x := biasedMeasure_nonneg hp0 hp1 x
    nlinarith [h_meas, h_sens_real]
  · -- Restrict to filter ≤ all
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intros x _ _
    exact mul_nonneg (biasedMeasure_nonneg hp0 hp1 x) (Nat.cast_nonneg _)

/-- **First moment of `subsetSatisfiedCount`.** `E_p[Y] = ∑_{S ∈ T} p^|S|`. -/
lemma biasedExpectation_subsetSatisfiedCount {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (T : Finset (Finset α)) :
    biasedExpectation p (fun x : α → Bool => (subsetSatisfiedCount T x : ℝ)) =
    ∑ S ∈ T, p ^ S.card := by
  rw [show (fun x : α → Bool => (subsetSatisfiedCount T x : ℝ)) =
        (fun x : α → Bool =>
          ∑ S ∈ T, ∏ i ∈ S, (if x i = true then (1 : ℝ) else 0)) from
        funext (subsetSatisfiedCount_cast T)]
  exact biasedExpectation_sum_subset_indicator p T

/-- **Second moment of `subsetSatisfiedCount`.** `E_p[Y²] = ∑_{S, S' ∈ T} p^|S ∪ S'|`. -/
lemma biasedExpectation_subsetSatisfiedCount_sq {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (T : Finset (Finset α)) :
    biasedExpectation p (fun x : α → Bool => ((subsetSatisfiedCount T x : ℝ))^2) =
    ∑ S ∈ T, ∑ S' ∈ T, p ^ (S ∪ S').card := by
  rw [show (fun x : α → Bool => ((subsetSatisfiedCount T x : ℝ))^2) =
        (fun x : α → Bool =>
          (∑ S ∈ T, ∏ i ∈ S, (if x i = true then (1 : ℝ) else 0))^2) from ?_]
  · exact biasedExpectation_sum_subset_indicator_sq p T
  · funext x
    rw [subsetSatisfiedCount_cast]

/-- **Factorial moment of `subsetSatisfiedCount`.**
`E_p[Y(Y-1)] = (∑_{S, S' ∈ T} p^|S ∪ S'|) - (∑_S p^|S|)`. -/
lemma biasedExpectation_subsetSatisfiedCount_factorial
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (T : Finset (Finset α)) :
    biasedExpectation p (fun x : α → Bool =>
      (subsetSatisfiedCount T x : ℝ) * ((subsetSatisfiedCount T x : ℝ) - 1)) =
    (∑ S ∈ T, ∑ S' ∈ T, p ^ (S ∪ S').card) - (∑ S ∈ T, p ^ S.card) := by
  rw [show (fun x : α → Bool =>
            (subsetSatisfiedCount T x : ℝ) * ((subsetSatisfiedCount T x : ℝ) - 1)) =
        (fun x : α → Bool =>
          ((subsetSatisfiedCount T x : ℝ))^2 - (subsetSatisfiedCount T x : ℝ)) from ?_]
  · rw [biasedExpectation_sub,
        biasedExpectation_subsetSatisfiedCount_sq,
        biasedExpectation_subsetSatisfiedCount]
  · funext x; ring

/-- **Integrated sharper Paley-Zygmund**: `E_p[Y] - E_p[Y(Y-1)] ≤ Pr_p[Y = 1]`. -/
lemma biasedProb_unique_ge_first_minus_factorial
    {α : Type*} [Fintype α] [DecidableEq α]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T : Finset (Finset α)) :
    biasedExpectation p (fun x => (subsetSatisfiedCount T x : ℝ)) -
    biasedExpectation p (fun x =>
      (subsetSatisfiedCount T x : ℝ) * ((subsetSatisfiedCount T x : ℝ) - 1)) ≤
    biasedProb p (Finset.univ.filter
      (fun x : α → Bool => subsetSatisfiedCount T x = 1)) := by
  rw [← biasedExpectation_sub, ← biasedExpectation_indicator]
  apply biasedExpectation_le_of_le hp0 hp1
  intros x
  rw [show ((if x ∈ Finset.univ.filter
              (fun x : α → Bool => subsetSatisfiedCount T x = 1)
            then (1 : ℝ) else 0)) =
        (if subsetSatisfiedCount T x = 1 then (1 : ℝ) else 0) from ?_]
  · exact subsetSatisfiedCount_paley_zygmund_unique T x
  · simp

/-- **Combined: influence ≥ L · (first - factorial moment).**
`infP p (monotoneDNF T) ≥ L · (E[Y] - E[Y(Y-1)])` when all terms have size ≥ L. -/
lemma infP_monotoneDNF_ge_first_minus_factorial
    {α : Type*} [Fintype α] [DecidableEq α]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T : Finset (Finset α)) (L : ℕ)
    (hL : ∀ S ∈ T, L ≤ S.card) :
    (L : ℝ) * (biasedExpectation p (fun x => (subsetSatisfiedCount T x : ℝ)) -
               biasedExpectation p (fun x =>
                 (subsetSatisfiedCount T x : ℝ) *
                 ((subsetSatisfiedCount T x : ℝ) - 1))) ≤
    infP p (monotoneDNF T) := by
  refine le_trans ?_ (infP_monotoneDNF_ge_unique_prob hp0 hp1 T L hL)
  apply mul_le_mul_of_nonneg_left
  · exact biasedProb_unique_ge_first_minus_factorial hp0 hp1 T
  · exact Nat.cast_nonneg _

/-- **Integrated Paley-Zygmund for `monotoneDNF`.** Combining the pointwise inequality
`Y - Y(Y-1) ≤ 1_{monotoneDNF = true}` with `biasedExpectation_sub` and
`biasedExpectation_indicator` gives:
`E_p[Y] - E_p[Y(Y-1)] ≤ Pr_p[monotoneDNF T = true]`. -/
lemma biasedProb_monotoneDNF_ge_first_minus_factorial
    {α : Type*} [Fintype α] [DecidableEq α]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T : Finset (Finset α)) :
    biasedExpectation p (fun x => (subsetSatisfiedCount T x : ℝ)) -
    biasedExpectation p (fun x =>
      (subsetSatisfiedCount T x : ℝ) * ((subsetSatisfiedCount T x : ℝ) - 1)) ≤
    biasedProb p (Finset.univ.filter (fun x : α → Bool => monotoneDNF T x = true)) := by
  rw [← biasedExpectation_sub]
  rw [← biasedExpectation_indicator]
  apply biasedExpectation_le_of_le hp0 hp1
  intros x
  rw [show ((if x ∈ Finset.univ.filter (fun x : α → Bool => monotoneDNF T x = true)
            then (1 : ℝ) else 0)) =
        (if monotoneDNF T x = true then (1 : ℝ) else 0) from ?_]
  · exact subsetSatisfiedCount_paley_zygmund T x
  · simp

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

/-- **Output bias of a Boolean function**: probability of true under uniform input. -/
noncomputable def outputBias {α : Type*} [Fintype α] [DecidableEq α]
    (G : (α → Bool) → Bool) : ℝ :=
  biasedProb (1/2 : ℝ)
    (Finset.univ.filter (fun x : α → Bool => G x = true))

/-- `outputBias G ∈ [0, 1]`. -/
lemma outputBias_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (G : (α → Bool) → Bool) : 0 ≤ outputBias G :=
  biasedProb_nonneg (by norm_num) (by norm_num) _

/-- `outputBias G ≤ 1`: count of true-inputs cannot exceed `2^|α|`. -/
lemma outputBias_le_one {α : Type*} [Fintype α] [DecidableEq α]
    (G : (α → Bool) → Bool) : outputBias G ≤ 1 := by
  unfold outputBias biasedProb
  rw [Finset.sum_congr rfl (fun x _ => biasedMeasure_half x), Finset.sum_const, nsmul_eq_mul,
      show ((1 : ℝ) / 2) ^ Fintype.card α = 1 / (2 : ℝ) ^ Fintype.card α from by
        rw [div_pow, one_pow], mul_one_div, div_le_one (by positivity)]
  have h := Finset.card_filter_le (Finset.univ : Finset (α → Bool)) (fun x => G x = true)
  rw [Finset.card_univ, card_cube] at h
  exact_mod_cast h

/-- Pointwise: `1_{monotoneDNF T = true} ≤ subsetSatisfiedCount T` (as reals). -/
lemma monotoneDNF_indicator_le_subsetSatisfiedCount
    {α : Type*} [Fintype α] [DecidableEq α] (T : Finset (Finset α)) (x : α → Bool) :
    (if x ∈ Finset.univ.filter (fun x : α → Bool => monotoneDNF T x = true)
        then (1 : ℝ) else 0) ≤ (subsetSatisfiedCount T x : ℝ) := by
  by_cases h : monotoneDNF T x = true
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, h, if_true]
    obtain ⟨S, hS, h_all⟩ := (monotoneDNF_eq_true_iff T x).mp h
    have : 1 ≤ subsetSatisfiedCount T x :=
      Nat.one_le_iff_ne_zero.mpr fun h_zero => by
        rw [subsetSatisfiedCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h_zero
        exact h_zero hS h_all
    exact_mod_cast this
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, h]
    exact_mod_cast Nat.zero_le _

/-- **Markov bound on `Pr[monotoneDNF = true]`** by `E[Y]`. -/
lemma biasedProb_monotoneDNF_le_first_moment
    {α : Type*} [Fintype α] [DecidableEq α] (T : Finset (Finset α))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    biasedProb p (Finset.univ.filter (fun x : α → Bool => monotoneDNF T x = true)) ≤
    ∑ S ∈ T, p ^ S.card := by
  rw [← biasedExpectation_indicator p, ← biasedExpectation_subsetSatisfiedCount]
  exact biasedExpectation_le_of_le hp0 hp1
    (monotoneDNF_indicator_le_subsetSatisfiedCount T)

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

/-! ## Helpers for the polynomial-graph construction -/

/-- **Helper**: `sensitivityAt F x` as a sum of indicators. -/
lemma sensitivityAt_cast_eq_sum_indicator
    {β : Type*} [Fintype β] [DecidableEq β]
    (F : (β → Bool) → Bool) (x : β → Bool) :
    (sensitivityAt F x : ℝ) =
      ∑ i : β, if F x ≠ F (flipBit x i) then (1 : ℝ) else 0 := by
  unfold sensitivityAt
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases h : F x ≠ F (flipBit x i) <;> simp [h]

/-- **Helper**: cast of weightedTotalSensitivity. -/
lemma weightedTotalSensitivity_cast_eq_sum
    {β : Type*} [Fintype β] [DecidableEq β]
    (F : (β → Bool) → Bool) (w : Bool → ℕ) :
    (weightedTotalSensitivity F w : ℝ) =
      ∑ i : β, ∑ t : β → Bool,
        (∏ k : β, (w (t k) : ℝ)) *
          (if F t ≠ F (flipBit t i) then (1 : ℝ) else 0) := by
  unfold weightedTotalSensitivity
  push_cast
  rfl

/-- **Helper**: biasedMeasure with `q = w_t / total` equals product weights / total^|β|. -/
lemma biasedMeasure_weight_ratio
    {β : Type*} [Fintype β] [DecidableEq β]
    (w : Bool → ℕ) (hW : 0 < (w true + w false : ℕ))
    (t : β → Bool) :
    biasedMeasure
        ((w true : ℝ) / ((w true + w false : ℕ) : ℝ)) t =
      (∏ k : β, (w (t k) : ℝ)) /
        (((w true + w false : ℕ) : ℝ) ^ Fintype.card β) := by
  classical
  set W : ℝ := ((w true + w false : ℕ) : ℝ) with hWdef
  have hWpos : 0 < W := by
    rw [hWdef]; exact_mod_cast hW
  rw [biasedMeasure_eq_prod]
  have h_point : ∀ k : β,
      (if t k = true then (w true : ℝ) / W
       else 1 - (w true : ℝ) / W) =
      (w (t k) : ℝ) / W := by
    intro k
    cases t k
    · simp; field_simp; rw [hWdef]; push_cast; ring
    · simp
  simp_rw [h_point]
  rw [Finset.prod_div_distrib]
  rw [Finset.prod_const, Finset.card_univ]

/-- (B1.1) **`biasedInfluence` ↔ `infP` connection**:
`biasedInfluence F w = infP (w_t / (w_t + w_f)) F`, when `w_t + w_f > 0`. -/
lemma biasedInfluence_eq_infP {β : Type*} [Fintype β] [DecidableEq β]
    (F : (β → Bool) → Bool) (w : Bool → ℕ) (h_pos : 0 < (w true + w false : ℕ)) :
    biasedInfluence F w =
    infP ((w true : ℝ) / ((w true + w false : ℕ) : ℝ)) F := by
  classical
  unfold biasedInfluence infP biasedExpectation
  rw [weightedTotalSensitivity_cast_eq_sum]
  simp_rw [biasedMeasure_weight_ratio w h_pos]
  simp_rw [sensitivityAt_cast_eq_sum_indicator]
  set W : ℝ := ((w true + w false : ℕ) : ℝ) with hWdef
  have hWpos : 0 < W := by rw [hWdef]; exact_mod_cast h_pos
  have hWpow : W ^ Fintype.card β ≠ 0 := by positivity
  rw [show (∑ i : β, ∑ t : β → Bool,
          (∏ k : β, (w (t k) : ℝ)) *
            (if F t ≠ F (flipBit t i) then (1 : ℝ) else 0)) /
        W ^ Fintype.card β =
        ∑ i : β, ∑ t : β → Bool,
          ((∏ k : β, (w (t k) : ℝ)) *
            (if F t ≠ F (flipBit t i) then (1 : ℝ) else 0)) /
            W ^ Fintype.card β from by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intros i _
    rw [Finset.sum_div]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro t _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  field_simp

/-- (B1.2.a) **Cardinality bijection via cmpl**: `|{x : dual f x = true}| = |{x : f x = false}|`. -/
lemma card_filter_dual_true_eq_card_filter_false
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : (α → Bool) → Bool) :
    ((Finset.univ : Finset (α → Bool)).filter
      (fun x => InfluenceSensitivity.dual f x = true)).card =
    ((Finset.univ : Finset (α → Bool)).filter (fun x => f x = false)).card := by
  refine Finset.card_bij (fun x _ => cmpl x) ?_
    (fun _ _ _ _ h => cmpl_injective h) ?_
  · intros x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      InfluenceSensitivity.dual] at hx ⊢
    cases hf : f (cmpl x) <;> simp_all
  · intros y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact ⟨cmpl y, by
      simp [Finset.mem_filter, InfluenceSensitivity.dual, cmpl_cmpl, hy], cmpl_cmpl y⟩

/-- (B1.2.b) **Output-bias is uniform-cardinality fraction**:
`outputBias g = #{x : g x = true} / 2^|α|`. -/
lemma outputBias_eq_card_div {α : Type*} [Fintype α] [DecidableEq α]
    (g : (α → Bool) → Bool) :
    outputBias g =
    (((Finset.univ : Finset (α → Bool)).filter (fun x => g x = true)).card : ℝ) *
    (1/2 : ℝ) ^ Fintype.card α := by
  unfold outputBias biasedProb
  rw [Finset.sum_congr rfl (fun x _ => biasedMeasure_half x)]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- (B1.2) **Output-bias of dual is one minus output-bias**: at p=1/2,
`outputBias (dual f) = 1 - outputBias f`. -/
lemma outputBias_dual_eq {α : Type*} [Fintype α] [DecidableEq α]
    (f : (α → Bool) → Bool) :
    outputBias (InfluenceSensitivity.dual f) = 1 - outputBias f := by
  rw [outputBias_eq_card_div, outputBias_eq_card_div,
      card_filter_dual_true_eq_card_filter_false]
  have h_split : ((Finset.univ.filter (fun x : α → Bool => f x = true)).card : ℝ) +
      (Finset.univ.filter (fun x : α → Bool => f x = false)).card =
      (2 : ℝ) ^ Fintype.card α := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (α → Bool))) (p := fun x => f x = true)
    rw [show ({a ∈ (Finset.univ : Finset (α → Bool)) | ¬ f a = true}) =
          Finset.univ.filter (fun x : α → Bool => f x = false) from by
        apply Finset.filter_congr; intros x _; cases f x <;> simp,
        Finset.card_univ, Fintype.card_fun, Fintype.card_bool] at h
    exact_mod_cast h
  have h_pow : (2 : ℝ) ^ Fintype.card α * (1 / 2 : ℝ) ^ Fintype.card α = 1 := by
    rw [div_pow, one_pow]; field_simp
  have := congrArg (· * (1 / 2 : ℝ) ^ Fintype.card α) h_split
  simp only [add_mul, h_pow] at this
  linarith

/-- **Count-ratio bridge**: the count_true / total ratio equals `outputBias G`. -/
lemma countAt_true_div_count_sum_eq_outputBias
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : (α → Bool) → Bool) :
    (((Finset.univ : Finset (α → Bool)).filter
        (fun x => G x = true)).card : ℝ) /
      ((((Finset.univ : Finset (α → Bool)).filter
          (fun x => G x = true)).card +
        ((Finset.univ : Finset (α → Bool)).filter
          (fun x => G x = false)).card : ℕ) : ℝ) =
    outputBias G := by
  classical
  rw [outputBias_eq_card_div]
  rw [countAt_partition_sum G]
  rw [Fintype.card_fun, Fintype.card_bool]
  push_cast
  rw [show (1 / 2 : ℝ) ^ Fintype.card α =
      1 / (2 : ℝ) ^ Fintype.card α from by
        rw [div_pow, one_pow]]
  ring

/-- **biasedInfluence at countAt G ↔ infP at outputBias G**. -/
lemma biasedInfluence_countAt_eq_infP_outputBias
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (F : (β → Bool) → Bool) (G : (α → Bool) → Bool) :
    biasedInfluence F
      (fun b : Bool =>
        ((Finset.univ : Finset (α → Bool)).filter (fun x => G x = b)).card) =
    infP (outputBias G) F := by
  classical
  have hpos :
      0 < (((Finset.univ : Finset (α → Bool)).filter (fun x => G x = true)).card +
            ((Finset.univ : Finset (α → Bool)).filter (fun x => G x = false)).card : ℕ) := by
    rw [countAt_partition_sum G]
    exact Fintype.card_pos
  rw [biasedInfluence_eq_infP F
    (fun b : Bool =>
      ((Finset.univ : Finset (α → Bool)).filter (fun x => G x = b)).card) hpos]
  rw [countAt_true_div_count_sum_eq_outputBias G]

/-- **Composition formula in `infP`/`outputBias` form**:
`Inf(F ∘ G) = Inf(G) · Inf_p F` where `p = outputBias G`. This is the clean
public form — it avoids exposing `weightedTotalSensitivity` and `biasedInfluence`. -/
theorem influence_compose_outputBias {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Nonempty α]
    (F : (β → Bool) → Bool) (G : (α → Bool) → Bool) :
    influence (InfluenceSensitivity.compose F G) =
    influence G * infP (outputBias G) F := by
  rw [influence_compose_general, biasedInfluence_countAt_eq_infP_outputBias]

/-- (B1) **Compose-influence formula** (polyGraph application): for monotone B
with `outputBias B = q`, and any monotone T,
`influence(compose T (dual B)) = influence B · infP (1 - q) T`. -/
lemma influence_compose_T_dual_B
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (T : ((α × α) → Bool) → Bool) (B : ((α × α) → Bool) → Bool) :
    influence (InfluenceSensitivity.compose T (InfluenceSensitivity.dual B)) =
    influence B * infP (1 - outputBias B) T := by
  rw [influence_compose_outputBias, influence_dual, outputBias_dual_eq]

/-- (B2) **Sensitivity bounds on `compose T (dual B)`** for monotone B, T. -/
lemma maxSensitivity_compose_T_dual_B
    {α : Type*} [Fintype α] [DecidableEq α]
    {T B : ((α × α) → Bool) → Bool}
    (hT : IsMonotone T) (hB : IsMonotone B) :
    maxSensitivity (InfluenceSensitivity.compose T (InfluenceSensitivity.dual B)) ≤
    max (maxSensitivityZero T * maxSensitivityOne B)
        (maxSensitivityOne T * maxSensitivityZero B) := by
  rw [maxSensitivity_compose hT hB.dual]
  rw [maxSensitivityZero_dual, maxSensitivityOne_dual]

/-- (B3) **Prime sequence with infinite reach**: there exists a sequence of
primes `Q_k → ∞` with `Q_k ≥ k`. -/
lemma exists_prime_seq_atTop :
    ∃ Q : ℕ → ℕ, (∀ k, (Q k).Prime) ∧
    Filter.Tendsto Q Filter.atTop Filter.atTop ∧
    ∀ k, k ≤ Q k := by
  classical
  refine ⟨fun k => (Nat.exists_infinite_primes k).choose,
    fun k => (Nat.exists_infinite_primes k).choose_spec.2, ?_,
    fun k => (Nat.exists_infinite_primes k).choose_spec.1⟩
  rw [Filter.tendsto_atTop_atTop]
  exact fun M => ⟨M, fun k hk => hk.trans (Nat.exists_infinite_primes k).choose_spec.1⟩

/-- **Composed block**: `composedBlock T B := compose T (dual B)`. -/
noncomputable def composedBlock
    {α : Type*} [Fintype α] [DecidableEq α]
    (T B : ((α × α) → Bool) → Bool) :
    (((α × α) × (α × α)) → Bool) → Bool :=
  InfluenceSensitivity.compose T (InfluenceSensitivity.dual B)

/-- **Composed block bounds**: assuming gadget bounds for B (at p=1/2) and T
(at p = 1 - outputBias B), the composed block has `Inf ≥ cT·cB·Q²` and `s ≤ Q³`. -/
lemma composedBlock_bounds
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {T B : ((α × α) → Bool) → Bool}
    {cT cB : ℝ} {Q : ℝ}
    (hTmono : IsMonotone T) (hBmono : IsMonotone B)
    (hTinf : cT * Q ≤ infP (1 - outputBias B) T)
    (hBinf : cB * Q ≤ infP (1 / 2 : ℝ) B)
    (hTs1 : (maxSensitivityOne T : ℝ) ≤ Q)
    (hTs0 : (maxSensitivityZero T : ℝ) ≤ Q ^ 2)
    (hBs1 : (maxSensitivityOne B : ℝ) ≤ Q)
    (hBs0 : (maxSensitivityZero B : ℝ) ≤ Q ^ 2)
    (_hcT : 0 ≤ cT) (hcB : 0 ≤ cB) (hQ_nonneg : 0 ≤ Q) :
    cT * cB * Q ^ 2 ≤ influence (composedBlock T B) ∧
    (maxSensitivity (composedBlock T B) : ℝ) ≤ Q ^ 3 := by
  have h_infP_nonneg : 0 ≤ infP (1 - outputBias B) T :=
    infP_nonneg (sub_nonneg.mpr (outputBias_le_one B))
      (by linarith [outputBias_nonneg B]) T
  refine ⟨?_, ?_⟩
  · unfold composedBlock
    rw [influence_compose_T_dual_B]
    have hBinf' : cB * Q ≤ influence B := infP_half_eq_influence B ▸ hBinf
    have h_mul : (cT * Q) * (cB * Q) ≤ infP (1 - outputBias B) T * influence B :=
      mul_le_mul hTinf hBinf' (by positivity) h_infP_nonneg
    nlinarith [h_mul, mul_comm (influence B) (infP (1 - outputBias B) T)]
  · unfold composedBlock
    have hs : (maxSensitivity (InfluenceSensitivity.compose T
                  (InfluenceSensitivity.dual B)) : ℝ) ≤
        (max (maxSensitivityZero T * maxSensitivityOne B)
            (maxSensitivityOne T * maxSensitivityZero B) : ℕ) := by
      exact_mod_cast maxSensitivity_compose_T_dual_B (α := α) hTmono hBmono
    refine hs.trans ?_
    push_cast
    refine max_le ?_ ?_ <;>
      nlinarith [hTs0, hTs1, hBs0, hBs1, sq_nonneg Q,
        Nat.cast_nonneg (α := ℝ) (maxSensitivityZero T),
        Nat.cast_nonneg (α := ℝ) (maxSensitivityOne T),
        Nat.cast_nonneg (α := ℝ) (maxSensitivityZero B),
        Nat.cast_nonneg (α := ℝ) (maxSensitivityOne B)]

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

/-- **Achievability summary.** For any `r ≤ 2/3`, the exponent `r` is
unconditionally achievable, and the universal upper bound `r ≤ 1` is sharp. -/
theorem achievability_summary :
    (∀ r : ℝ, r ≤ (2 / 3 : ℝ) → ExponentAchievable r) ∧
    (∀ r : ℝ, ExponentAchievable r → r ≤ 1) :=
  ⟨fun _ hr => ExponentAchievable.mono hr twoThirdsExponentAchievable_unconditional,
   fun _ hr => hr.le_one⟩

end InfluenceSensitivity

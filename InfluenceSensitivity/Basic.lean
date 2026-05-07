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


end InfluenceSensitivity

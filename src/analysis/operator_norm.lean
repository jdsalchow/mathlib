/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow
-/
import algebra.module
import analysis.bounded_linear_maps
import analysis.real data.real.basic
import algebra.pi_instances
import order.complete_lattice
import tactic.abel tactic.subtype_instance
import group_theory.subgroup
import tactic.squeeze

variables {k : Type*} 
variables {E : Type*} {F : Type*}

/- The space of bounded linear maps
 -
 - Define the set of bounded linear maps between normed spaces and show basic facts about it. In particular
 -
 - (*) define a set L(E,F) of bounded linear maps between k normed spaces,
 - (*) show that L(E,F) is a vector subspace of E → F,
 - (*) define the 'operator norm' on L(E,F) and show that it induces the structure of a normed space on L(E,F).
 -/

/- This section should move to 'algebra/module.lean'. It equips a subspace with its induced vector space structure. -/
section vector_space

/- This instance makes type class resolution work. I'm not sure why it doesn't otherwise.
 - In any case this shows that maps to a vector space form a vector space.
 -/
instance vector_space_of_functions (α : Type*) (k : Type*) (V : Type*)
  [discrete_field k] [add_comm_group V] [vector_space k V] : vector_space k (α → V) := pi.vector_space k

variables [discrete_field k] [add_comm_group E]

/-- A subset of a vector space is a subspace if it is an additive subgroup and closed under scalar multiplication. -/
class is_subspace (carrier : set E) [vector_space k E] extends is_add_subgroup carrier : Prop :=
(smul_mem : ∀ c {x}, x ∈ carrier → c • x ∈ carrier)

/-- A set with the property 'is_subspace' is an additive commutative group. -/
instance is_subspace.add_comm_group {S : set E} [vector_space k E] [is_subspace S] : add_comm_group S :=
by subtype_instance

/-- Define scalar multiplication a set with the 'is_subspace' property. -/
instance is_subspace.has_scalar {S : set E} [vector_space k E] [is_subspace S] : has_scalar k S :=
{smul := λ c x, ⟨c • x, is_subspace.smul_mem c x.2⟩}

/-- Show that a subset with the 'is_subspace' property carries a vector space structure. -/
instance is_subspace.vector_space {S : set E} [vs : vector_space k E] [is_subspace S] : vector_space k S :=
{ 
  smul_add := assume r x y, begin simp, congr', exact semimodule.smul_add r x y end,
  add_smul := assume r s x, begin cases x, unfold has_scalar.smul, congr', simp, exact semimodule.add_smul r s _ end,
  mul_smul := assume r s x, begin cases x, unfold has_scalar.smul, congr' 1, simp, exact semimodule.mul_smul _ _ _ end,
  one_smul := assume x, begin cases x, unfold has_scalar.smul, congr', simp end,
  zero_smul := assume x, begin cases x, unfold has_scalar.smul, congr', simp, unfold has_zero.zero end,
  smul_zero := assume r, begin unfold has_scalar.smul, congr', simp, unfold has_zero.zero end,
  ..is_subspace.has_scalar
}

end vector_space

/- Define the set of bounded linear maps, introduce the notation L(E,F) for the set of bounded linear maps.
 - Some parts of this should move to 'analysis/bounded_linear_map.lean', in particular the structural
 - stuff done in analogy to linear maps.
 -/
section bounded_linear_maps

variables [hnfk : normed_field k] [normed_space k E]  [normed_space k F]
include hnfk

-- move to bounded_linear_map.lean from here
/-- A bounded linear map is a linear map with a bound. -/
structure bounded_linear_map (E : Type*) (F : Type*) [normed_space k E] [normed_space k F]
  extends linear_map E F :=
(bound : ∃ M, M > 0 ∧ ∀ x : E, ∥ to_fun x ∥ ≤ M * ∥ x ∥)

instance : has_coe_to_fun $ bounded_linear_map E F := ⟨_, λf,f.to_fun⟩

theorem is_bounded_linear (f : bounded_linear_map E F) : is_bounded_linear_map f := {..f}

@[extensionality] theorem bounded.linear_map.ext {f g : bounded_linear_map E F} {H : ∀ x, f x = g x} : f = g :=
by cases f with flin bound_f; cases flin; cases g with glin bound_g; cases glin; congr'; exact funext H
-- move to bounded_linear_map.lean till here

def bounded_linear_maps (E : Type*) (F : Type*) [normed_space k E] [normed_space k F] : set (E → F) :=
is_bounded_linear_map

notation `L(` E `,` F `)` := bounded_linear_maps E F

/-- Coerce bounded linear maps to functions. -/
instance : has_coe_to_fun $ L(E,F) :=
{F := _, coe := (λ f, f.val)}

/-- Coerce terms of type L(E,F) to the structure 'bounded_linear_map E F'. -/
instance : has_coe (↥L(E,F)) (bounded_linear_map E F) :=
{coe := λ(A : L(E,F)), {to_fun := ⇑A ..A.property}}

@[extensionality] theorem ext {A B : L(E,F)} (H : ∀ x, A x = B x) : A = B :=
begin
  cases A with A hA,
  cases B with B hB,
  congr',
  exact funext H
end

instance : is_subspace L(E,F) := {
  smul_mem := assume c A, is_bounded_linear_map.smul c,
  neg_mem := assume f, is_bounded_linear_map.neg',
  add_mem := assume f g, is_bounded_linear_map.add,
  zero_mem := is_bounded_linear_map.zero
}

/-- Bounded linear maps are ... bounded -/
lemma exists_bound (A : L(E,F)) : ∃ c, c > 0 ∧ ∀ x : E, ∥A x∥ ≤ c * ∥x∥ := (A : bounded_linear_map E F).bound

/-- Bounded linear maps are conveniently bounded on the unit ball. -/
lemma exists_bound' (A : L(E,F)) : ∃ c, c > 0 ∧ ∀ x : E, ∥x∥ ≤ 1 → ∥A x∥ ≤ c :=
let ⟨c, _, H⟩ := exists_bound A in
exists.intro c ⟨‹c > 0›,
  assume x _,
  calc ∥A x∥ ≤ c * ∥x∥ : H x
        ... ≤ c * 1 : (mul_le_mul_left ‹c > 0›).mpr ‹∥x∥ ≤ 1›
        ... = c : mul_one c⟩

instance bounded_linear_maps.is_linear_map {A : L(E,F)} : is_linear_map A :=
let ⟨A_val, A_prop⟩ := A in
have is_bounded_linear_map A_val, from A_prop,
is_bounded_linear_map.to_is_linear_map ‹is_bounded_linear_map A_val›


-- the remaining lemmas should be in module.lean

lemma map_add (f : E → F) {x y : E} [h : is_linear_map f] : f (x + y) = f x + f y :=
linear_map.map_add (is_linear_map.mk' f h) x y

lemma map_smul (f : E → F) {c : k} {x : E} [h : is_linear_map f] : f (c • x) = c • f x :=
linear_map.map_smul (is_linear_map.mk' f h) c x 

lemma map_zero (f : E → F) [h : is_linear_map f] : f 0 = 0 :=
linear_map.map_zero $ is_linear_map.mk' f h

/-
@[simp] lemma map_neg (x : β) : f (- x) = - f x :=
by rw [← neg_one_smul, map_smul, neg_one_smul]

@[simp] lemma map_sub (x y : β) : f (x - y) = f x - f y :=
by simp [map_neg, map_add]

@[simp] lemma map_sum {ι} {t : finset ι} {g : ι → β} :
  f (t.sum g) = t.sum (λi, f (g i)) :=
(finset.sum_hom f f.map_zero f.add).symm
-/
end bounded_linear_maps

/- Now define the operator norm. We only do this for normed spaces over ℝ, since we need a
 - scalar multiplication with reals to prove that ∥A x∥ ≤ ∥A∥ * ∥x∥. It would be enough to
 - have a vector space over a normed field k with a real scalar multiplication and certain
 - compatibility conditions.
 -
 - The main task is to show that the operator norm is definite, homogeneous, and satisfies the
 - triangle inequality. This is done after a few preliminary lemmas necessary to deal with cSup.
 -/
section operator_norm

variables [normed_space ℝ E] [normed_space ℝ F]
open lattice set

/-- The operator norm of a bounded linear map A : E → F is the sup of
 - the set ∥A x∥ with ∥x∥ = 1. If E = {0} we set ∥A∥ = 0.
 -/
noncomputable def operator_norm : L(E, F) → ℝ :=
assume A, Sup (image (λ x, ∥A x∥) {x | ∥x∥ ≤ 1})

noncomputable instance : has_norm L(E,F) :=
{norm := operator_norm}

lemma norm_of_unit_ball_bdd_above (A : L(E,F)) : bdd_above (image (norm ∘ A) {x | ∥x∥ ≤ 1}) :=
let ⟨c, _, H⟩ := (exists_bound' A : ∃ c, c > 0 ∧ ∀ x : E, ∥x∥ ≤ 1 → ∥A x∥ ≤ c) in
bdd_above.mk c
  (assume r ⟨x, (_ : ∥x∥ ≤ 1), (_ : ∥A x∥ = r)⟩,
    show r ≤ c, from 
      calc r = ∥A x∥ : eq.symm ‹∥A x∥ = r›
         ... ≤ c : H x ‹∥x∥ ≤ 1›)

lemma zero_in_im_ball (A : L(E,F)) : (0:ℝ) ∈ {r : ℝ | ∃ (x : E), ∥x∥ ≤ 1 ∧ ∥A x∥ = r} :=
exists.intro (0:E) $ and.intro (by rw[norm_zero]; exact zero_le_one) (by rw[map_zero A]; simp)

lemma operator_norm_nonneg (A : L(E,F)) : 0 ≤ ∥A∥ :=
have (0:ℝ) ∈ _, from zero_in_im_ball A,
suffices 0 ≤ Sup (image (norm ∘ A) {x | ∥x∥ ≤ 1}), by assumption,
let ⟨c, _, H⟩ := (exists_bound' A : ∃ c, c > 0 ∧ ∀ x : E, ∥x∥ ≤ 1 → ∥A x∥ ≤ c) in
le_cSup (norm_of_unit_ball_bdd_above A) ‹(0:ℝ) ∈ _›

lemma bounded_by_operator_norm_on_unit_vector (A : L(E, F)) {x : E} (_ : ∥x∥ = 1) : ∥A x∥ ≤ ∥A∥ :=
suffices ∥A x∥ ≤ Sup (image (norm ∘ A) {x | ∥x∥ ≤ 1}), by assumption,
let ⟨c, _, _⟩ := (exists_bound A : ∃ c, c > 0 ∧ ∀ x : E, ∥ A x ∥ ≤ c * ∥ x ∥) in
have ∥A x∥ ∈ (image (norm ∘ A) {x | ∥x∥ ≤ 1}), from exists.intro x ⟨le_of_eq ‹∥x∥ = 1›, rfl⟩,
le_cSup (norm_of_unit_ball_bdd_above A) ‹∥A x∥ ∈ _›

/-- This is the fundamental property of the operator norm: ∥A x∥ ≤ ∥A∥ * ∥x∥. -/
theorem bounded_by_operator_norm {A : L(E,F)} {x : E} : ∥A x∥ ≤ ∥A∥ * ∥x∥ :=
classical.by_cases
  (assume : x = (0:E),
    calc ∥A x∥ ≤ 0 : by rw[‹x = 0›, map_zero A, norm_zero]; exact le_refl 0
          ... = ∥A∥ * ∥x∥ : by rw[‹x = 0›, norm_zero, mul_zero])
  (assume : x ≠ (0:E),
    have ∥x∥ ≠ 0, from ne_of_gt $ (norm_pos_iff x).mpr ‹x ≠ 0›,
    have ∥∥x∥⁻¹∥ = ∥x∥⁻¹, from abs_of_nonneg $ inv_nonneg.mpr $ norm_nonneg x,
    have ∥∥x∥⁻¹•x∥ = 1, begin rw[norm_smul, ‹∥∥x∥⁻¹∥ = ∥x∥⁻¹›], exact inv_mul_cancel ‹∥x∥ ≠ 0› end,
    calc ∥A x∥ = (∥x∥ * ∥x∥⁻¹) * ∥A x∥ : by rw[mul_inv_cancel ‹∥x∥ ≠ 0›]; ring 
          ... = ∥∥x∥⁻¹∥ * ∥A x∥ * ∥x∥ : by rw[‹∥∥x∥⁻¹∥ = ∥x∥⁻¹›]; ring 
          ... = ∥∥x∥⁻¹• A x ∥ * ∥x∥ : by rw[←normed_space.norm_smul ∥x∥⁻¹ (A x)]
          ... = ∥A (∥x∥⁻¹• x)∥ * ∥x∥ : by rw[map_smul A]
          ... ≤ ∥A∥ * ∥x∥ : (mul_le_mul_right ((norm_pos_iff x).mpr ‹x ≠ 0›)).mpr (bounded_by_operator_norm_on_unit_vector A ‹∥∥x∥⁻¹•x∥ = 1›))

lemma bounded_by_operator_norm_on_unit_ball (A : L(E, F)) {x : E} (_ : ∥x∥ ≤ 1) : ∥A x∥ ≤ ∥A∥ :=
calc ∥A x∥ ≤ ∥A∥ * ∥x∥ : bounded_by_operator_norm 
        ... ≤ ∥A∥ * 1 : mul_le_mul_of_nonneg_left ‹∥x∥ ≤ 1› (operator_norm_nonneg A)
        ... = ∥A∥ : mul_one ∥A∥

lemma bounded_by_operator_norm' (A : L(E,F)) (x : E) : ∥A x∥ ≤ ∥A∥ * ∥x∥ :=
@bounded_by_operator_norm _ _ _ _ A x


lemma operator_norm_bounded_by {A : L(E,F)} (c : nnreal) : (∀ x : E, ∥x∥ ≤ 1 → ∥A x∥ ≤ (c:ℝ)) → ∥A∥ ≤ c :=
assume H : ∀ x : E, ∥x∥ ≤ 1 → ∥A x∥ ≤ c,
suffices Sup (image (norm ∘ A) {x | ∥x∥ ≤ 1}) ≤ c, by assumption,
cSup_le (set.ne_empty_of_mem $ zero_in_im_ball A) 
  (show ∀ (r : ℝ), r ∈ (image (norm ∘ A) {x | ∥x∥ ≤ 1}) → r ≤ c, from 
    assume r ⟨x, _, _⟩, 
      calc r = ∥A x∥ : eq.symm ‹_›
         ... ≤ c : H x ‹_›)

set_option class.instance_max_depth 33

theorem operator_norm_triangle (A : L(E,F)) (B : L(E,F)) : ∥A + B∥ ≤ ∥A∥ + ∥B∥ :=
operator_norm_bounded_by (⟨∥A∥, operator_norm_nonneg A⟩ + ⟨∥B∥, operator_norm_nonneg B⟩)
  (assume x _,
    calc ∥(A + B) x∥ = ∥A x + B x∥ : rfl
                ... ≤ ∥A x∥ + ∥B x∥ : norm_triangle _ _
                ... ≤ ∥A∥ + ∥B∥ : add_le_add (bounded_by_operator_norm_on_unit_ball A ‹_›)
                                            (bounded_by_operator_norm_on_unit_ball B ‹_›))

theorem operator_norm_zero_iff (A : L(E,F)) : A = 0 ↔ ∥A∥ = 0:=
iff.intro
  (assume : A = 0,
    let M := {r : ℝ | ∃ (x : E), ∥x∥ ≤ 1 ∧ ∥A x∥ = r} in
    -- note that we have M = (image (norm ∘ A) {x | ∥x∥ ≤ 1}), from rfl
    suffices Sup M = 0, by assumption,
    suffices M = {0}, by rw[this]; exact cSup_singleton 0,
    (set.ext_iff M {0}).mpr $ assume r, iff.intro
      (assume : ∃ (x : E), ∥x∥ ≤ 1 ∧ ∥A x∥ = r,
        let ⟨x, _, _⟩ := this in
            have h : ∥(0:F)∥ = r, by rwa[‹A=0›] at *, by finish)
      (assume : r ∈ {0},
        have r = 0, from set.eq_of_mem_singleton this,
        exists.intro (0:E) $ and.intro (by rw[norm_zero]; exact zero_le_one) (by rw[this, map_zero A]; simp)))
  (assume : ∥A∥ = 0,
    suffices ∀ x, A x = 0, from ext this,
    assume x,
      have ∥A x∥ ≤ 0, from 
        calc ∥A x∥ ≤ ∥A∥ * ∥x∥ : bounded_by_operator_norm
              ... = 0 : by rw[‹∥A∥ = 0›]; ring,
      (norm_le_zero_iff (A x)).mp this)


local attribute[instance] classical.prop_decidable

/-- To show that the supremum of a non-empty subset S of ℝ that is bounded from above has suprerum b, we have
 - to check that
 - 1) b is a upper bound
 - 2) every other upper bound b' of is satisfies b ≤ b'.
 - This is different from the genereal case: we use that ℝ is totally ordered. The theorem hold in this
 - generality, but we only need this special case.
 -/
theorem real.cSup_intro {s : set ℝ} {b : ℝ} (_ : s ≠ ∅)
  (_ : ∀ a ∈ s, a ≤ b) (H : ∀ub, (∀ a ∈ s, a ≤ ub) → (b ≤ ub)) : Sup s = b :=
suffices ∀w, w < b → (∃a∈s, w < a), from cSup_intro ‹s ≠ ∅› ‹∀a∈s, a ≤ b› this,
assume w _, 
  suffices ¬∀a∈s, w ≥ a, from 
    let ⟨a, (h : ¬(a ∈ s → w ≥ a))⟩ := not_forall.mp this in
    have a ∈ s, from (not_imp.mp h).1,
    have w < a, from lt_of_not_ge (not_imp.mp h).2,
    show ∃ a ∈ s, w < a, from ⟨a, ‹a ∈ s›, ‹w < a›⟩,
  assume : ∀a∈s, w ≥ a,
    absurd
      (show b ≤ w, from H w this)
      (not_le_of_lt ‹w < b›)


theorem operator_norm_homogeneous (c : ℝ) (A : L(E, F)) : ∥c • A∥ = ∥c∥ * ∥A∥ :=
-- ∥c • A∥ is the supremum of the image of the map x ↦ ∥c • A x∥ on the unit ball in E
-- we show that this is the same as ∥c∥ * ∥A∥ by showing 1) and 2):
-- 1) ∥c∥ * ∥A∥ is an upper bound for the image of x ↦ ∥c • A x∥ on the unit ball
-- 2) any w < ∥c∥ * ∥A∥ is not an upper bound (this is equivalent to showing that every upper bound is ≥ ∥c∥ * ∥A∥)
suffices (∀ a ∈ _, a ≤ ∥c∥ * ∥A∥) ∧ (∀ (ub : ℝ), (∀ a ∈ _, a ≤ ub) → ∥c∥ * ∥A∥ ≤ ub), from
    real.cSup_intro (show _ ≠ ∅, from set.ne_empty_of_mem $ zero_in_im_ball _) this.1 this.2,
and.intro
  (show ∀ a ∈ image (λ x, ∥(c • A) x∥) {x : E | ∥x∥ ≤ 1}, a ≤ ∥c∥ * ∥A∥, from
    assume a (hₐ : ∃ (x : E), ∥x∥ ≤ 1 ∧ ∥(c • A) x∥ = a), 
      let ⟨x, _, _⟩ := hₐ in
        calc a = ∥c • A x∥    : eq.symm ‹_›
           ... = ∥c∥ * ∥A x∥   : by rw[←norm_smul c (A x)]; refl
           ... ≤ ∥c∥ * ∥A∥     :  mul_le_mul_of_nonneg_left (bounded_by_operator_norm_on_unit_ball A ‹∥x∥ ≤ 1›) (norm_nonneg c))
  (show ∀ (ub : ℝ), (∀ a ∈ image (λ (x : E), ∥(c • A) x∥) {x : E | ∥x∥ ≤ 1}, a ≤ ub) → ∥c∥ * ∥A∥ ≤ ub, from
    assume u u_is_ub,
      classical.by_cases
        (assume : c = 0,
          calc ∥c∥ * ∥A∥ = 0 : by rw[‹c=0›, norm_zero, zero_mul]
                    ... ≤ u : u_is_ub (0:ℝ) $ zero_in_im_ball _)
        (assume : c ≠ 0,
          have ∥c∥ ≠ 0, from ne_of_gt $ (norm_pos_iff c).mpr ‹c ≠ 0›,
          have bla : u = ∥c∥ * (∥c∥⁻¹ * u), by rw[←mul_assoc, mul_inv_cancel ‹∥c∥ ≠ 0›, one_mul],
          suffices ∥A∥ ≤ ∥c∥⁻¹ * u, from
            have u = ∥c∥ * (∥c∥⁻¹ * u), by rw[←mul_assoc, mul_inv_cancel ‹∥c∥ ≠ 0›, one_mul],
            by rw[this]; exact mul_le_mul_of_nonneg_left ‹_› (norm_nonneg c),
          cSup_le
            (set.ne_empty_of_mem $ zero_in_im_ball _)
            (assume n (H : ∃ (x : E), ∥x∥ ≤ 1 ∧ ∥A x∥ = n),
              let ⟨x, _, _⟩ := H in 
              calc n = ∥A x∥ : eq.symm ‹∥A x∥ = n›
                 ... = ∥c∥⁻¹ * ∥c • A x∥ : by rw[norm_smul, ←mul_assoc, inv_mul_cancel ‹∥c∥ ≠ 0›, one_mul]
                 ... ≤ ∥c∥⁻¹ * u : mul_le_mul_of_nonneg_left (u_is_ub ∥c • A x∥ ⟨x, ‹∥x∥ ≤ 1›, rfl⟩) $ inv_nonneg.mpr $ norm_nonneg c)))

-- move to normed_space.lean from here, note that we don't assume k=ℝ here
/-- A normed space can be build from a norm that satisfies algebraic properties. This is formalised in this structure. -/
structure normed_space.core (k : Type*) (E : Type*)
  [out_param $ discrete_field k] [normed_field k] [add_comm_group E] [has_scalar k E] [has_norm E]:=
(definite : ∀ x : E, x = 0 ↔ ∥x∥ = 0)
(homogeneous : ∀ c : k, ∀ x : E, ∥c • x∥ = ∥c∥ * ∥x∥)
(triangle : ∀ x y : E, ∥x + y∥ ≤ ∥x∥ + ∥y∥)

noncomputable def normed_space.of_core (k : Type*) (E : Type*)
  [normed_field k] [add_comm_group E] [vector_space k E] [has_norm E] (C : normed_space.core k E) : normed_space k E :=
begin
  exact {
    dist := λ x y, ∥x - y∥,
    dist_eq := assume x y, by refl,
    dist_self := assume x, (C.definite (x - x)).mp (show x - x = 0, by simp),
    eq_of_dist_eq_zero := assume x y h, show (x = y), from sub_eq_zero.mp $ (C.definite (x - y)).mpr h,
    dist_triangle := assume x y z,
      calc ∥x - z∥ = ∥x - y + (y - z)∥ : by simp
              ... ≤ ∥x - y∥ + ∥y - z∥  : C.triangle _ _,
    dist_comm := assume x y,
      calc ∥x - y∥ = ∥ -(1 : k) • (y - x)∥ : by simp
               ... = ∥y - x∥ : begin rw[C.homogeneous], simp end,
    norm_smul := C.homogeneous
  }
end
-- move to normed_space.lean till here

/-- Expose L(E,F) equipped with the operator norm as normed space. -/
noncomputable instance : normed_space ℝ L(E,F) :=
normed_space.of_core ℝ L(E,F) {
  definite := operator_norm_zero_iff,
  homogeneous := operator_norm_homogeneous,
  triangle := operator_norm_triangle
}

end operator_norm


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

instance vector_space_of_functions (α : Type*) (k : Type*) (V : Type*)
  [discrete_field k] [add_comm_group V] [vector_space k V] : vector_space k (α → V) := pi.vector_space k

class is_subspace (carrier : set E) [discrete_field k] [add_comm_group E] [vector_space k E] extends is_add_subgroup carrier : Prop :=
(smul_mem : ∀ c {x}, x ∈ carrier → c • x ∈ carrier)

instance is_subspace.add_comm_group {S : set E} [discrete_field k] [add_comm_group E] [vector_space k E] [is_subspace S] : add_comm_group S :=
by subtype_instance

instance is_subspace.has_scalar {S : set E} [discrete_field k] [add_comm_group E] [vector_space k E] [is_subspace S] : has_scalar k S :=
{smul := λ c x, ⟨c • x, is_subspace.smul_mem c x.2⟩}

instance is_subspace.vector_space {S : set E} [discrete_field k] [add_comm_group E] [vs : vector_space k E] [is_subspace S] : vector_space k S :=
{ 
  smul_add := assume r x y, begin simp, congr', exact semimodule.smul_add r x y end,
  add_smul := assume r s x, begin cases x, unfold has_scalar.smul, congr', simp, exact semimodule.add_smul r s _ end,
  mul_smul := assume r s x, begin cases x, unfold has_scalar.smul, congr' 1, simp, exact semimodule.mul_smul _ _ _ end,
  one_smul := assume x, begin cases x, unfold has_scalar.smul, congr', simp end,
  zero_smul := assume x, begin cases x, unfold has_scalar.smul, congr', simp, unfold has_zero.zero end,
  smul_zero := assume r, begin unfold has_scalar.smul, congr', simp, unfold has_zero.zero end,
  ..is_subspace.has_scalar
}

section bounded_linear_maps

variable [hnfk : normed_field k]

include hnfk

variables [normed_space k E]
variables [normed_space k F]

structure bounded_linear_map (E : Type*) (F : Type*) [normed_space k E] [normed_space k F]
  extends linear_map E F :=
(bound : ∃ M, M > 0 ∧ ∀ x : E, ∥ to_fun x ∥ ≤ M * ∥ x ∥)

instance : has_coe_to_fun $ bounded_linear_map E F := ⟨_, λf,f.to_fun⟩

theorem is_bounded_linear (f : bounded_linear_map E F) : is_bounded_linear_map f := {..f}

@[extensionality] theorem ext {f g : bounded_linear_map E F} {H : ∀ x, f x = g x} : f = g :=
by cases f with flin bound_f; cases flin; cases g with glin bound_g; cases glin; congr'; exact funext H




def bounded_linear_maps (E : Type*) (F : Type*) [normed_group E] [normed_space k E] [normed_group F] [normed_space k F] : set (E → F) :=
  is_bounded_linear_map

notation `L(` E `,` F `)` := bounded_linear_maps E F


instance : has_coe_to_fun $ bounded_linear_maps E F :=
{F := _, coe := (λ f, f.val)}

instance : has_coe (↥(bounded_linear_maps E F)) (bounded_linear_map E F) :=
{coe := λ(L : bounded_linear_maps E F), {to_fun := ⇑L ..L.property}}


@[extensionality] theorem bounded_linear_maps.ext {A B : bounded_linear_maps E F} (H : ∀ x, A x = B x) : A = B :=
begin
  cases A with A hA,
  cases B with B hB,
  congr',
  exact funext H
end


instance bounded_linear_maps.is_linear_map {A : L(E,F)} : is_linear_map A :=
let ⟨A_val, A_prop⟩ := A in
have is_bounded_linear_map A_val, from A_prop,
is_bounded_linear_map.to_is_linear_map ‹is_bounded_linear_map A_val›

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


--instance : has_coe (bounded_linear_map E F) (linear_map E F) :=
--{coe := λ(L : bounded_linear_map E F), L.to_linear_map}

lemma exists_bound (L : bounded_linear_maps E F) : 
  ∃ c, c > 0 ∧ ∀ x : E, ∥ L x ∥ ≤ c * ∥ x ∥ :=
(L : bounded_linear_map E F).bound

lemma exists_bound' (L : bounded_linear_maps E F) : 
  ∃ c, c > 0 ∧ ∀ x : E, ∥x∥ ≤ 1 →  ∥ L x ∥ ≤ c :=
let ⟨c, _, H⟩ := exists_bound L in
exists.intro c ⟨‹c > 0›,
  assume x _,
  calc ∥L x∥ ≤ c * ∥x∥ : H x
        ... ≤ c * 1 : (mul_le_mul_left ‹c > 0›).mpr ‹∥x∥ ≤ 1›
        ... = c : mul_one c⟩


instance : is_subspace (bounded_linear_maps E F) := {
  smul_mem := assume c A, is_bounded_linear_map.smul c,
  neg_mem := assume f, is_bounded_linear_map.neg',
  add_mem := assume f g, is_bounded_linear_map.add,
  zero_mem := is_bounded_linear_map.zero
}

end bounded_linear_maps

section real_normed_spaces

variables [normed_space ℝ E]
variables [normed_space ℝ F]

open lattice set

lemma norm_of_unit_ball_bdd_above (A : L(E,F)) : bdd_above (image (λ x, ∥A x∥) {x | ∥x∥ ≤ 1}) :=
let M := {r : ℝ | r = 0 ∨ ∃ x, ∥x∥ = 1 ∧ ∥A x∥ = r},
    ⟨c, _, H⟩ := (exists_bound' A : ∃ c, c > 0 ∧ ∀ x : E, ∥x∥ ≤ 1 → ∥A x∥ ≤ c) in
bdd_above.mk c
  (assume r ⟨x, (_ : ∥x∥ ≤ 1), (_ : ∥A x∥ = r)⟩,
    show r ≤ c, from 
      calc r = ∥A x∥ : eq.symm ‹∥A x∥ = r›
         ... ≤ c : H x ‹∥x∥ ≤ 1›)

/- The operator norm of a bounded linear map A: E → F is the sup of
 - the set ∥A x∥ with ∥x∥ = 1. If E = {0} we set ∥A∥ = 0.
 -/
noncomputable def op_norm : L(E, F) → ℝ := 
assume A, Sup { r : ℝ | r = 0 ∨ ∃ x, ∥x∥ = 1 ∧ ∥A x∥ = r }

noncomputable def operator_norm : L(E, F) → ℝ :=
assume A, Sup (image (λ x, ∥A x∥) {x | ∥x∥ ≤ 1})

noncomputable instance : has_norm L(E,F) :=
{norm := operator_norm}

lemma operator_norm_nonneg (A : L(E,F)) : 0 ≤ ∥A∥ :=
let M := {r : ℝ |  ∃ (x : E), ∥x∥ ≤ 1 ∧ ∥A x∥ = r} in
have (0:ℝ) ∈ M, from exists.intro (0:E) $ and.intro (by rw[norm_zero]; exact zero_le_one) (by rw[map_zero A]; simp),
suffices 0 ≤ Sup M, by assumption,
let ⟨c, _, H⟩ := (exists_bound' A : ∃ c, c > 0 ∧ ∀ x : E, ∥x∥ ≤ 1 → ∥A x∥ ≤ c) in
le_cSup (norm_of_unit_ball_bdd_above A) ‹(0:ℝ) ∈ M›

lemma bounded_by_operator_norm_on_unit_vector (A : L(E, F)) {x : E} (_ : ∥x∥ = 1) : ∥A x∥ ≤ ∥A∥ :=
let M := (image (λ x, ∥A x∥) {x | ∥x∥ ≤ 1}) in
suffices ∥A x∥ ≤ Sup M, by assumption,
let ⟨c, _, _⟩ := (exists_bound A : ∃ c, c > 0 ∧ ∀ x : E, ∥ A x ∥ ≤ c * ∥ x ∥) in
have ∥A x∥ ∈ M, from exists.intro x ⟨le_of_eq ‹∥x∥ = 1›, rfl⟩,
le_cSup (norm_of_unit_ball_bdd_above A) ‹∥A x∥ ∈ M›

lemma bounded_by_operator_norm {A : L(E,F)} {x : E} : ∥A x∥ ≤ ∥A∥ * ∥x∥ :=
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
let M := {r : ℝ |  ∃ (x : E), ∥x∥ ≤ 1 ∧ ∥A x∥ = r} in
have (0:ℝ) ∈ M, from exists.intro (0:E) $ and.intro (by rw[norm_zero]; exact zero_le_one) (by rw[map_zero A]; simp),
suffices Sup M ≤ c, by assumption,
cSup_le (set.ne_empty_of_mem ‹(0:ℝ) ∈ M›) 
  (show ∀ (r : ℝ), r ∈ M → r ≤ c, from 
    assume r ⟨x, _, _⟩, 
      calc r = ∥A x∥ : eq.symm ‹_›
         ... ≤ c : H x ‹_›)

set_option class.instance_max_depth 48

lemma operator_norm_triangle (A : L(E,F)) (B : L(E,F)) : ∥A + B∥ ≤ ∥A∥ + ∥B∥ :=
operator_norm_bounded_by (⟨∥A∥, operator_norm_nonneg A⟩ + ⟨∥B∥, operator_norm_nonneg B⟩)
  (assume x _,
    calc ∥(A + B) x∥ = ∥A x + B x∥ : rfl
                ... ≤ ∥A x∥ + ∥B x∥ : norm_triangle _ _
                ... ≤ ∥A∥ + ∥B∥ : add_le_add (bounded_by_operator_norm_on_unit_ball A ‹_›)
                                            (bounded_by_operator_norm_on_unit_ball B ‹_›))

theorem compare_indexed_cSup {α : Type*} {ι : Type*} [conditionally_complete_lattice α]
  {I : set ι} {s : ι → α} {t : ι → α} (h : ∀ i ∈ I, s i ≤ t i) 
  (_ : image s I ≠ ∅) (_ : bdd_above (t '' I)): (Sup $ image s I) ≤ (Sup $ image t I) :=
have ∀ i ∈ I, s i ≤ Sup (t '' I), from
  assume i _, le_trans (h i ‹i ∈ I›) $ le_cSup ‹bdd_above (t '' I)› ⟨i, ‹i ∈ I›, rfl⟩,
show Sup (s '' I) ≤ Sup (t '' I), from
  cSup_le ‹s '' I ≠ ∅› $ assume a,
    show a ∈ s '' I → a ≤ Sup (t '' I), from
      assume ⟨i, _, (_ : s i = a)⟩,
        calc a = s i : eq.symm ‹_›
           ... ≤ Sup (t '' I) : this i ‹i ∈ I›

lemma operator_norm_zero_iff (A : L(E,F)) : A = 0 ↔ ∥A∥ = 0:=
iff.intro
  (assume : A = 0,
    let M := {r : ℝ | ∃ (x : E), ∥x∥ ≤ 1 ∧ ∥A x∥ = r} in
    suffices Sup M = 0, by assumption,
    suffices M = {0}, by rw[this]; exact cSup_singleton 0,
    (set.ext_iff M {0}).mpr $ assume r, iff.intro
      (assume : ∃ (x : E), ∥x∥ ≤ 1 ∧ ∥A x∥ = r,
            let ⟨x, _, _⟩ := this in
            have h : ∥(0:F)∥ = r, by rwa[‹A=0›] at *,
            by finish)
      (assume : r ∈ {0},
        have r = 0, from set.eq_of_mem_singleton this,
        exists.intro (0:E) $ and.intro (by rw[norm_zero]; exact zero_le_one) (by rw[this, map_zero A]; simp)))
  (assume : ∥A∥ = 0,
    suffices ∀ x, A x = 0, from bounded_linear_maps.ext this,
    assume x,
      have ∥A x∥ ≤ 0, from 
        calc ∥A x∥ ≤ ∥A∥ * ∥x∥ : bounded_by_operator_norm
              ... = 0 : by rw[‹∥A∥ = 0›]; ring,
      (norm_le_zero_iff (A x)).mp this)

lemma operator_norm_homogeneous (c : ℝ) (A : L(E, F)) : ∥c • A∥ = ∥c∥ * ∥A∥ :=
have ∀ x, ∥(c • A) x∥ = ∥c∥ * ∥A x∥, from assume x, norm_smul c (A x),
have ∥c • A∥ ≤ ∥c∥ * ∥A∥, from operator_norm_bounded_by (⟨∥c∥, norm_nonneg c⟩ * ⟨∥A∥, operator_norm_nonneg A⟩)
  (assume x _,
    calc ∥(c • A)x∥ = ∥c∥ * ∥A x∥       : by rw[←norm_smul c (A x)]; refl
               ... ≤ ∥c∥ * ∥A∥          :  mul_le_mul_of_nonneg_left (bounded_by_operator_norm_on_unit_ball A ‹∥x∥ ≤ 1›) (norm_nonneg c)
               ... = (⟨∥c∥, norm_nonneg _⟩ * ⟨∥A∥, operator_norm_nonneg _⟩ : nnreal) : rfl),
have ∀ x, ∥(c • A) x∥ = ∥c∥ * ∥A x∥, from assume x, norm_smul c (A x),
have ∥c∥ * ∥A∥ ≤ ∥c • A∥, from
  classical.by_cases
    (assume : c = 0,
      calc ∥c∥ * ∥A∥ = 0 : by rw[‹c=0›, norm_zero]; simp
                ... ≤ ∥c • A∥ : operator_norm_nonneg $ c • A)
    (assume : c ≠ 0, 
      have ∀ x, ∥x∥ ≤ 1 → ∥A∥ ≤ ∥c∥⁻¹ * ∥c • A x∥, from assume x _,        
        let s : E → ℝ := λ x, ∥c∥⁻¹ * ∥c • A x∥,
            t : E → ℝ := λ x, ∥A x∥,
            I := {x : E | ∥x∥ ≤ 1} in
  have ∀ x ∈ {x : E | ∥x∥ ≤ 1}, ∥A x∥ ≤ ∥c∥⁻¹ * ∥c • A∥, from sorry,
  have ∥A∥ ≤ ∥c∥⁻¹ * ∥c • A∥, from cSup_le sorry (show ∀ r ∈ t '' {x :E | ∥x∥ ≤ 1}, r ≤ ∥c∥⁻¹ * ∥c • A∥, from sorry),
  sorry),
  
show ∥c • A∥ = ∥c∥ * ∥A∥, from
  partial_order.le_antisymm _ _ ‹∥c • A∥ ≤ ∥c∥ * ∥A∥› ‹∥c∥ * ∥A∥ ≤ ∥c • A∥›

structure normed_space.core (k : Type*) (E : Type*)
  [out_param $ discrete_field k] [normed_field k] [add_comm_group E] [has_scalar k E] [has_norm E]:=
(definite : ∀ x : E, x = 0 ↔ ∥x∥ = 0)
(homogeneous : ∀ c : k, ∀ x : E, ∥c • x∥ = ∥c∥ * ∥x∥)
(triangle : ∀ x y : E, ∥x + y∥ ≤ ∥x∥ + ∥y∥)

def normed_space.of_core (k : Type*) (E : Type*)
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

noncomputable instance : normed_space ℝ L(E,F) :=
normed_space.of_core ℝ L(E,F) {
  definite := operator_norm_zero_iff,
  homogeneous := operator_norm_homogeneous,
  triangle := operator_norm_triangle
}

end real_normed_spaces

import analysis.asymptotics .deriv .operator_norm topology.metric_space.lipschitz

variables {E : Type*} [normed_space ℝ E]
variables {F : Type*} [normed_space ℝ F]
variables {G : Type*} [normed_space ℝ G]

open topological_space function

local notation `L(` E `,` F `)` := @bounded_linear_maps _ E F _ _ _

def is_differentiable (f : E → F) : Prop := ∀ x : E, ∃ Dfx : L(E, F), has_fderiv_at f Dfx x

noncomputable def differentiable_maps (E : Type*) [normed_space ℝ E] (F : Type*) [normed_space ℝ F] : subspace ℝ (E → F) :=
{ carrier := {f : E → F | is_differentiable f},
  zero := assume x, ⟨(0:L(E,F)), has_fderiv_at_const 0 x⟩,
  add := assume f g hf hg x,
         let ⟨Dfx, _⟩ := hf x, ⟨Dgx, _⟩ := hg x in
           exists.intro (Dfx + Dgx) (has_fderiv_at_add ‹_› ‹_›),
  smul := assume c f hf x,
          let ⟨Dfx, _⟩ := hf x in
            exists.intro (c • Dfx) (has_fderiv_at_smul c ‹_›)}

instance differentiable_maps.to_fun : has_coe_to_fun $ differentiable_maps E F :=
{F := λ _, (E → F), coe := (λ f, f.val)}


noncomputable def D : differentiable_maps E F → E → L(E,F) :=
assume f, λ x , classical.some (f.property x)


def posreal := {r : ℝ // 0 < r}
local notation ` ℝ>0 ` := posreal

section posreal
instance : has_coe ℝ>0 ℝ := ⟨subtype.val⟩

noncomputable instance : has_inv ℝ>0   := ⟨λa, ⟨(a.1)⁻¹, inv_pos a.2⟩⟩
instance : has_mul ℝ>0   := ⟨λa b, ⟨a * b, mul_pos a.2 b.2⟩⟩
noncomputable instance : has_div ℝ>0   := ⟨λa b, ⟨a / b, div_pos a.2 b.2⟩⟩
noncomputable instance : has_add ℝ>0   := ⟨λa b, ⟨a + b, add_pos a.2 b.2⟩⟩
instance : has_one ℝ>0   := ⟨⟨1, zero_lt_one⟩⟩
@[simp] protected lemma coe_inv (r : ℝ>0) : ((r⁻¹ : ℝ>0) : ℝ) = r⁻¹ := rfl
noncomputable instance : decidable_linear_order ℝ>0 :=
decidable_linear_order.lift (coe : ℝ>0 → ℝ) subtype.val_injective


end posreal

-- notation for the closed ball of radius r
local notation `B_[` r `]` x := metric.closed_ball x r



structure newton_picard_right_inverse (f : differentiable_maps E F) :=
(to_fun : L(F,E))
(is_right_inverse : ∀ x, (D f 0) (to_fun x) = x)
(r : ℝ>0)
(C : ℝ>0)
--(ε := (min r (5*C)⁻¹ : ℝ))
(N := (λx, f x - f 0 - (D f 0) x : E → F))
(g := to_fun)
(quadratic_estimate : ∀ x y : E, ∥x∥ ≤ min r (5*C)⁻¹ → ∥y∥ ≤ min r (5*C)⁻¹ → ∥g (N x) - g (N y)∥ ≤ C * (∥(x:E)∥ + ∥(y:E)∥) * ∥(x - y:E)∥)
(almost_inverse : ∥g (f 0)∥ ≤ (min r (5*C)⁻¹)/2 )

noncomputable def newton_picard_right_inverse.ε {f : differentiable_maps E F} (g : newton_picard_right_inverse f) : ℝ := min g.r (5*g.C)⁻¹

def newton_picard_right_inverse.εpos {f : differentiable_maps E F} (g : newton_picard_right_inverse f) : g.ε > 0 :=
lt_min g.r.property (show (0:ℝ) < (5*g.C)⁻¹, begin apply inv_pos, apply mul_pos, linarith, exact g.C.property end )

lemma newton_picard_right_inverse.ε_mul_C_le_5_inv {f : differentiable_maps E F} (g : newton_picard_right_inverse f) : g.ε * g.C ≤ 5⁻¹ :=
begin 
  have := inv_mul_cancel (@ne_of_gt _ _ (g.C:ℝ) 0 g.C.property),
  have : (min (g.r:ℝ) (5 * g.C)⁻¹) * g.C ≤ 5⁻¹ * g.C⁻¹ * g.C :=
  begin
    apply mul_le_mul_of_nonneg_right _ (le_of_lt g.C.property),
    refine le_trans (min_le_right g.r (5 * g.C)⁻¹) _,
    rw[mul_inv_eq', mul_comm]
  end,
  apply le_trans this,
  rw[mul_assoc, inv_mul_cancel (@ne_of_gt _ _ (g.C:ℝ) 0 g.C.property), mul_one] 
end

noncomputable instance (f : differentiable_maps E F) : has_coe_to_fun $ newton_picard_right_inverse f :=
{F := λ _, (F → E), coe := (λ g, g.to_fun)}

lemma newton_picard_right_inverse.quadratic_estimate' {f : differentiable_maps E F} (g : newton_picard_right_inverse f) : ∀ x : E, ∥x∥ ≤ g.ε → ∥g (f x - f 0 - (D f 0) x)∥ ≤ g.C * ∥(x:E)∥^2 := 
begin
  assume x hx, 
  have := g.quadratic_estimate x 0 hx (by rw norm_zero; exact le_of_lt g.εpos),
  rw[pow_two ∥x∥, ←mul_assoc],
  simp at this,
  rw [show ⇑g = (g.to_fun), from rfl],
  simpa
end


@[simp] lemma newton_picard_right_inverse.map_neg (x : F) {f : differentiable_maps E F} {g : newton_picard_right_inverse f} : g (- x) = - g x :=
by rw (show (g : F → E) = (g.to_fun : F → E), from rfl); apply bounded_linear_map.map_neg


notation `∃!` binders `,` p:(scoped P, P) `,` `moreover` q:(scoped Q, Q) := exists_unique p ∧ ∀ x, p x → q x

lemma exists_unique_moreover.intro {α : Sort*} {p : α → Prop} {q : α → Prop} (w : α) (h₁ : p w) (h₂ : ∀ y, p y → y = w) (h₃ : q w) :
  ∃! x, p x, moreover q x:=
and.intro (exists.intro w ⟨h₁, h₂⟩) (by intros y hy; rwa[h₂ y hy])

open lipschitz_with

/-- Newton Picard method: solve an equation f x = 0 for x using a linear almost inverse.
 This proof is adopted from Audin, Damian, 'Morse Theory and Floer Homology' -/
theorem newton_picard (f : differentiable_maps E F) (g : newton_picard_right_inverse f) [complete_space E] : 
  ∃! x : E, f x = 0 ∧ ∥x∥ < g.ε ∧ ∃ y, x = g y, 
    moreover ∥x∥ ≤ (5/3) * ∥g (f 0)∥ :=

-- decompose f into an affine and a nonlinear part, f x = f 0 + (D f 0) x + N x
-- and rephrase the equation as a fixed point problem
let L := (D f 0), N := (λx, f x - f 0 - (D f 0) x : E → F),
    ϕ := λ x:E, g (L x - f x) in 

have ∀ x, ϕ x = x → f x = 0, from
  have ∀ x, (⇑L ∘ ϕ) x = (⇑L - f) x, by intro x; dsimp only [ϕ, L, comp]; erw[g.is_right_inverse]; refl,
  assume x (_ : ϕ x = x),
    have L x - f x = L x := by conv { to_rhs, rw[←‹ϕ x = x›]}; exact eq.symm (this x),
    show f x = 0, by apply (@sub_left_inj _ _ (L x) _ _).mp; simpa,
  
have ∀ x, ϕ x = x → ∃ y, x = g y, begin intros x hxfix, dsimp[ϕ] at hxfix, exact ⟨L x - f x, eq.symm hxfix⟩ end,

have ∀ x, f x = 0 ∧ (∃ y, x = g y) → ϕ x = x, from
  assume x ⟨_, _⟩,
  let ⟨y, (_ : x = g y)⟩ := ‹∃ y, x = g y› in
  calc ϕ x = g (L x - 0) : by rw ←‹f x = 0›
       ... = g (L (g y)) : by rw ‹x = g y›; simp
       ... = x : by erw[g.is_right_inverse]; exact eq.symm ‹x = g y›,


have lipschitz_within_with (B_[g.ε] 0) ((2:ℝ)/5) ϕ, from and.intro
  (show (0 ≤ (2:ℝ)/5), by linarith) (assume x y hx hy,
  have ∥x∥ ≤ g.ε, by rwa ←dist_zero_right x,
  have ∥y∥ ≤ g.ε, by rwa ←dist_zero_right y,
  begin 
    refine 
    calc dist (ϕ x) (ϕ y) = ∥(g (-f 0 - N x) - g (-f 0 - N y))∥ : by rw dist_eq_norm; dsimp[ϕ, N, L]; congr; repeat {apply congr_arg, simp}
                      ... = ∥g (N x) - g (N y)∥ : _
               ... ≤ g.C * (∥x∥ + ∥y∥) * ∥x - y∥ : g.quadratic_estimate x y ‹∥x∥ ≤ g.ε› ‹∥y∥ ≤ g.ε›
               ... ≤ g.C * (2 * g.ε) * ∥x - y∥ : _
               ... = g.C * g.ε * (2 * ∥x - y∥) : by ring
               ... ≤  5⁻¹ * (2 * ∥x - y∥) : by rw[mul_comm (g.C:ℝ) g.ε]; apply mul_le_mul_of_nonneg_right g.ε_mul_C_le_5_inv _; linarith using [norm_nonneg (x-y)]
               ... = (2/5) * ∥x - y∥ : by ring
               ... = (2/5) * dist x y : by rw dist_eq_norm,

    -- show that ∥(g (-f 0 - N x) - g (-f 0 - N y))∥ = ∥g (N x) - g (N y)∥
    rw[←norm_neg], congr' 1,
    repeat {rw[show g (-f 0 - _) = g (-f 0) - g _, from (to_linear_map g.to_fun).map_sub (-f 0) _]},
    simp,

    -- show that (g.C) * (∥x∥ + ∥y∥) * ∥x - y∥ ≤ (g.C) * (2 * (g.ε)) * ∥x - y∥
    repeat {rw[mul_comm ↑g.C, mul_assoc]}, 
    apply mul_le_mul_of_nonneg_right (_) (show 0 ≤ ∥x - y∥ * ↑(g.C), from mul_nonneg (norm_nonneg _) (le_of_lt g.C.property)), 
    rw[show 2 * (g.ε:ℝ) = g.ε + g.ε, by ring], 
    apply add_le_add; assumption                                                
  end),


have ∀ x, ∥x∥ ≤ g.ε → ∥ϕ x∥ < g.ε, from
  assume x _,
  calc ∥ϕ x∥ = ∥g (f 0 + N x)∥ : begin rw [←norm_neg (ϕ x)], dsimp[ϕ, N, L], rw[show - g ((D f 0) x + -f x) = g (- ((D f 0) x + -f x)), by rw ←newton_picard_right_inverse.map_neg; simp], congr, apply congr_arg, simp, end
        ... ≤ ∥g (f 0)∥ + ∥g (N x)∥ : by rw[show g (f 0 + _) = g (f 0) + g _, from (to_linear_map g.to_fun).map_add (f 0) _]; exact norm_triangle _ _
        ... ≤ g.ε/2 + g.C * ∥x∥^2 :  add_le_add g.almost_inverse (g.quadratic_estimate' x ‹_›)
        ... ≤ g.ε/2 + g.C * g.ε^2 : begin apply add_le_add (le_of_eq rfl), apply mul_le_mul_of_nonneg_left _ (le_of_lt g.C.property), rw[pow_two ∥x∥, pow_two (g.ε:ℝ)],
                                      exact mul_le_mul ‹∥x∥ ≤ g.ε›  ‹∥x∥ ≤ g.ε› (norm_nonneg x) (le_of_lt g.εpos) end
        ... ≤ g.ε * ((2:ℝ)⁻¹ + (5:ℝ)⁻¹) : begin rw[mul_add (g.ε:ℝ) 2⁻¹ 5⁻¹], apply add_le_add, apply le_of_eq, refl, rw mul_comm, rw[pow_two g.ε], 
  rw[mul_assoc],
  apply mul_le_mul_of_nonneg_left g.ε_mul_C_le_5_inv (le_of_lt g.εpos) end
        ... < g.ε : by conv {to_rhs, rw[←mul_one (g.ε:ℝ)]}; apply mul_lt_mul_of_pos_left _ g.εpos; norm_num,

have corestricts : ∀ x : B_[g.ε] (0:E), ϕ x ∈ B_[g.ε] (0:E), from
  (assume ⟨x, _⟩,
    have dist x 0 ≤ g.ε, by assumption,
    show dist (ϕ x) 0 ≤ g.ε, by rw dist_zero_right at *; exact le_of_lt (‹∀ x, ∥x∥ ≤ g.ε → ∥ϕ x∥ < g.ε› x ‹∥x∥ ≤ g.ε›)),

have h_unique : _, from fixed_point_unique_of_contraction_within corestricts (show (2:ℝ)/5 < 1, by linarith) ‹lipschitz_within_with _ _ ϕ›,
have (0:E) ∈ B_[g.ε] (0:E), by simp [le_of_lt g.εpos],
have ∃ x : B_[g.ε] (0:E), ϕ x = x, from exists_fixed_point_of_contraction_within corestricts (show (2:ℝ)/5 < 1, by linarith) ‹lipschitz_within_with _ _ ϕ› metric.is_closed_ball ⟨⟨(0:E),this⟩⟩,

let ⟨⟨x, x_in_B⟩, is_fixed_point⟩ := this in 
  have h_x_property : f x = 0 ∧ ∥x∥ < (g.ε) ∧ ∃ (y : F), x = g y, from 
    ⟨‹∀ x, ϕ x = x → f x = 0› x ‹ϕ x = x›, 
      suffices ∥ϕ x∥ < g.ε, by rwa[eq.symm ‹ϕ x = x›],
        ‹∀ x, ∥x∥ ≤ g.ε → ∥ϕ x∥ < g.ε› x (show ∥x∥ ≤ g.ε, by rwa ←dist_zero_right x),
      ‹∀ (x : E), ϕ x = x → (∃ (y : F), x = g y)› x ‹ϕ x = x›⟩,

  have h_x_unique : ∀ (y : E), (λ (x : E), f x = 0 ∧ ∥x∥ < g.ε ∧ ∃ (y : F), x = g y) y → y = x, 
  begin
    rintros y ⟨_, _, z, _⟩,
    apply h_unique,
    simpa [le_of_lt ‹∥y∥ < g.ε›],
    exact ‹∀ x, f x = 0 ∧ (∃ y, x = g y) → ϕ x = x› y ⟨‹f y = 0›, ⟨z, ‹y = g z›⟩⟩,
    assumption
  end,

  have h_moreover : ∥x∥ ≤ (5/3) * ∥g (f 0)∥, from 
    have (2/5 * ∥x∥ ≥ ∥x∥ - ∥ϕ 0∥), from 
      calc ((2:ℝ)/5) * ∥x∥ = 2/5 * ∥x - 0∥ : by conv {to_lhs, rw ← sub_zero x}
                      ... ≥ ∥ϕ x - ϕ 0∥ : begin
                                           repeat {rw[←dist_eq_norm]},
                                           exact ‹lipschitz_within_with (B_[g.ε]0) (2 / 5)  ϕ›.2 x 0 ‹_› 
                                             (suffices (0:ℝ) ≤ g.ε, by simp [this], (le_of_lt g.εpos))
                                          end
                      ... = ∥x - ϕ 0∥ : by conv {to_rhs, rw eq.symm (‹ϕ x = x› : ϕ x = x)}
                      ... ≥ ∥(x:E)∥ - ∥ϕ 0∥ : norm_reverse_triangle',
    have ∥ϕ 0∥ = ∥g (f 0)∥,
    begin
      dsimp [ϕ], 
      rw[show (g : F → E) = g.to_fun, from rfl],
      simp
    end,
  begin
    rw ←this,
    have := add_le_add ‹2/5 * ∥x∥ ≥ ∥x∥ - ∥ϕ 0∥› (le_refl ∥ϕ 0∥),
    have := add_le_add (le_refl (-2/5 * ∥x∥)) this,
    have := mul_le_mul_of_nonneg_left this (show (0:ℝ) ≤ 5/3, by linarith),
    ring at this,
    assumption
  end,

  exists_unique_moreover.intro x h_x_property h_x_unique h_moreover

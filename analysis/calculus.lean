import analysis.normed_space analysis.metric_space
import analysis.bounded_linear_maps
import analysis.topology.topological_space analysis.topology.sequences
import algebra.field
import tactic.abel algebra.pi_instances
import analysis.functional.operator_norm

class banach_space (k : out_param $ Type*) (E : Type*) [out_param $ normed_field k] 
  extends normed_space k E, complete_space E 

universes u v -- w

variables {E : Type u} [banach_space ℝ E]
variables {F : Type v} [banach_space ℝ F]

variable {U : topological_space.opens E} 
variable {x : E}

def is_differential_at (_ : x ∈ U) (L : L(E,F)) (f : U → F) : Prop := 
∃ (ψ : E → F) (_ : continuous ψ) (_ : ψ 0 = 0), ∀ h : E, x + h ∈ U →
  f ⟨x + h, ‹x + h ∈ U›⟩ = (f ⟨x, ‹x ∈ U›⟩) + (L h) + ∥h∥ • (ψ h)

def is_linear_approximation_at {x : E} (_ : x ∈ U) (L : E → F) (f : U → F) {ψ : E → F} (_ : continuous ψ) (_ : ψ 0 = 0): Prop :=
∀ h : E, x + h ∈ U → f ⟨x + h, ‹x + h ∈ U›⟩ = (f ⟨x, ‹x ∈ U›⟩) + (L h) + ∥h∥ • (ψ h)

lemma exists2_imp_exists2 {α : Sort*} {p q r : α → Prop} (h : ∀ a, p a → (q a → r a))
  (_ : ∃ {a : α} (_ : p a), q a) : ∃ {a : α} (_ : p a), r a :=
let ⟨a, _ , _⟩ := ‹∃ {a : α} (_ : p a), q a› in
exists.intro a (exists.intro ‹p a› $ h a ‹p a› ‹q a›)


lemma in_preimage_of_small_enough {X : Type*} [topological_space X] {U : set X} (_ : is_open U)
  {f : ℝ → X} (_ : continuous f) (_ : f 0 ∈ U) : ∃ {r : ℝ} (_ : r > 0), ∀ {t : ℝ}, abs t < r → f t ∈ U := 
have is_open {t : ℝ | f t ∈ U}, from ‹continuous f› U ‹is_open U›,
have ∃ r > 0, ball 0 r ⊆ {t | f t ∈ U}, from is_open_metric.mp ‹is_open _› 0 ‹(0:ℝ) ∈ {t : ℝ | f t ∈ U}›,
suffices ∀ (r : ℝ), r > 0 → ball 0 r ⊆ {t : ℝ | f t ∈ U} → ∀ {t : ℝ}, abs t < r → f t ∈ U, from
  exists2_imp_exists2 this ‹_›,
assume r _ _ t _,
have t ∈ {t | f t ∈ U}, from set.mem_of_mem_of_subset (show t ∈ ball (0:ℝ) r, by simpa)
                                                       ‹ball 0 r ⊆ {t | f t ∈ U}›,
this

lemma differential_is_unique (f : U → F) (x ∈ U)
  {L₁} (_ : is_differential_at ‹x ∈ U› L₁ f)
  {L₂} (_ : is_differential_at ‹x ∈ U› L₂ f) : L₁ = L₂ :=
-- show that L₁ = L₂ by showing that L₁ v = L₂ v, ∀ v
by ext v; exact
  show L₁ v = L₂ v, from
    -- substract the defining equalities for L₁ and L₂ to get 0 = L₁ v - L₂ v + ∥v∥ • (ψ₁ (t • v) - ψ₂ (t • v))
    let ⟨ψ₁, _, _, H₁⟩ := ‹is_differential_at ‹x ∈ U› L₁ f›,
        ⟨ψ₂, _, _, H₂⟩ := ‹is_differential_at ‹x ∈ U› L₂ f› in
    have is_bounded_linear_map L₁, from L₁.property,
    have is_bounded_linear_map L₂, from L₂.property,
    
    -- for t small enough, x + t • v is in U
    have ∃ {r : ℝ} (_ : r > 0), ∀ {t : ℝ}, abs t < r → x + t • v ∈ U, from
      have (continuous (λ (t:ℝ), x + t • v)), from continuous_add continuous_const (continuous_smul continuous_id continuous_const),
      in_preimage_of_small_enough U.property this (show x + 0 • v ∈ U, by simp; assumption),
    let ⟨r, _, _⟩ := this in

    -- and for such t we can prove an equality
    have H₁ : ∀ (t : ℝ), abs t < r → t > 0 → 0 = L₁ v - L₂ v + ∥v∥ • (ψ₁ (t • v) - ψ₂ (t • v)), from 
      assume t (_ : abs t < r) (_ : t > 0),
        have x + t • v ∈ U, from ‹∀ {t : ℝ}, abs t < r → x + t • v ∈ U› ‹abs t < r›,
        let h := t • v in
        have eq1 : f ⟨x + h ,‹_ ∈ U›⟩ = (f ⟨x, ‹_ ∈ U›⟩) + (L₁ h) + ∥h∥ • (ψ₁ h), from H₁ _ _, 
        have eq2 : f ⟨x + h ,‹_ ∈ U›⟩ = (f ⟨x, ‹_ ∈ U›⟩) + (L₂ h) + ∥h∥ • (ψ₂ h), from H₂ _ _,
        have H₁ : 0 = t • (L₁ v - L₂ v) + ∥t∥ • ∥v∥ • (ψ₁ h - ψ₂ h), from
          calc (0 : F) = ((f ⟨x, ‹_ ∈ U›⟩) + (L₁ h) + ∥h∥ • (ψ₁ h)) -
                         ((f ⟨x, ‹_ ∈ U›⟩) + (L₂ h) + ∥h∥ • (ψ₂ h))        : by rw[←eq1, ←eq2]; simp
                   ... = (L₁ (t • v)) - (L₂ (t • v)) + ∥h∥ • (ψ₁ h - ψ₂ h) : by rw[smul_sub, show h = t•v, from rfl]; simp
                   ... = t • (L₁ v) - t • (L₂ v) + ∥t • v∥ • (ψ₁ h - ψ₂ h) : by rw[‹is_bounded_linear_map L₁›.smul,
                                                                                  ‹is_bounded_linear_map L₂›.smul]
                   ... = t • (L₁ v - L₂ v) + ∥t∥ • ∥v∥ • (ψ₁ h - ψ₂ h) : by rw[←smul_sub, norm_smul, mul_smul],
        -- multiply by 1/t
        have t⁻¹ * t = 1, from inv_mul_cancel $ ne_of_gt ‹t > 0›,
        have t⁻¹ * ∥t∥ = 1, by rwa[show ∥t∥ = abs t, from rfl, abs_of_pos ‹t > 0›],
        calc (0:F) = (1/t) • (t • (L₁ v - L₂ v) + ∥t∥ • ∥v∥ • (ψ₁ h - ψ₂ h)) : by rw [←H₁, smul_zero]
               ... = (L₁ v - L₂ v) + ∥v∥ • (ψ₁ h - ψ₂ h) :  by simp; rw [smul_add, show h = t • v, from rfl, ←mul_smul, ‹t⁻¹ * ∥t∥ = 1›, one_smul];
                                                               simp; rw[←mul_smul, ‹t⁻¹ * t = 1›, one_smul]; simp,

    -- now let t go to zero to in H₁ and conclude 0 = L₁ v - L₂ v
    -- first show that the equation depends continuously on t
    let ϕ : ℝ → F := λ t,  L₁ v - L₂ v + ∥v∥ • (ψ₁ (t • v) - ψ₂ (t • v)) in
    have continuous ϕ, from 
      have h1 : continuous $ λ t : ℝ, ψ₁ (t • v), from continuous.comp (continuous_smul continuous_id continuous_const) ‹continuous ψ₁›,
      have h2 : continuous $ λ t : ℝ, ψ₂ (t • v), from continuous.comp (continuous_smul continuous_id continuous_const) ‹continuous ψ₂›,
      continuous_add continuous_const (continuous_smul continuous_const (continuous_sub h1 h2)),
    
    -- plug in the sequence 1/n for t
    let seq : ℕ → ℝ := λ n, 1 / (↑n + 1) in
    have sequence.converges_to seq 0, from sequence.converges_to_iff_tendsto.mpr tendsto_div,

    have 0 = ϕ 0, from
      have sequence.converges_to (ϕ∘seq) 0, from
        -- the sequence converges since, according to to H₁, ϕ seq n is zero for 1/n < r 
        show ∀ V : set F, (0:F) ∈ V → is_open V → ∃ n0 : ℕ, ∀ n ≥ n0, ((ϕ∘seq) n) ∈ V, from 
          assume V (_ : (0:F) ∈ V) (_ : is_open V),          
          -- seq n is eventually 'small enough', thus H₁ applies and the sequence is eventually constantly zero
          have ∃ n0 : ℕ, ∀ n ≥ n0, dist (seq n) 0 < r, from (sequence.metrically_converges_to_iff_tendsto.mpr tendsto_div) r ‹r > 0›,       
          suffices ∀ (n0 : ℕ), (∀ (n : ℕ), n ≥ n0 → dist (seq n) 0 < r) → ∀ (n : ℕ), n ≥ n0 → (ϕ ∘ seq) n ∈ V, from 
            exists_imp_exists this ‹_›,
          assume n0 H n (_ : n ≥ n0),
          have abs (seq n) < r, from
          calc abs (seq n) = ∥seq n∥ : by rw[show ∥seq n∥ = abs (seq n), from rfl]
                 ... = dist (seq n) 0 : by simp
                 ... < r : H n ‹n ≥ n0›,
          have h : 0 = L₁ v - L₂ v + ∥v∥ • (ψ₁ ((seq n) • v) - ψ₂ ((seq n) • v)), from
              H₁ (seq n) this (sequence.one_div_succ_pos n),
          have ((ϕ∘seq) n) = L₁ v - L₂ v + ∥v∥ • (ψ₁ ((seq n) • v) - ψ₂ ((seq n) • v)), by refl,
          show ((ϕ∘seq) n) ∈ V, begin rw this, rw ←h , exact ‹0 ∈ V› end,
      have sequence.converges_to (ϕ∘seq) (ϕ 0), from sequence.cont_to_seq_cont ‹continuous ϕ› seq ‹sequence.converges_to seq 0›,
      show 0 = ϕ 0, from sequence.limits_are_unique ‹sequence.converges_to (ϕ∘seq) 0› ‹sequence.converges_to (ϕ∘seq) (ϕ 0)›,
    calc L₁ v = L₁ v - ϕ 0                                 : by rw[←‹0 = ϕ 0›]; exact (eq.symm $ sub_zero $ L₁ v)
          ... = L₁ v - (L₁ v - L₂ v + ∥v∥ • (ψ₁ 0 - ψ₂ 0)) : by rw[←zero_smul v]
          ... = L₁ v - (L₁ v - L₂ v + ∥v∥ • 0)             : by rw[‹ψ₁ 0 = 0›, ‹ψ₂ 0 = 0›, sub_zero]
          ... = L₂ v                                       : by simp; abel

def differentiable_at (_ : x ∈ U) (f : U → F) := ∃ L : L(E, F), is_differential_at ‹x ∈ U› L f

noncomputable def differential_at (_ : x ∈ U) {f : U → F} (D : differentiable_at ‹x ∈ U› f) : L(E, F):=
classical.some D

def differentiable (f : U → F) : Prop := ∀ x ∈ U, differentiable_at ‹x ∈ U› f

noncomputable def differential {f : U → F} (h : differentiable f) : U → L(E,F) :=
λ x, differential_at x.property (h x x.property)

set_option class.instance_max_depth 48
lemma differential_is_additive (_ : x ∈ U) (f : U → F) {Dfx : L(E,F)} (hDfx : is_differential_at ‹x ∈ U› Dfx f)
                                              (g : U → F) {Dgx : L(E,F)} (hDgx : is_differential_at ‹x ∈ U› Dgx g) :
      is_differential_at ‹x ∈ U› (Dfx + Dgx) (f + g):=
 show ∃ (ψ : E → F) (_ : continuous ψ) (_ : ψ 0 = 0),
          ∀ h (_ : x + h ∈ U), (f + g) ⟨x + h, ‹_›⟩ = (f + g) ⟨x, ‹_›⟩ + (Dfx + Dgx) h + ∥h∥ • ψ h, from
   let ⟨ψf, _, _, eqf⟩ := hDfx,
       ⟨ψg, _, _, eqg⟩ := hDgx in   
    ⟨ψf + ψg, continuous_add ‹continuous ψf› ‹continuous ψg›, by simp[‹ψf 0 = 0›, ‹ψg 0 = 0›], 
      assume h _,
        show (f + g) ⟨x + h, ‹_›⟩ = (f + g) ⟨x, ‹_›⟩ + (Dfx + Dgx) h + ∥h∥ • (ψf + ψg) h, 
        by simp[eqf h ‹_›, eqg h ‹_›, smul_add, show ((Dfx + Dgx) h) = Dfx h + Dgx h, from rfl]⟩

lemma differentiable_add {f : U → F} {g : U → F} (_ : differentiable f) (_ : differentiable g) : differentiable $ λ x, f x + g x :=
assume x _,
show differentiable_at ‹x ∈ U› $ λ x, f x + g x, from
  let ⟨Dfx, _⟩ := ‹differentiable f› x ‹_›,
      ⟨Dgx, _⟩ := ‹differentiable g› x ‹_› in
  show ∃ L : L(E,F), is_differential_at ‹_› L (f + g), from
    exists.intro (Dfx + Dgx) $ differential_is_additive ‹x ∈ U› f ‹_› g ‹_›


lemma differential_is_homogeneous (_ : x ∈ U) (c : ℝ) (f : U → F) {Dfx : L(E,F)} (hDfx : is_differential_at ‹x ∈ U› Dfx f) :
  is_differential_at ‹x ∈ U› (c • Dfx) (c • f) := 
show ∃ (ψ : E → F) (_: continuous ψ) (_ : ψ 0 = 0),
        ∀ h (_ : x + h ∈ U), c • f ⟨x + h, ‹x + h ∈ U›⟩ = c • f ⟨x , ‹x ∈ U›⟩ + c • Dfx h + ∥h∥ • ψ h, from
let ⟨ψ, _, _, eq⟩ := hDfx in
⟨c • ψ, continuous_smul continuous_const ‹continuous ψ›, by simp[‹ψ 0 = 0›],
  assume h _,
    show c • f ⟨x + h, ‹x + h ∈ U›⟩ = c • f ⟨x , ‹x ∈ U›⟩ + c • Dfx h + ∥h∥ • c • ψ h, by simp [eq, smul_add, smul_smul, mul_comm]⟩

lemma differentiable_smul {f : U → F} {c : ℝ} (_ : differentiable f) : differentiable $ c • f :=
assume x _,
show differentiable_at ‹x ∈ U› $ c • f, from
  let ⟨Dfx, _⟩ := ‹differentiable f› x ‹_› in
  show ∃ L : L(E,F), is_differential_at ‹_› L (c • f), from
    exists.intro (c • Dfx) $ differential_is_homogeneous ‹x ∈ U› c f ‹_›

lemma differential_const {_ : x ∈ U} {c : F} : is_differential_at ‹x ∈ U› 0 (λ_,c) :=
let f := ((λ_,c) : U → F),
    Dfx := (0 : L(E,F)) in
(show ∃ (ψ : E → F) (_: continuous ψ) (_ : ψ 0 = 0),
      ∀ h (_ : x + h ∈ U), f ⟨x + h, ‹_›⟩ = f ⟨x , ‹x ∈ U›⟩ +  Dfx h + ∥h∥ • ψ h, from
⟨λ_,0, continuous_const, by simp, assume h _, by rw[show ⇑Dfx = (λ(_:E),(0:F)), from rfl]; simp⟩)
     
lemma differentiable_const (c : F) : differentiable (λ_, c : U → F) :=
assume x _,
show differentiable_at ‹x ∈ U› $ _, from 
  exists.intro _ differential_const

def differentiable_maps (U : topological_space.opens E) (F : Type*) [normed_group F] [banach_space ℝ F] : set (U → F) :=
  differentiable

instance (U : topological_space.opens E): is_subspace (differentiable_maps U F) := {
  smul_mem := assume c f, differentiable_smul,
  add_mem := assume f g, differentiable_add,
  zero_mem := differentiable_const 0,
  neg_mem := assume f _, 
               have -f = (-1 : ℝ) • f, by apply funext; simp,
               begin rw[this], exact differentiable_smul ‹differentiable f› end
}

noncomputable def D : differentiable_maps U F → U → L(E,F) :=
assume ⟨f, _⟩, differential ‹_›

def continuously_differentiable_maps (U : topological_space.opens E) (F : Type*) [normed_group F] [banach_space ℝ F] : set $ differentiable_maps U F :=
assume f, continuous (D f)

notation `C¹(` U `,` F `)` := continuously_differentiable_maps U F

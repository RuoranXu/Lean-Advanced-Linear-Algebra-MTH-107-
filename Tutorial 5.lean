import linear_algebra.basic
import linear_algebra.linear_map
import linear_algebra.matrix
import polynomial.basic
import data.real.basic

variables {F : Type} [field F] {V W U : Type}
[add_comm_group V] [module F V]
[add_comm_group W] [module F W]
[add_comm_group U] [module F U]

-- Question 1: Differentiation operator not invertible
def D : linear_map F (polynomial F) (polynomial F) := polynomial.derivative F

lemma D_not_invertible : ¬invertible D :=
begin
  intro h,
  have : D.injective, from invertible.injective h,
  have : polynomial.const 1 ∈ D.ker,
  { simp [D, polynomial.derivative_const] },
  have : polynomial.const 1 = 0, from this.1,
  contradiction
end

-- Question 2: Matrix of differentiation on span(e^x, x e^x, x² e^x)
def U : Type := span F { exp X, X * exp X, X² * exp X }
def B : vector_space.basis F U := [exp X, X * exp X, X² * exp X]

-- Compute D on basis vectors
lemma D_expX : D (exp X) = exp X :=
begin
  simp [D, polynomial.derivative_exp]
end

lemma D_XexpX : D (X * exp X) = exp X + X * exp X :=
begin
  simp [D, polynomial.derivative_mul, polynomial.derivative_X, polynomial.derivative_exp]
end

lemma D_X2expX : D (X² * exp X) = 2•X * exp X + X² * exp X :=
begin
  simp [D, polynomial.derivative_mul, polynomial.derivative_X_pow, polynomial.derivative_exp]
end

-- Matrix [D]_B^B
def [D]_B^B : matrix (fin 3) (fin 3) F :=
λ i j, match (i, j) with
| (0, 0) := 1 | (0, 1) := 1 | (0, 2) := 0
| (1, 0) := 0 | (1, 1) := 1 | (1, 2) := 2
| (2, 0) := 0 | (2, 1) := 0 | (2, 2) := 1
end

lemma matrix_D_BB : linear_map.matrix_repr D B B = [D]_B^B :=
begin
  ext i j,
  cases i,
  { cases j,
    { rw D_expX, exact rfl },
    { rw D_XexpX, exact rfl },
    { rw D_X2expX, exact rfl } },
  { cases j,
    { rw D_expX, exact rfl },
    { rw D_XexpX, exact rfl },
    { rw D_X2expX, exact rfl } },
  { cases j,
    { rw D_expX, exact rfl },
    { rw D_XexpX, exact rfl },
    { rw D_X2expX, exact rfl } }
end

-- Question 3: S₁T=id and TS₂=id implies T invertible
lemma T_invertible_if_both_inverses (S₁ S₂ : linear_map F W V)
  (h1 : S₁ ∘ T = linear_map.id) (h2 : T ∘ S₂ = linear_map.id) :
  invertible T :=
begin
  have : S₁ = S₂,
  { ext w,
    rw [← h1, linear_map.comp_apply, h2, linear_map.comp_apply, linear_map.id_apply] },
  use S₁,
  split,
  { exact h1 },
  { rw this, exact h2 }
end

-- Question 4: Restriction T|_U is isomorphism if ker(T)⊕U=V
lemma restriction_is_isomorphism (h_dirsum : T.ker ⊕ U = V) (h_surj : T.surjective) :
  invertible (T.restrict U) :=
begin
  have : T.restrict U.injective,
  { intro u hu,
    have : u ∈ T.ker ∩ U,
    { split,
      { exact hu },
      { exact set.mem_of_subset (linear_map.restrict_domain_subset) rfl } },
    have : u = 0, from h_dirsum.2 this,
    exact this },
  have : T.restrict U.surjective,
  { intro w,
    obtain ⟨v, hv⟩ := h_surj w,
    obtain ⟨u₁, u₂, hu1, hu2, hv_eq⟩ := h_dirsum.1 v,
    have : T u₂ = w,
    { rw hv_eq at hv,
      simp [hu1, hv] },
    exact ⟨u₂, hu2, this⟩ },
  exact invertible.of_bijective this this
end

-- Question 5: Interpolation map is isomorphism
variables {x₁ ... xₙ₊₁ : F} (h_distinct : ∀ i ≠ j, xᵢ ≠ xⱼ)
def T : linear_map F (polynomial F)ₙ (F^(n+1)) :=
λ p, λ i, polynomial.eval xᵢ₊₁ p

-- 5a: T is injective
lemma T_injective : T.injective :=
begin
  intro p hp,
  have : p has roots x₁ ... xₙ₊₁,
  { simp [hp, polynomial.has_root] },
  have : degree p ≤ n,
  { exact polynomial.degree_le_of_subset (polynomial F)ₙ p },
  have : p = 0,
  { apply polynomial.eq_zero_of_degree_le_n_has_n+1_roots this h_distinct },
  exact this
end

-- 5b: T is isomorphism (hence unique interpolation)
lemma T_is_isomorphism : invertible T :=
begin
  have : finite_dimensional.dim F (polynomial F)ₙ = n+1,
  { exact polynomial.dim_polynomial F n },
  have : finite_dimensional.dim F (F^(n+1)) = n+1,
  { exact finite_dimensional.dim_finvec F (n+1) },
  have : T.bijective,
  { split,
    { exact T_injective h_distinct },
    { exact finite_dimensional.surjective_of_injective_of_same_dim this this T_injective } },
  exact invertible.of_bijective this
end

-- Question 6: Lagrange interpolation formula
def p_i (i : fin (n+1)) : polynomial F :=
∏ (j : fin (n+1)) (j ≠ i), (X - polynomial.const xⱼ₊₁) / ∏ (j ≠ i) (xᵢ₊₁ - xⱼ₊₁)

lemma p_i_eval : ∀ i j, polynomial.eval xⱼ₊₁ (p_i i) = if i = j then 1 else 0 :=
begin
  intros i j,
  cases i = j,
  { simp [p_i, polynomial.eval_div, polynomial.eval_mul, polynomial.eval_sub,
          polynomial.eval_X, polynomial.eval_const, h_distinct] },
  { simp [p_i, polynomial.eval_div, polynomial.eval_mul, polynomial.eval_sub,
          polynomial.eval_X, polynomial.eval_const, h_distinct, false] }
end

lemma lagrange_interpolation (y : F^(n+1)) :
  T⁻¹ y = ∑ (i : fin (n+1)) y i • p_i i :=
begin
  ext x,
  rw [linear_map.inv_apply, T, polynomial.eval_sum, polynomial.eval_smul],
  simp [p_i_eval h_distinct]
end

-- Question 7: V ≅ L(F, V)
def F_eval : linear_map F (linear_map F F V) V :=
λ T, T 1

lemma F_eval_is_isomorphism : invertible F_eval :=
begin
  have : F_eval.injective,
  { intro T hT,
    ext λ,
    have : T λ = λ•T 1,
    { exact linear_map.smul_apply T λ 1 },
    rw hT at this,
    simp [this] },
  have : F_eval.surjective,
  { intro v,
    def T : linear_map F F V := λ λ, λ•v,
    have : T.linear,
    { split,
      { intros λ₁ λ₂, simp [add_smul] },
      { intros λ₁ λ₂, simp [smul_smul] } },
    have : F_eval T = v,
    { simp [T, F_eval] },
    exact ⟨T, this⟩ },
  exact invertible.of_bijective this this
end

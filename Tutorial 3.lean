import linear_algebra.basic
import linear_algebra.subspace
import linear_algebra.dimension
import polynomial.basic

variables {F : Type} [field F] {V : Type} [add_comm_group V] [module F V]

-- Question 1: Span and linear independence preservation
variables (u1 u2 u3 : V)

-- 1a: If (u1,u2,u3) spans V, so does (u1-u2, u2-u3, u3)
lemma span_preserved : span F {u1, u2, u3} = span F {u1 - u2, u2 - u3, u3} :=
begin
  apply set.subset.antisymm,
  { -- ⊆: Any linear combo of u1,u2,u3 is combo of new vectors
    intros v hv,
    obtain ⟨λ1, λ2, λ3, rfl⟩ := hv,
    have : λ1*u1 + λ2*u2 + λ3*u3 = λ1*(u1 - u2) + (λ2 + λ1)*(u2 - u3) + (λ3 + λ2)*u3,
    { simp [add_mul, sub_mul, add_assoc, add_comm] },
    exact span.mem_span_singleton.mpr this },
  { -- ⊇: New vectors are in span of u1,u2,u3
    intros v hv,
    cases hv,
    { rw hv, exact span.mem_span_singleton.mpr (by simp) },
    { rw hv, exact span.mem_span_singleton.mpr (by simp) },
    { rw hv, exact span.mem_span_singleton.mpr (by simp) },
    { rw hv, apply span.add_mem, assumption, assumption },
    { rw hv, apply span.smul_mem, assumption } }
end

-- 1b: If (u1,u2,u3) is linearly independent, so is (u1-u2, u2-u3, u3)
lemma lin_indep_preserved (h : linear_independent F [u1, u2, u3]) :
  linear_independent F [u1 - u2, u2 - u3, u3] :=
begin
  intros λ1 λ2 λ3 h_eq,
  have : λ1*(u1 - u2) + λ2*(u2 - u3) + λ3*u3 = 0, from h_eq,
  simp [add_mul, sub_mul] at this,
  rearrange_terms this,
  have : λ1*u1 + (λ2 - λ1)*u2 + (λ3 - λ2)*u3 = 0, from this,
  apply h to this,
  have λ1_eq := this.1,
  have λ2_eq := this.2,
  have λ3_eq := this.3,
  rw λ1_eq at λ2_eq,
  rw λ2_eq at λ3_eq,
  exact ⟨λ1_eq, λ2_eq, λ3_eq⟩
end

-- Question 2: dim U = dim V ⇒ U = V (finite dim)
lemma subspace_eq_of_same_dim [finite_dimensional F V] {U : set V} [is_subspace F U]
  (h : finite_dimensional.dim F U = finite_dimensional.dim F V) : U = V :=
begin
  have : finite_dimensional F U, from finite_dimensional.of_subspace F U,
  obtain ⟨B, hB⟩ := finite_dimensional.exists_basis F U,
  have : linear_independent F (vector_space.basis.to_list B), from hB.1,
  have : vector_space.basis.to_list B spans F V,
  { apply finite_dimensional.spans_of_lin_indep_of_length_eq_dim,
    rw [h, hB.2] },
  have : U = span F (vector_space.basis.to_list B), from hB.3,
  rw this,
  exact span_eq_univ_of_spans F (vector_space.basis.to_list B)
end

-- Question 3: Basis for U = { p ∈ P(F)_2 | p(1) = 0 }
def P2 : Type := polynomial F
def U : set P2 := { p | polynomial.eval 1 p = 0 }

-- 3a: Basis for U
def p1 : P2 := polynomial.X - 1
def p2 : P2 := polynomial.X^2 - 1

lemma p1_mem_U : p1 ∈ U :=
begin
  simp [U, p1, polynomial.eval_sub, polynomial.eval_X, polynomial.eval_one]
end

lemma p2_mem_U : p2 ∈ U :=
begin
  simp [U, p2, polynomial.eval_sub, polynomial.eval_X_pow, polynomial.eval_one]
end

lemma p1_p2_lin_indep : linear_independent F [p1, p2] :=
begin
  intros λ1 λ2 h_eq,
  have : λ1*(X - 1) + λ2*(X^2 - 1) = 0, from h_eq,
  expand_polynomial this,
  equate_coeffs,
  { -- X² term: λ2 = 0
    exact rfl },
  { -- X term: λ1 = 0
    rw ← prev_coeff_eq_zero, exact rfl },
  { -- Constant term: -λ1 - λ2 = 0, which holds by λ1=λ2=0
    simp }
end

lemma U_basis : vector_space.basis F (span F [p1, p2]) = U :=
begin
  apply set.subset.antisymm,
  { -- span [p1,p2] ⊆ U
    intros p hp,
    obtain ⟨λ1, λ2, rfl⟩ := hp,
    simp [U, p1, p2, polynomial.eval_add, polynomial.eval_smul, p1_mem_U, p2_mem_U] },
  { -- U ⊆ span [p1,p2]
    intros p hp,
    have : p = (polynomial.X - 1) * q + r, from polynomial.divisibility_by_linear (X - 1) p,
    have : r = 0,
    { rw polynomial.eval_div_eq (X - 1) p,
      simp [hp] },
    rw this at h,
    have : q ∈ P(F)₁,
    { rw polynomial.degree_mul (X - 1) q,
      simp [polynomial.degree_le_of_subset (span F [p1,p2]) U] },
    obtain ⟨a, b, rfl⟩ := polynomial.eq_smul_X_add_const q,
    have : p = a*(X - 1)*X + b*(X - 1) = a*(X² - X) + b*(X - 1) = a*(X² - 1) + (b - a)*(X - 1),
    { simp [mul_add, add_mul] },
    exact span.mem_span_singleton.mpr this }
end

-- 3b: Extend to basis of P(F)_2
def q : P2 := 1
lemma P2_basis : linear_independent F [p1, p2, q] :=
begin
  intros λ1 λ2 λ3 h_eq,
  have : λ1*(X - 1) + λ2*(X² - 1) + λ3*1 = 0, from h_eq,
  expand_polynomial this,
  equate_coeffs,
  { -- X² term: λ2 = 0
    exact rfl },
  { -- X term: λ1 = 0
    rw ← prev_coeff_eq_zero, exact rfl },
  { -- Constant term: -λ1 - λ2 + λ3 = 0 ⇒ λ3 = 0
    simp [λ1=0, λ2=0] }
end

-- 3c: W = span q, U ⊕ W = P(F)_2
def W : set P2 := span F [q]
lemma U_dirsum_W : U ⊕ W = univ :=
begin
  rw direct_sum_eq_univ_iff,
  split,
  { -- U + W = P(F)_2
    intros p,
    have : p = (p - polynomial.eval 1 p * q) + polynomial.eval 1 p * q,
    { simp },
    have hp : p - polynomial.eval 1 p * q ∈ U,
    { simp [U, polynomial.eval_sub, polynomial.eval_smul, polynomial.eval_one] },
    have hq : polynomial.eval 1 p * q ∈ W, from span.mem_span_singleton,
    exact ⟨p - polynomial.eval 1 p * q, polynomial.eval 1 p * q, this⟩ },
  { -- U ∩ W = {0}
    intros p hp hq,
    obtain ⟨λ, rfl⟩ := hq,
    have : polynomial.eval 1 p = λ,
    { simp [q, polynomial.eval_smul, polynomial.eval_one] },
    rw hp at this,
    simp [this] }
end

-- Question 4: Possible dim(U ∩ W) for 3-dim subspaces of F^5
lemma possible_intersection_dims :
  ∀ d ∈ {1, 2, 3}, ∃ (U W : set (F^5)) [is_subspace F U] [is_subspace F W]
  (hU : finite_dimensional.dim F U = 3) (hW : finite_dimensional.dim F W = 3),
  finite_dimensional.dim F (U ∩ W) = d :=
begin
  intro d,
  cases d,
  { -- d=1
    def U : set (F^5) := { v | v.4 = 0 ∧ v.5 = 0 },
    def W : set (F^5) := { v | v.1 = 0 ∧ v.2 = 0 },
    have hU : is_subspace F U ∧ finite_dimensional.dim F U = 3,
    { split,
      { exact is_subspace.mk (λ _ _, true) (λ _ _, true) (λ _ _, true) },
      { exact finite_dimensional.dim_of_basis F U [ (1,0,0,0,0), (0,1,0,0,0), (0,0,1,0,0) ] } },
    have hW : is_subspace F W ∧ finite_dimensional.dim F W = 3,
    { split,
      { exact is_subspace.mk (λ _ _, true) (λ _ _, true) (λ _ _, true) },
      { exact finite_dimensional.dim_of_basis F W [ (0,0,1,0,0), (0,0,0,1,0), (0,0,0,0,1) ] } },
    have h_inter : U ∩ W = { v | v.1=0 ∧ v.2=0 ∧ v.4=0 ∧ v.5=0 },
    { simp },
    have h_dim : finite_dimensional.dim F (U ∩ W) = 1,
    { exact finite_dimensional.dim_of_basis F (U ∩ W) [ (0,0,1,0,0) ] },
    use U, W, hU.1, hW.1, hU.2, hW.2, h_dim },
  { -- d=2
    def U : set (F^5) := { v | v.4 = 0 ∧ v.5 = 0 },
    def W : set (F^5) := { v | v.1 = 0 ∧ v.5 = 0 },
    have hU : is_subspace F U ∧ finite_dimensional.dim F U = 3,
    { split,
      { exact is_subspace.mk (λ _ _, true) (λ _ _, true) (λ _ _, true) },
      { exact finite_dimensional.dim_of_basis F U [ (1,0,0,0,0), (0,1,0,0,0), (0,0,1,0,0) ] } },
    have hW : is_subspace F W ∧ finite_dimensional.dim F W = 3,
    { split,
      { exact is_subspace.mk (λ _ _, true) (λ _ _, true) (λ _ _, true) },
      { exact finite_dimensional.dim_of_basis F W [ (0,1,0,0,0), (0,0,1,0,0), (0,0,0,1,0) ] } },
    have h_inter : U ∩ W = { v | v.1=0 ∧ v.4=0 ∧ v.5=0 },
    { simp },
    have h_dim : finite_dimensional.dim F (U ∩ W) = 2,
    { exact finite_dimensional.dim_of_basis F (U ∩ W) [ (0,1,0,0,0), (0,0,1,0,0) ] },
    use U, W, hU.1, hW.1, hU.2, hW.2, h_dim },
  { -- d=3
    def U : set (F^5) := { v | v.4 = 0 ∧ v.5 = 0 },
    def W : set (F^5) := U,
    have hU : is_subspace F U ∧ finite_dimensional.dim F U = 3,
    { split,
      { exact is_subspace.mk (λ _ _, true) (λ _ _, true) (λ _ _, true) },
      { exact finite_dimensional.dim_of_basis F U [ (1,0,0,0,0), (0,1,0,0,0), (0,0,1,0,0) ] } },
    have h_inter : U ∩ W = U,
    { simp },
    have h_dim : finite_dimensional.dim F (U ∩ W) = 3,
    { rw h_inter, exact hU.2 },
    use U, W, hU.1, hU.1, hU.2, hU.2, h_dim }
end

-- Question 5: Infinite dimensional iff arbitrary long lin indep lists
lemma infinite_dim_iff_arbitrary_lin_indep :
  infinite_dimensional F V ↔ ∀ m : ℕ, ∃ (v₁ ... vₘ : V), linear_independent F [v₁, ..., vₘ] :=
begin
  split,
  { intro h,
    intro m,
    induction m,
    { use [], exact linear_independent.nil },
    { obtain ⟨v₁ ... vₘ₊₁, h_ind⟩ := m_ih,
      have : span F [v₁ ... vₘ₊₁] ≠ V,
      { intro h_eq,
        rw h_eq at h,
        contradiction },
      obtain ⟨v, hv⟩ := set.not_subset_iff_exists.1 (λ x hx, h_eq hx),
      use v₁ ... vₘ₊₁, v,
      apply linear_independent.cons h_ind hv } },
  { intro h,
    intro fin_dim,
    obtain ⟨B, hB⟩ := finite_dimensional.exists_basis F V,
    let m := vector_space.basis.card B + 1,
    obtain ⟨v₁ ... vₘ, h_ind⟩ := h m,
    have : linear_independent F [v₁ ... vₘ] ∧ card [v₁ ... vₘ] = m > vector_space.basis.card B,
    { split, exact h_ind, simp },
    contradiction }
end

-- Question 6: ℝ^ℕ is infinite dimensional
def ℝ^ℕ : Type := ℕ → ℝ
def e (n : ℕ) : ℝ^ℕ := λ k, if k = n then 1 else 0

lemma e_lin_indep (m : ℕ) : linear_independent ℝ [e 0, e 1, ..., e (m-1)] :=
begin
  intros λ₀ ... λₘ₋₁ h_eq,
  ext k,
  cases k,
  { simp [e, h_eq] },
  { simp [e, h_eq] }
end

lemma ℝ^ℕ_infinite_dim : infinite_dimensional ℝ ℝ^ℕ :=
begin
  rw infinite_dim_iff_arbitrary_lin_indep,
  intro m,
  use e 0, e 1, ..., e (m-1),
  exact e_lin_indep m
end

-- Question 7: Subspaces of ℝ³ are {0}, lines, planes, ℝ³
lemma subspaces_of_R3 :
  ∀ (U : set (ℝ^3)) [is_subspace ℝ U],
  U = {0} ∨
  (∃ u ≠ 0, U = span ℝ [u]) ∨
  (∃ u v, linear_independent ℝ [u, v] ∧ U = span ℝ [u, v]) ∨
  U = univ :=
begin
  intro U,
  intro hU,
  have : finite_dimensional ℝ U, from finite_dimensional.of_subspace ℝ U,
  obtain ⟨dim, h_dim⟩ := finite_dimensional.dim ℝ U,
  cases dim,
  { -- dim=0: U={0}
    exact or.inl (subspace_eq_zero_iff_dim_zero.1 h_dim) },
  { -- dim=1: line through origin
    obtain ⟨u, hu⟩ := finite_dimensional.exists_non_zero U,
    have : span ℝ [u] = U,
    { apply subspace_eq_of_same_dim,
      rw [h_dim, finite_dimensional.dim_of_basis ℝ (span ℝ [u]) [u]] },
    exact or.inr (or.inl (⟨u, hu, this⟩)) },
  { -- dim=2: plane through origin
    obtain ⟨u, hu⟩ := finite_dimensional.exists_non_zero U,
    have : span ℝ [u] ≠ U,
    { intro h_eq,
      rw h_eq at h_dim,
      contradiction },
    obtain ⟨v, hv⟩ := set.not_subset_iff_exists.1 (λ x hx, h_eq hx),
    have : linear_independent ℝ [u, v],
    { intro h,
      obtain ⟨λ, μ, h_eq⟩ := h,
      rw h_eq at hv,
      simp [hv] },
    have : span ℝ [u, v] = U,
    { apply subspace_eq_of_same_dim,
      rw [h_dim, finite_dimensional.dim_of_basis ℝ (span ℝ [u, v]) [u, v]] },
    exact or.inr (or.inr (or.inl (⟨u, v, this.1, this.2⟩))) },
  { -- dim=3: U=ℝ³
    have : U = univ,
    { apply subspace_eq_of_same_dim,
      rw [h_dim, finite_dimensional.dim ℝ ℝ^3] },
    exact or.inr (or.inr (or.inr this)) }
end

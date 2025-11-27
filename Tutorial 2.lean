import linear_algebra.basic
import linear_algebra.subspace
import data.real.basic

variables {F : Type} [field F] {V : Type} [add_comm_group V] [module F V]

-- Question 1: (-1)•v = -v
lemma neg_one_smul_eq_neg (v : V) : (-1 : F) • v = -v :=
begin
  have h : v + (-1)•v = 0•v,
  { rw [← smul_add, add_neg_eq_zero, smul_zero] },
  rw zero_smul at h,
  exact add_left_neg_iff_eq_neg h
end

-- Question 2: Subspace checks for ℝ³
variables {x y z : F}

-- 2a: U = { (x,y,z) | 2x - 3y + z = 0 } is subspace
def U : set (F^3) := { v : F^3 | 2*v.1 - 3*v.2 + v.3 = 0 }

lemma U_is_subspace : is_subspace F U :=
begin
  split,
  { -- Contains zero
    have : 2*0 - 3*0 + 0 = 0, simp,
    exact this },
  { -- Closed under addition
    intros u v hu hv,
    have : 2*(u.1 + v.1) - 3*(u.2 + v.2) + (u.3 + v.3) = 0,
    { rw [add_mul, add_mul, add_mul],
      simp [hu, hv] },
    exact this },
  { -- Closed under scalar multiplication
    intros λ u hu,
    have : 2*(λ•u.1) - 3*(λ•u.2) + (λ•u.3) = 0,
    { rw [smul_mul_assoc, smul_mul_assoc, smul_mul_assoc],
      simp [hu, λ•0=0] },
    exact this }
end

-- 2b: W = { (x,y,z) | xyz = 0 } is not subspace
def W : set (F^3) := { v : F^3 | v.1 * v.2 * v.3 = 0 }

lemma W_not_subspace : ¬is_subspace F W :=
begin
  intro h,
  let u : F^3 := (1, 1, 0),
  let v : F^3 := (0, 0, 1),
  have hu : u ∈ W, { simp },
  have hv : v ∈ W, { simp },
  have huv : u + v ∈ W, from h.2 u v hu hv,
  have h' : (u + v).1 * (u + v).2 * (u + v).3 = 1*1*1 = 1 ≠ 0,
  { simp [u, v] },
  contradiction
end

-- Question 3: Increasing sequences not subspace
def R_infty : Type := ℕ → ℝ
def X : set R_infty := { s : R_infty | ∀ n, s n ≤ s (n+1) }

lemma X_not_subspace : ¬is_subspace ℝ X :=
begin
  intro h,
  let s : R_infty := λ n, if n=0 then 0 else 1,
  have hs : s ∈ X,
  { intros n,
    cases n,
    { simp },
    { simp } },
  have h_neg : (-1 : ℝ) • s ∈ X, from h.3 (-1) s hs,
  have h' : (-1 • s) 0 = 0, { simp },
  have h'' : (-1 • s) 1 = -1, { simp },
  have : (-1 • s) 0 ≤ (-1 • s) 1, from h_neg 0,
  simp [h', h''] at this,
  contradiction
end

-- Question 4: u ∈ U, v ∈ V ⇨ v ∈ U ↔ u + v ∈ U
lemma subspace_mem_iff_add_mem {U : set V} [is_subspace F U] (u : U) (v : V) :
  v ∈ U ↔ (u + v) ∈ U :=
begin
  split,
  { intro hv, exact is_subspace.add_mem U u v (is_subspace.mem U u) hv },
  { intro huv,
    have : v = (-1)•u + (u + v),
    { rw [add_assoc, neg_one_smul_eq_neg, add_neg_self, zero_add] },
    exact is_subspace.add_mem U ((-1)•u) (u + v)
      (is_subspace.smul_mem U (-1) u (is_subspace.mem U u)) huv }
end

-- Question 5: Direct sum complements for xy-plane
def xy_plane : set (F^3) := { v : F^3 | v.3 = 0 }
def W1 : set (F^3) := { v : F^3 | v.1 = 0 ∧ v.2 = 0 }
def W2 : set (F^3) := { v : F^3 | v.1 = 0 ∧ v.2 = v.3 }

lemma xy_plane_is_subspace : is_subspace F xy_plane :=
begin
  split,
  { simp },
  { intros u v hu hv, simp [hu, hv] },
  { intros λ u hu, simp [hu] }
end

lemma W1_is_subspace : is_subspace F W1 :=
begin
  split,
  { simp },
  { intros u v hu hv, simp [hu, hv] },
  { intros λ u hu, simp [hu] }
end

lemma W2_is_subspace : is_subspace F W2 :=
begin
  split,
  { simp },
  { intros u v hu hv,
    simp [hu, hv, add_eq_add_iff_eq] },
  { intros λ u hu,
    simp [hu, smul_eq_smul_iff_eq] }
end

lemma xy_plane_dirsum_W1 : xy_plane ⊕ W1 = univ :=
begin
  rw direct_sum_eq_univ_iff,
  split,
  { -- xy_plane + W1 = ℝ³
    intros v,
    let u : F^3 := (v.1, v.2, 0),
    let w : F^3 := (0, 0, v.3),
    have hu : u ∈ xy_plane, { simp },
    have hw : w ∈ W1, { simp },
    use u, w,
    simp [u, w] },
  { -- Intersection is {0}
    intros v hv1 hv2,
    simp [xy_plane, W1] at hv1 hv2,
    exact ⟨hv1, hv2.1, hv2.2⟩ }
end

lemma xy_plane_dirsum_W2 : xy_plane ⊕ W2 = univ :=
begin
  rw direct_sum_eq_univ_iff,
  split,
  { -- xy_plane + W2 = ℝ³
    intros v,
    let u : F^3 := (v.1, v.2 - v.3, 0),
    let w : F^3 := (0, v.3, v.3),
    have hu : u ∈ xy_plane, { simp },
    have hw : w ∈ W2, { simp },
    use u, w,
    simp [u, w] },
  { -- Intersection is {0}
    intros v hv1 hv2,
    simp [xy_plane, W2] at hv1 hv2,
    have : v.3 = 0, from hv1,
    simp [this, hv2.1] }
end

-- Question 6: Subspace addition is commutative
lemma subspace_add_comm {U W : set V} [is_subspace F U] [is_subspace F W] :
  U + W = W + U :=
begin
  ext v,
  split,
  { rintro ⟨u, w, hw⟩,
    use w, u,
    rw [add_comm, hw] },
  { rintro ⟨w, u, hw⟩,
    use u, w,
    rw [add_comm, hw] }
end

-- Question 7: Only {0} has additive inverse subspace
lemma only_zero_has_inverse_subspace {U : set V} [is_subspace F U] :
  (∃ W : set V, [is_subspace F W] ∧ U + W = {0}) ↔ U = {0} :=
begin
  split,
  { intros h,
    obtain ⟨W, hW, hsum⟩ := h,
    have : U ⊆ {0},
    { intros u hu,
      have : u + 0 ∈ U + W, from is_subspace.add_mem U u 0 hu (is_subspace.zero_mem W),
      rw hsum at this,
      simp at this },
    exact subset_eq this (is_subspace.zero_subset U) },
  { intro h,
    use {0},
    split,
    { exact is_subspace_zero F V },
    { rw h,
      simp } }
end

-- Question 8: ℝ^ℝ = U_e ⊕ U_o
def U_e : set (ℝ → ℝ) := { f | ∀ x, f (-x) = f x }
def U_o : set (ℝ → ℝ) := { f | ∀ x, f (-x) = -f x }

lemma U_e_is_subspace : is_subspace ℝ U_e :=
begin
  split,
  { simp },
  { intros f g hf hg x,
    rw [add_neg, hf, hg] },
  { intros λ f hf x,
    rw [smul_neg, hf] }
end

lemma U_o_is_subspace : is_subspace ℝ U_o :=
begin
  split,
  { simp },
  { intros f g hf hg x,
    rw [add_neg, hf, hg, neg_add_neg] },
  { intros λ f hf x,
    rw [smul_neg, hf, neg_smul] }
end

lemma U_e_dirsum_U_o : U_e ⊕ U_o = univ :=
begin
  rw direct_sum_eq_univ_iff,
  split,
  { -- U_e + U_o = ℝ^ℝ
    intros f,
    def f_e (x) := (f x + f (-x))/2,
    def f_o (x) := (f x - f (-x))/2,
    have h_e : f_e ∈ U_e,
    { intro x,
      simp [f_e, neg_add_comm] },
    have h_o : f_o ∈ U_o,
    { intro x,
      simp [f_o, neg_sub, neg_neg] },
    have h_sum : f = f_e + f_o,
    { ext x,
      simp [f_e, f_o, add_sub_add_same] },
    use f_e, f_o, h_sum },
  { -- Intersection is {0}
    intros f hf he,
    ext x,
    have : f x = f_e x, from he x,
    have : f x = f_o x, from hf x,
    simp [f_e, f_o] at this,
    rw add_eq_neg_self_iff at this,
    exact this }
end

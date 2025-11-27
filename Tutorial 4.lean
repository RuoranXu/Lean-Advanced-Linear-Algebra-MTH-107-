import linear_algebra.basic
import linear_algebra.subspace
import linear_algebra.linear_map
import data.complex.basic
import polynomial.basic

variables {F : Type} [field F] {U V W : Type}
[add_comm_group U] [module F U]
[add_comm_group V] [module F V]
[add_comm_group W] [module F W]

-- Question 1: Linear map checks
namespace question1

-- 1a: T₁([x; y]) = xy is not linear
def T₁ : F^2 → F := λ v, v.1 * v.2

lemma T₁_not_linear : ¬linear_map F F^2 F T₁ :=
begin
  intro h,
  let u : F^2 := (1, 0),
  let v : F^2 := (0, 1),
  have h1 : T₁ (u + v) = T₁ (1, 1) = 1*1 = 1,
  { simp },
  have h2 : T₁ u + T₁ v = (1*0) + (0*1) = 0,
  { simp },
  have h_eq : 1 = 0, from h.map_add u v ▸ h1 ▸ h2,
  contradiction
end

-- 1b: T₂(z) = conjugate(z) is ℝ-linear (C as ℝ-vector space)
def T₂ : ℂ → ℂ := complex.conj

lemma T₂_R_linear : linear_map ℝ ℂ ℂ T₂ :=
begin
  split,
  { -- Additive
    intros z w,
    rw complex.conj_add,
    exact rfl },
  { -- ℝ-smul
    intros λ z,
    rw complex.conj_smul_real,
    exact rfl }
end

-- 1c: T₂(z) = conjugate(z) is not ℂ-linear
lemma T₂_C_not_linear : ¬linear_map ℂ ℂ ℂ T₂ :=
begin
  intro h,
  have h_i : T₂ (complex.I * 1) = complex.I * T₂ 1,
  { apply h.map_smul complex.I 1 },
  have left : T₂ (complex.I) = -complex.I,
  { simp },
  have right : complex.I * T₂ 1 = complex.I * 1 = complex.I,
  { simp },
  have : -complex.I = complex.I, from h_i ▸ left ▸ right,
  contradiction
end

-- 1d: T₃(p) = p(2) is linear
def T₃ : polynomial F → F := λ p, polynomial.eval 2 p

lemma T₃_linear : linear_map F (polynomial F) F T₃ :=
begin
  split,
  { -- Additive
    intros p q,
    rw polynomial.eval_add,
    exact rfl },
  { -- Smul
    intros λ p,
    rw polynomial.eval_smul,
    exact rfl }
end

end question1

-- Question 2: Kernel and image inclusions for compositions
variables {T : linear_map F U V} {S : linear_map F V W}

-- 2a: ker(T) ⊆ ker(S ∘ T)
lemma ker_T_subset_ker_ScompT : T.ker ⊆ (S ∘ T).ker :=
begin
  intros u hu,
  have : (S ∘ T) u = S (T u) = S 0 = 0,
  { rw hu, simp },
  exact this
end

-- 2b: im(S ∘ T) ⊆ im(S)
lemma im_ScompT_subset_im_S : (S ∘ T).image ⊆ S.image :=
begin
  intros w hw,
  obtain ⟨u, hu⟩ := hw,
  have : w = S (T u),
  { rw hu },
  exact ⟨T u, this⟩
end

-- Question 3: Injective map preserves linear independence
lemma injective_preserves_lin_indep (hT : T.injective) (v₁ ... vₖ : U)
  (h_ind : linear_independent F [v₁, ..., vₖ]) :
  linear_independent F [T v₁, ..., T vₖ] :=
begin
  intros λ₁ ... λₖ h_eq,
  have : T (λ₁•v₁ + ... + λₖ•vₖ) = 0,
  { rw [linear_map.map_add, linear_map.map_smul, h_eq] },
  have : λ₁•v₁ + ... + λₖ•vₖ = 0, from hT this,
  apply h_ind to this,
  exact ⟨λ₁=0, ..., λₖ=0⟩
end

-- Question 4: Surjective/injective iff right/left inverse
-- 4a: Surjective iff right inverse
lemma surjective_iff_right_inverse [finite_dimensional F W] :
  T.surjective ↔ ∃ S : linear_map F W U, T ∘ S = linear_map.id :=
begin
  split,
  { intro h_surj,
    obtain ⟨B, hB⟩ := finite_dimensional.exists_basis F W,
    def S (w : W) := ∑ (b ∈ B), (vector_space.basis.coord B w b) • (some (h_surj b)),
    have S_linear : linear_map F W U S,
    { split,
      { intros w₁ w₂,
        simp [S, finset.sum_add_distrib, vector_space.basis.coord_add] },
      { intros λ w,
        simp [S, finset.smul_sum, vector_space.basis.coord_smul] } },
    have TcompS_eq_id : T ∘ S = linear_map.id,
    { ext w,
      rw [linear_map.comp_apply, S],
      have : w = ∑ (b ∈ B), (vector_space.basis.coord B w b) • b,
      { exact vector_space.basis.sum_coord B w },
      rw this,
      simp [linear_map.map_sum, linear_map.map_smul, h_surj] },
    use S, exact TcompS_eq_id },
  { intro h,
    obtain ⟨S, h_eq⟩ := h,
    intro w,
    have : w = T (S w),
    { rw [← h_eq, linear_map.comp_apply, linear_map.id_apply] },
    exact ⟨S w, this⟩ }
end

-- 4b: Injective iff left inverse
lemma injective_iff_left_inverse [finite_dimensional F W] :
  T.injective ↔ ∃ S : linear_map F W U, S ∘ T = linear_map.id :=
begin
  split,
  { intro h_inj,
    have : T.image is a subspace of W, from linear_map.image_is_subspace,
    obtain ⟨B, hB⟩ := finite_dimensional.exists_basis F (T.image),
    def S (w : W) := ∑ (b ∈ B), (vector_space.basis.coord B w b) • (some (h_inj.symm b)),
    have S_linear : linear_map F W U S,
    { split,
      { intros w₁ w₂,
        simp [S, finset.sum_add_distrib, vector_space.basis.coord_add] },
      { intros λ w,
        simp [S, finset.smul_sum, vector_space.basis.coord_smul] } },
    have ScompT_eq_id : S ∘ T = linear_map.id,
    { ext u,
      rw [linear_map.comp_apply, S],
      have : T u = ∑ (b ∈ B), (vector_space.basis.coord B (T u) b) • b,
      { exact vector_space.basis.sum_coord B (T u) },
      rw this,
      simp [linear_map.map_sum, linear_map.map_smul, h_inj] },
    use S, exact ScompT_eq_id },
  { intro h,
    obtain ⟨S, h_eq⟩ := h,
    intro u,
    have : T u = 0 ⇒ u = 0,
    { intro hu,
      rw [← h_eq, linear_map.comp_apply, hu, linear_map.map_zero, linear_map.id_apply] },
    exact this }
end

-- Question 5: Rephrase ODE and recurrence as linear maps
-- 5a: ODE f'' - 3f' + 2f = 0
def C^∞(ℝ) : Type := ℝ → ℝ
def D : linear_map ℝ C^∞(ℝ) C^∞(ℝ) := λ f x, f'(x)
def T_ode : linear_map ℝ C^∞(ℝ) C^∞(ℝ) := D^2 - 3•D + 2•linear_map.id

lemma ode_equiv_ker_T : ∀ f : C^∞(ℝ), f'' - 3f' + 2f = 0 ↔ f ∈ T_ode.ker :=
begin
  intro f,
  ext x,
  rw [T_ode, linear_map.sub_apply, linear_map.add_apply, linear_map.smul_apply,
      linear_map.comp_apply, D, D, linear_map.id_apply],
  simp
end

-- 5b: Recurrence xₙ₊₂ = xₙ₊₁ + xₙ + 1
def ℝ^ℕ : Type := ℕ → ℝ
def S : linear_map ℝ ℝ^ℕ ℝ^ℕ := λ x n, x (n+1)
def c : ℝ^ℕ := λ _, 1
def T_rec : linear_map ℝ ℝ^ℕ ℝ^ℕ := S^2 - S - linear_map.id

lemma recurrence_equiv_Tc : ∀ x : ℝ^ℕ, (∀ n, x (n+2) = x (n+1) + x n + 1) ↔ T_rec x = c :=
begin
  intro x,
  ext n,
  rw [T_rec, linear_map.sub_apply, linear_map.add_apply, linear_map.comp_apply,
      S, S, linear_map.id_apply],
  simp
end

-- Question 6: Distributive property T(S₁ + S₂) = T S₁ + T S₂
variables {S₁ S₂ : linear_map F U V}
lemma comp_distrib : T ∘ (S₁ + S₂) = T ∘ S₁ + T ∘ S₂ :=
begin
  ext u,
  rw [linear_map.comp_apply, linear_map.add_apply, linear_map.comp_apply, linear_map.comp_apply],
  exact rfl
end

-- Question 7: S T = 0 iff im(T) ⊆ ker(S)
lemma comp_zero_iff_im_subset_ker : S ∘ T = linear_map.zero ↔ T.image ⊆ S.ker :=
begin
  split,
  { intro h,
    intros v hv,
    obtain ⟨u, hu⟩ := hv,
    have : S v = S (T u) = (S ∘ T) u = 0,
    { rw hu, h },
    exact this },
  { intro h,
    ext u,
    have : T u ∈ T.image,
    { exact ⟨u, rfl⟩ },
    have : S (T u) = 0, from h this,
    exact this }
end

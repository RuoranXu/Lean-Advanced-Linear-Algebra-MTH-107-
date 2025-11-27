import linear_algebra.basic
import linear_algebra.projection
import polynomial.basic
import data.real.basic
import data.complex.basic

universes u v w
variables {F : Type u} [field F] {V : Type v} [add_comm_group V] [module F V]
variables {W : Type w} [add_comm_group W] [module F W]
local notation `Id` := linear_map.id

-- Question 1: Projection equation solvability
lemma projection_solvable_iff (P : linear_map F V V) (hP : P.comp P = P) (b : V) :
  ∃ x : V, P x = b ↔ P b = b :=
begin
  split,
  { rintro ⟨x, hx⟩,
    calc P b = P (P x) : by rw hx
           = (P.comp P) x : by rw linear_map.comp_apply
           = P x : by rw hP
           = b : by rw hx },
  { intro h,
    use b,
    rw h }
end

-- Question 2: Complementary projection
lemma complementary_projection (P : linear_map F V V) (hP : P.comp P = P) :
  (Id - P).comp (Id - P) = Id - P :=
begin
  rw linear_map.comp_sub, rw linear_map.sub_comp, rw linear_map.comp_id,
  rw id_comp, rw P.comp_P, rw hP,
  simp [linear_map.add_sub, linear_map.sub_add],
end
where P.comp_P := linear_map.comp_self P

lemma ker_proj_eq_im_complementary (P : linear_map F V V) (hP : P.comp P = P) :
  P.ker = (Id - P).image :=
begin
  ext v,
  split,
  { intro hv : P v = 0,
    use v,
    rw linear_map.sub_apply, rw hv, rw linear_map.id_apply },
  { rintro ⟨u, hu : (Id - P) u = v⟩,
    rw hu at ⊢,
    calc P v = P (u - P u) : rfl
           = P u - P (P u) : linear_map.map_sub P u (P u)
           = P u - P u : by rw hP
           = 0 : sub_self }
end

lemma ker_complementary_eq_im_proj (P : linear_map F V V) (hP : P.comp P = P) :
  (Id - P).ker = P.image :=
by rw [← ker_proj_eq_im_complementary (Id - P), complementary_projection P hP]

-- Question 3: Matrix projection example
def A : matrix (fin 3) (fin 3) ℚ :=
λ i j, match (i, j) with
| (0, 0) := 2/3 | (0, 1) := 1/3 | (0, 2) := 1/3
| (1, 0) := 1/3 | (1, 1) := 2/3 | (1, 2) := -1/3
| (2, 0) := 1/3 | (2, 1) := -1/3 | (2, 2) := 2/3
end

lemma A_squared_eq_A : A * A = A :=
begin
  compute_matrix,
  all_goals { simp [rat.add, rat.mul, A] },
end

def b : fin 3 → ℚ := ![1, 1, 0]
def c : fin 3 → ℚ := ![1, -1, -1]

lemma Ax_b_consistent : ∃ x : fin 3 → ℚ, A.mul_vec x = b :=
begin
  use b,
  compute_matrix_mul_vec A b,
  simp [rat.add, rat.mul],
end

lemma Ax_c_inconsistent : ¬∃ x : fin 3 → ℚ, A.mul_vec x = c :=
begin
  intro h,
  rw matrix.mul_vec_eq_iff at h,
  have hA := A_squared_eq_A,
  rw ← hA at h,
  compute_matrix_mul_vec A c,
  simp [rat.add, rat.mul],
  contradiction,
end

lemma decompose_b : ∃ u u' : fin 3 → ℚ, u ∈ A.column_space ∧ u' ∈ A.kernel ∧ b = u + u' :=
begin
  use b, use 0,
  split, { exact ⟨b, rfl⟩ },
  split, { exact linear_map.zero_mem_ker (matrix.to_lin A) },
  simp,
end

lemma decompose_c : ∃ u u' : fin 3 → ℚ, u ∈ A.column_space ∧ u' ∈ A.kernel ∧ c = u + u' :=
begin
  use 0, use c,
  split, { exact ⟨0, rfl⟩ },
  split, { compute_matrix_mul_vec A c; simp; exact rfl },
  simp,
end

-- Question 4: T=2P-Id characterization
def T (P : linear_map F V V) : linear_map F V V := 2 • P - Id

lemma projection_iff_T_squared_id (P : linear_map F V V) :
  P.comp P = P ↔ T P • T P = Id :=
begin
  rw T,
  calc (2 • P - Id).comp (2 • P - Id) = 4 • (P.comp P) - 4 • P + Id :
    by rw [linear_map.comp_sub, linear_map.sub_comp, linear_map.smul_comp, linear_map.comp_smul,
           linear_map.smul_sub, linear_map.sub_smul, linear_map.comp_id, id_comp,
           linear_map.smul_self 2, linear_map.smul_self 2]
  split,
  { intro hP, rw hP, simp [linear_map.smul_sub, linear_map.sub_smul] },
  { intro h, rw h, simp, }
end

-- Question 5: Left/right inverses and consistency
lemma right_inverse_consistent (T : linear_map F V W) (S : linear_map F W V)
  (h : T.comp S = Id) (b : W) : T (S b) = b :=
by rw [linear_map.comp_apply, h, linear_map.id_apply]

lemma left_inverse_consistent_iff (T : linear_map F V W) (S : linear_map F W V)
  (h : S.comp T = Id) (b : W) :
  ∃ x : V, T x = b ↔ T (S b) = b :=
begin
  split,
  { rintro ⟨x, hx⟩,
    calc T (S b) = T (S (T x)) : by rw hx
               = (T.comp S) (T x) : by rw linear_map.comp_apply
               = Id (T x) : by rw h
               = T x : by rw linear_map.id_apply
               = b : by rw hx },
  { intro hb,
    use S b,
    rw hb }
end

-- Question 6: Differentiation operator inverses
def D : linear_map ℝ (polynomial ℝ) (polynomial ℝ) := polynomial.derivative ℝ

def T : linear_map ℝ (polynomial ℝ) (polynomial ℝ) :=
linear_map.of_fun (λ p, polynomial.integral 0 p)
(by { intros p q, simp [polynomial.integral_add], }
by { intros c p, simp [polynomial.integral_smul] })

lemma D_comp_T_eq_id : D.comp T = Id :=
begin
  ext p,
  induction p using polynomial.induction_on,
  { simp [polynomial.integral_zero, D, polynomial.derivative_zero] },
  { simp [polynomial.integral_monomial, D, polynomial.derivative_monomial,
          linear_map.add_apply, polynomial.add_derivative, ih] }
end

lemma D_no_left_inverse : ¬∃ S : linear_map ℝ (polynomial ℝ) (polynomial ℝ), S.comp D = Id :=
begin
  intro h,
  have inj_D : D.injective, by rw [linear_map.injective_iff_comp_id, h],
  contradiction,
end

-- Question 7: TS and ST are projections
lemma TS_projection (T : linear_map F V W) (S : linear_map F W V)
  (hT : T.comp S.comp T = T) (hS : S.comp T.comp S = S) :
  (T.comp S).comp (T.comp S) = T.comp S :=
by rw [linear_map.comp_assoc, hT, linear_map.comp_assoc]

lemma ST_projection (T : linear_map F V W) (S : linear_map F W V)
  (hT : T.comp S.comp T = T) (hS : S.comp T.comp S = S) :
  (S.comp T).comp (S.comp T) = S.comp T :=
by rw [linear_map.comp_assoc, hS, linear_map.comp_assoc]

lemma Im_ST_eq_Im_S (T : linear_map F V W) (S : linear_map F W V)
  (hS : S.comp T.comp S = S) :
  (S.comp T).image = S.image :=
begin
  ext v,
  split,
  { rintro ⟨u, hu⟩, exact ⟨T u, by rw [linear_map.comp_apply, hu]⟩ },
  { rintro ⟨w, hw⟩,
    use S w,
    rw [linear_map.comp_apply, hS, linear_map.comp_apply, hw] }
end

lemma Ker_ST_eq_Ker_T (T : linear_map F V W) (S : linear_map F W V)
  (hT : T.comp S.comp T = T) :
  (S.comp T).ker = T.ker :=
begin
  ext v,
  split,
  { intro hv,
    calc T v = T.comp S.comp T v : by rw hT
           = (T.comp S) (T v) : by rw linear_map.comp_apply
           = (T.comp S) 0 : by rw hv
           = 0 : linear_map.map_zero (T.comp S) },
  { intro hv,
    calc (S.comp T) v = S (T v) : by rw linear_map.comp_apply
                     = S 0 : by rw hv
                     = 0 : linear_map.map_zero S }
end

import linear_algebra.basic
import linear_algebra.matrix
import linear_algebra.change_basis
import data.real.basic
import trigonometry.basic

variables {F : Type} [field F] [has_trigonometric_functions F]

-- Question 1: Rotation matrix and composition
def R_θ (θ : F) : linear_map F (F^2) (F^2) :=
linear_map.matrix_to_lin
[ [cos θ, -sin θ],
  [sin θ, cos θ] ]

lemma R_θ_comp_R_φ (θ φ : F) : R_θ ∘ R_φ = R_(θ+φ) :=
begin
  ext v,
  rw [linear_map.comp_apply, R_θ, R_φ],
  compute_matrix_mul,
  simp [cos_add, sin_add]
end

-- Question 2: Reflection matrix
def S_θ (θ : F) : linear_map F (F^2) (F^2) :=
let v₁ := [cos θ, sin θ],
    v₂ := [-sin θ, cos θ],
    B := [v₁, v₂],
    [S]_B^B := matrix.diagonal [1, -1],
    P := change_basis_matrix B (standard_basis F 2),
    P_inv := matrix.inverse P
in linear_map.matrix_to_lin (P * [S]_B^B * P_inv)

lemma [S_θ]_B^B (θ : F) :
  linear_map.matrix_repr (S_θ θ) [v₁, v₂] [v₁, v₂] = matrix.diagonal [1, -1] :=
begin
  simp [S_θ, change_basis_matrix, matrix_repr]
end

lemma [S_θ]_std^std (θ : F) :
  linear_map.matrix_repr (S_θ θ) (standard_basis F 2) (standard_basis F 2) =
  [ [cos (2θ), sin (2θ)],
    [sin (2θ), -cos (2θ)] ] :=
begin
  compute_matrix_mul,
  simp [cos_add, sin_add, cos_double, sin_double]
end

-- Question 3: Stretching transformation
def B : vector_space.basis F (F^2) := [ [3,4], [-4,3] ]
def T : linear_map F (F^2) (F^2) :=
linear_map.of_basis B B (matrix.diagonal [2, 3])

lemma [T]_B^B : linear_map.matrix_repr T B B = matrix.diagonal [2, 3] :=
begin
  simp [T, linear_map.of_basis]
end

lemma [T]_std^std :
  linear_map.matrix_repr T (standard_basis F 2) (standard_basis F 2) =
  (matrix.from_cols B.1 B.2) * matrix.diagonal [2, 3] * (matrix.from_cols B.1 B.2)⁻¹ :=
begin
  rw change_basis_matrix_repr,
  exact rfl
end

-- Question 4: Inverse of differentiation operator
def D : linear_map F U U := polynomial.derivative F
def [D]_B^B_inv : matrix (fin 3) (fin 3) F :=
[ [1, -1, 1],
  [0, 1, -2],
  [0, 0, 1] ]

lemma D_inv_matrix : [D]_B^B * [D]_B^B_inv = matrix.id :=
begin
  compute_matrix_mul,
  simp
end

def f : U := 2•exp X - 2•X exp X + X² exp X
lemma D_f_eq_X2expX : D f = X² exp X :=
begin
  simp [D, f, D_expX, D_XexpX, D_X2expX],
  ring
end

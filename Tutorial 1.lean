import data.set.function
import linear_algebra.basic
import linear_algebra.matrix
import data.real.basic

-- Question 1: Functions between finite sets
variables (X : Type) (Y : Type)
def X1 : Type := unit -- X = {a} (unit type has exactly one element)
def Y1 : Type := bool -- Y = {b, c} (bool has two elements: ff, tt)

-- 1a: All functions X→Y
def f1 : X1 → Y1 := λ _, ff
def f2 : X1 → Y1 := λ _, tt
lemma all_functions_XY : ∀ f : X1 → Y1, f = f1 ∨ f = f2 :=
begin
  intro f,
  cases f (),
  { left, refl },
  { right, refl }
end

-- 1b: All functions Y→X
def g : Y1 → X1 := λ _, ()
lemma unique_function_YX : ∀ f : Y1 → X1, f = g :=
begin
  intro f,
  ext y,
  cases y,
  { refl },
  { refl }
end

-- 1c: Compositions
lemma comp_f1_g : f1 ∘ g = λ (y : Y1), ff :=
begin
  ext y, refl
end
lemma comp_f2_g : f2 ∘ g = λ (y : Y1), tt :=
begin
  ext y, refl
end
lemma comp_g_f1 : g ∘ f1 = id :=
begin
  ext x, refl
end
lemma comp_g_f2 : g ∘ f2 = id :=
begin
  ext x, refl
end

-- Question 2: Injective/surjective compositions
variables {X Y Z : Type} {f : X → Y} {g : Y → Z}

-- 2a: Composition of injectives is injective
lemma comp_injective : injective f → injective g → injective (g ∘ f) :=
begin
  intros hf hg a b h,
  apply hf,
  apply hg,
  exact h
end

-- 2b: Composition of surjectives is surjective
lemma comp_surjective : surjective f → surjective g → surjective (g ∘ f) :=
begin
  intros hf hg z,
  obtain ⟨y, hy⟩ := hg z,
  obtain ⟨x, hx⟩ := hf y,
  use x,
  rw [function.comp_apply, hx, hy]
end

-- 2c: Consequences of composition injectivity/surjectivity
lemma comp_injective_implies_f_injective : injective (g ∘ f) → injective f :=
begin
  intros h a b ha,
  apply h,
  rw [function.comp_apply, ha]
end

lemma comp_surjective_implies_g_surjective : surjective (g ∘ f) → surjective g :=
begin
  intros h z,
  obtain ⟨x, hx⟩ := h z,
  use f x,
  rw [function.comp_apply, hx]
end

-- Question 3: Distributive properties of F^m
variables {F : Type} [field F] {m : ℕ}
lemma distr1 (a : F) (u v : F^m) : a • (u + v) = a • u + a • v :=
begin
  ext i,
  rw [finvec.smul_add, finvec.add_smul]
end

lemma distr2 (a b : F) (u : F^m) : (a + b) • u = a • u + b • u :=
begin
  ext i,
  rw [finvec.add_smul, finvec.smul_add]
end

-- Question 4: g∘f=id does not imply f∘g=id
example : ∃ (X Y : Type) (f : X → Y) (g : Y → X), g ∘ f = id ∧ f ∘ g ≠ id :=
begin
  use X1, Y1, f1, g,
  split,
  { exact comp_g_f1 X1 Y1 },
  { intro h,
    have h' : (f1 ∘ g) tt = tt, by rw h; refl,
    rw comp_f1_g X1 Y1 at h',
    contradiction }
end

-- Question 5: Left/right inverses for finite sets
variables [fintype X] [fintype Y] {f : X → Y}

-- 5a: Injective implies left inverse
lemma injective_has_left_inverse : injective f → ∃ g : Y → X, g ∘ f = id :=
begin
  intros hf,
  cases fintype.eq_empty_or_nonempty X,
  { use λ _, (),
    ext x, cases x },
  { obtain ⟨x0, _⟩ := h,
    def g (y : Y) := if h : ∃ x, f x = y then (the unique x where f x = y) else x0,
    use g,
    ext x,
    specialize hf (g (f x)) x,
    rw [dif_pos ⟨x, rfl⟩] at hf,
    exact hf }
end

-- 5b: Surjective implies right inverse
lemma surjective_has_right_inverse : surjective f → ∃ g : Y → X, f ∘ g = id :=
begin
  intros hf,
  def g (y : Y) := some (hf y),
  use g,
  ext y,
  rw [dif_pos (hf y)]
end

-- Question 7: Determinant and inverse of matrix A
def A : matrix (fin 3) (fin 3) ℝ :=
λ i j, match (i, j) with
| (0, 0) := 2 | (0, 1) := -2 | (0, 2) := 1
| (1, 0) := 3 | (1, 1) := 5 | (1, 2) := 0
| (2, 0) := -1 | (2, 1) := 3 | (2, 2) := 4
end

-- Compute determinant ( Lean 内置行列式计算 )
lemma det_A : det A = 49 :=
begin
  compute_matrix_det A,
  simp
end

-- Compute inverse ( 验证 A * A⁻¹ = I )
def A_inv : matrix (fin 3) (fin 3) ℝ :=
λ i j, match (i, j) with
| (0, 0) := 20/49 | (0, 1) := 11/49 | (0, 2) := -5/49
| (1, 0) := -12/49 | (1, 1) := 9/49 | (1, 2) := 3/49
| (2, 0) := 14/49 | (2, 1) := -4/49 | (2, 2) := 16/49
end

lemma A_mul_Ainv_eq_id : A * A_inv = matrix.id :=
begin
  compute_matrix_mul A A_inv,
  simp [rat.add, rat.mul]
end

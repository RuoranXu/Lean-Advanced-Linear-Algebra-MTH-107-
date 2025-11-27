import linear_algebra.inner_product_space
import data.real.basic
import calculus.smooth
import trigonometry.basic

variables {F : Type} [normed_field F] [inner_product_space F V]

-- Question 1: Norm calculation
lemma norm_3u_minus_2v (u v : V) (hu : ⟪u, u⟫ = 4) (hv : ⟪v, v⟫ = 6) (huv : ⟪u, v⟫ = -2) :
  ∥3•u - 2•v∥ = √(3²*4 + (-2)²*6 - 2*3*(-2)*2) :=
begin
  rw inner_product_space.norm_sq_eq_inner,
  simp [inner_product_space.inner_smul, inner_product_space.inner_sub,
        hu, hv, huv, ring]
end

-- Question 2: Orthogonal projection of x onto 1
def ⟨p, q⟩ : polynomial ℝ → polynomial ℝ → ℝ :=
λ p q, ∫₀¹ (p x * q x) dx

def p : polynomial ℝ := (∫₀¹ x dx) / (∫₀¹ 1 dx) * 1
def q : polynomial ℝ := X - p

lemma p_orthogonal_q : ⟨p, q⟩ = 0 :=
begin
  simp [p, q, integral_mul, integral_add, integral_const, integral_X],
  ring
end

-- Question 3: Converse of Pythagorean theorem (real inner product)
lemma converse_pythagorean (V : Type) [inner_product_space ℝ V] (u v : V) :
  ∥u∥² + ∥v∥² = ∥u + v∥² ↔ ⟪u, v⟫ = 0 :=
begin
  rw [inner_product_space.norm_sq_eq_inner, inner_product_space.norm_sq_eq_inner,
      inner_product_space.norm_sq_eq_inner, inner_product_space.inner_add],
  simp [add_comm, add_left_inj],
  ring
end

-- Question 4: Cauchy-Schwarz implies mean of squares ≥ square of mean
lemma mean_squares_ge_square_mean (x₁ ... xₙ : ℝ) :
  (∑ xᵢ / n)² ≤ (∑ xᵢ²) / n :=
begin
  let u := [x₁, ..., xₙ],
  let v := [1, ..., 1],
  have : ⟪u, v⟫² ≤ ∥u∥² * ∥v∥², from cauchy_schwarz u v,
  simp [inner_product_space.inner_finvec, inner_product_space.norm_sq_finvec] at this,
  divide both sides by n²,
  simp
end

-- Question 5: Dot product derivative rule
lemma dot_product_derivative {n : ℕ} (γ δ : ℝ → ℝⁿ) [smooth γ] [smooth δ] :
  ∀ t, (γ t • δ t)' = γ' t • δ t + γ t • δ' t :=
begin
  intro t,
  rw finvec.dot_product,
  simp [smooth.deriv_sum, smooth.deriv_mul]
end

-- Question 6: Constant speed implies velocity ⊥ acceleration
lemma constant_speed_velocity_perp_acceleration {n : ℕ} (γ : ℝ → ℝⁿ) [smooth γ]
  (h_const_speed : ∀ t, ∥γ' t∥ = c) :
  ∀ t, ⟪γ' t, γ'' t⟫ = 0 :=
begin
  intro t,
  have : (∥γ' t∥²)' = 0, from (h_const_speed t).symm ▸ deriv_const c,
  rw inner_product_space.norm_sq_eq_inner at this,
  simp [dot_product_derivative, this]
end

-- Question 7: Correlation coefficient ∈ [-1, 1]
def r (x y : ℝⁿ) : ℝ :=
let x̄ := (∑ xᵢ) / n,
    ȳ := (∑ yᵢ) / n,
    x̃ᵢ := xᵢ - x̄,
    ỹᵢ := yᵢ - ȳ
in (∑ x̃ᵢ ỹᵢ) / (√(∑ x̃ᵢ²) * √(∑ ỹᵢ²))

lemma correlation_bounded : -1 ≤ r x y ≤ 1 :=
begin
  let x̃ := λ i, x i - (∑ x j)/n,
  let ỹ := λ i, y i - (∑ y j)/n,
  have : ⟪x̃, ỹ⟫² ≤ ∥x̃∥² * ∥ỹ∥², from cauchy_schwarz x̃ ỹ,
  simp [inner_product_space.inner_finvec, inner_product_space.norm_sq_finvec] at this,
  divide both sides by (∥x̃∥² * ∥ỹ∥²),
  simp [r]
end

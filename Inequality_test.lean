import Mathlib

namespace P1_MAT351_2025_Q4

theorem sum_of_squares (a b : ℝ)(h : a ≠ 0 ∨ b ≠ 0) : a^2+b^2>0 := by
  cases h with
  | inl ha =>
    have ha2 : 0 < a^2 := sq_pos_of_ne_zero ha
    have hb2 : 0 <= b^2 := sq_nonneg b
    exact add_pos_of_pos_of_nonneg ha2 hb2
  | inr hb =>
    have ha2 : 0 <= a^2 := sq_nonneg a
    have hb2 : 0 < b^2 := sq_pos_of_ne_zero hb
    simpa [add_comm] using add_pos_of_pos_of_nonneg hb2 ha2

-- Q4(a): over ℝ, if (a,b) ≠ (0,0) then a^2+ab+b^2 > 0
theorem q4a (a b : ℝ) (h : a ≠ 0 ∨ b ≠ 0) : a^2 + a * b + b^2 > 0 := by
  have hsum : 0<a^2+b^2 := sum_of_squares a b h
  by_cases hab: 0<=a*b
  .
    have hpos : 0 < (a^2+b^2) + a*b := add_pos_of_pos_of_nonneg hsum hab
    simpa [add_assoc, add_comm] using hpos
  .
    have hneg1 : 0 > a*b := lt_of_not_ge hab
    have hneg2 : 0 < -(a*b) := neg_pos.mpr hneg1
    have hsq : 0 <= (a+b)^2 := sq_nonneg (a+b)
    have hneg3 : 0 < -(a*b) + (a+b)^2  := add_pos_of_pos_of_nonneg hneg2 hsq
    have hrew : -(a*b) + (a+b)^2 = a^2 + a*b + b^2 := by ring
    simpa [hrew] using hneg3

-- Q4(b): over ℝ, if a > b then a^3 > b^3
 theorem q4b (a b : ℝ) (h : a > b) : a^3 > b^3 := by
  have heq : a^3 - b^3 = (a-b) * (a^2 + a*b + b^2) := by ring
  have hpos1 : 0 < a-b := sub_pos.mpr h
  have hab : a ≠ 0 ∨ b ≠ 0  := by
    by_cases ha: a ≠ 0
    .
      exact Or.inl ha
    .
      have ha0 : a = 0 := by simpa using ha
      have hbneg : b < 0 := by simpa [ha0] using h
      have hb0 : b ≠ 0 := ne_of_lt hbneg
      exact Or.inr hb0
  have hpos2 : a^2 + a*b + b^2 > 0 := q4a a b hab
  have hmul : 0 < (a-b) * (a^2 + a*b + b^2) := mul_pos hpos1 hpos2
  have hpos3 : 0 < a^3 - b^3 := by simpa [heq] using hmul
  exact sub_pos.mp hpos3

end P1_MAT351_2025_Q4

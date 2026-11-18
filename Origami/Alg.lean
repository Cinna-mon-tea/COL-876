import Origami.Basic

namespace Origami

inductive AlgConstrNum : ℝ → Prop
  | rat (q : ℚ) : AlgConstrNum q
  | add {x y} : AlgConstrNum x → AlgConstrNum y → AlgConstrNum (x + y)
  | mul {x y} : AlgConstrNum x → AlgConstrNum y → AlgConstrNum (x * y)
  | neg {x} : AlgConstrNum x → AlgConstrNum (-x)
  | inv {x} : AlgConstrNum x → AlgConstrNum x⁻¹
  | sqrt {x} : AlgConstrNum x → AlgConstrNum (Real.sqrt x)
  | cubic {a b c r : ℝ} : AlgConstrNum a → AlgConstrNum b → AlgConstrNum c →
      r ^ 3 + a * r ^ 2 + b * r + c = 0 → AlgConstrNum r

def AlgConstrLine (f : Line) : Prop :=
  ∃ a b c : ℝ, AlgConstrNum a ∧ AlgConstrNum b ∧ AlgConstrNum c ∧ (a ≠ 0 ∨ b ≠ 0) ∧
    ∀ z : ℂ, z ∈ f ↔ a * z.re + b * z.im + c = 0

namespace AlgConstrNum
theorem zero : AlgConstrNum 0 := by exact_mod_cast AlgConstrNum.rat 0
theorem one : AlgConstrNum 1 := by exact_mod_cast AlgConstrNum.rat 1
theorem sub {x y} (hx : AlgConstrNum x) (hy : AlgConstrNum y) : AlgConstrNum (x - y) := by
  rw [sub_eq_add_neg]
  exact .add hx hy.neg
theorem div {x y} (hx : AlgConstrNum x) (hy : AlgConstrNum y) : AlgConstrNum (x / y) := by
  rw [div_eq_mul_inv]
  exact .mul hx hy.inv
theorem sq {x} (hx : AlgConstrNum x) : AlgConstrNum (x ^ 2) := by
  rw [pow_two]
  exact .mul hx hx
theorem pow {x : ℝ} (hx : AlgConstrNum x) : ∀ n : ℕ, AlgConstrNum (x ^ n)
  | 0 => by simpa using AlgConstrNum.one
  | n + 1 => by rw [pow_succ]; exact (AlgConstrNum.pow hx n).mul hx
theorem ofNat (n : ℕ) [n.AtLeastTwo] : AlgConstrNum (OfNat.ofNat n : ℝ) := by
  exact_mod_cast AlgConstrNum.rat n
theorem of_quad {a b r : ℝ}
  (ha : AlgConstrNum a)
  (hb : AlgConstrNum b)
  (h : r ^ 2 + a * r + b = 0) :
    AlgConstrNum r := AlgConstrNum.cubic ha hb AlgConstrNum.zero (by linear_combination r * h)
end AlgConstrNum

syntax "is_oc_core" : tactic
macro_rules
  | `(tactic| is_oc_core) => `(tactic| first
    | assumption
    | exact AlgConstrNum.zero
    | exact AlgConstrNum.one
    | exact AlgConstrNum.ofNat _
    | (apply AlgConstrNum.sub <;> is_oc_core)
    | (apply AlgConstrNum.div <;> is_oc_core)
    | (apply AlgConstrNum.add <;> is_oc_core)
    | (apply AlgConstrNum.mul <;> is_oc_core)
    | (apply AlgConstrNum.neg; is_oc_core)
    | (apply AlgConstrNum.inv; is_oc_core)
    | (apply AlgConstrNum.sqrt; is_oc_core)
    | (apply AlgConstrNum.pow; is_oc_core)
    | (refine And.intro ?_ ?_ <;> is_oc_core))

macro "is_oc" : tactic => `(tactic| (try casesm* _ ∧ _) <;> is_oc_core)

theorem AlgConstrNum.of_cubic_fn {G : ℝ → ℝ} {c3 s : ℝ} (hc3 : c3 ≠ 0) (hI : AlgConstrNum c3)
    (hG : ∀ x, G x = c3 * x ^ 3 + ((G 1 + G (-1)) / 2 - G 0) * x ^ 2
      + ((G 1 - G (-1)) / 2 - c3) * x + G 0)
    (h0 : AlgConstrNum (G 0)) (h1 : AlgConstrNum (G 1)) (hm : AlgConstrNum (G (-1))) (hs : G s = 0) : AlgConstrNum s := by
  have hdiv : c3 * c3⁻¹ = 1 := mul_inv_cancel₀ hc3
  have hroot : s ^ 3 + ((G 1 + G (-1)) / 2 - G 0) / c3 * s ^ 2
      + ((G 1 - G (-1)) / 2 - c3) / c3 * s + G 0 / c3 = 0 := by
    rw [hG s] at hs
    linear_combination c3⁻¹ * hs - s ^ 3 * hdiv
  exact AlgConstrNum.cubic (by is_oc) (by is_oc) (by is_oc) hroot

end Origami

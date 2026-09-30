import Mathlib

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  have hp : p := h.left
  have hqr : q ∨ r := h.right
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
| inl hqr =>
              exact Or.inl ⟨hp, hqr⟩
| inr hqr =>
              exact Or.inr ⟨hp, hqr⟩

example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

def f8 (x y z : Nat) : Nat :=
match x, y, z with
| 8, _, _ => y
| _, 8, _ => y
| _, _, 8 => y
| _, _, _ => 1

example (x y z w : Nat) : x ≠ 8 → y ≠ 8 → z ≠ 8 → z = w → f8 x y w = 1 := by
  intros
  simp [f8]
  split <;> (first | contradiction | rfl)

def g (x y : List Nat) : Nat :=
match x, y with
| [a, b], _ => a + b + 1
| _, [b, _] => b + 1
| _, _ => 1

example (x y : List Nat) (h : g x y = 0) : False := by
  simp [g] at h
  split at h <;> contradiction

variable (a b c d e : Nat)
example (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) : a = e :=
  calc
  a = b := h1
  _ = c + 1 := h2
  _ = d + 1 := congrArg (Nat.succ) h3
  _ = 1 + d := Nat.add_comm d 1
  _ = e := Eq.symm h4

example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
  _ = b := h1
  _ < b + 1 := Nat.lt_succ_self b
  _ ≤ c + 1 := Nat.succ_le_succ h2
  _ < d := h3


def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

def divides_transitive {x y z : Nat} (h1 : divides x y) (h2 : divides y z) : divides x z := by
  simp [divides] at *
  let ⟨k1, d1⟩ := h1
  let ⟨k2, d2⟩ := h2
  exists (k1*k2)
  rw [<- d2, <- d1, <- Nat.mul_assoc, Nat.mul_comm k1 k2]

instance : Trans divides divides divides
where
trans := divides_transitive

variable (x y z : Nat)
example (h1 : divides x y) (h2 : y = z) : divides x (2*z) :=
  calc
  divides x y := h1
  _ = z := h2
  divides _ (2*z) := by
    -- simp [divides]
    rw[divides]
    exists 2

-- 31 august

example (P Q : Prop) : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      apply h
      apply And.intro <;> assumption
    · left
      assumption
  -- · intro h
  --   by_cases hP : P
  --   · have hnQ : ¬Q := by
  --       false_or_by_contra
  --       have hQ : Q := by sorry
  --       contradiction

  · sorry

/-
  Have: a - 3 = 2b
  a^2 = 4b^2 + 12b + 9
  a^2 - a + 3 = 4b^2 + 12b + 12 - 2b - 3 = 4b^2 + 10b + 9
  Show: a^2 - a + 3 = 4b^2 + 10b + 9
-/

example (a b : Nat) (h : a - 3 = 2 * b) : a^2 - a + 3 = 4 * b^2 + 10*b + 9 :=
  have h1 : a = 2*b + 3 := by
    -- rw[<- Nat.add_right_cancel]
    sorry
  calc
  a^2 - a + 3 = (2*b + 3)^2 - (2*b + 3) + 3 := by rw[h1]
  _ = 4*b^2 + 12*b + 9 - 2*b - 3 + 3 := by grind
  _ = 4*b^2 + 10*b + 9 := by grind

example (a b : ℚ) (h1 : a - b = 4) (h2 : a*b = 1) : (a + b)^2 = 20 :=
calc
(a + b)^2 = a^2 + b^2 - 2*a*b + 4*a*b := by ring
_ = (a - b)^2 + 4*(a*b) := by ring
_ = 4^2 + 4*(1) := by rw[h1, h2]
_ = 20 := by ring

example : {a : ℕ | 4 ∣ a} ⊆ {b : ℕ | 2 ∣ b} := by
  -- dsimp [Set.subset_def]
  simp
  intro a ha
  show ∃ k : ℕ, a = 2 * k
  obtain ⟨c, hc⟩ := ha
  exists c * 2
  ring
  rw [Nat.mul_comm]
  assumption

example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2*x ≥ 3) : y > 3 :=
  calc
  -- y ≥ 3 - 2*x := by omega
  -- _ > 3 - 2*0 := by omega
  -- just this much works as well.

  y = y + 2*x - 2*x := by ring
  _ ≥ 3 - 2*x := by rel [hy]
  -- _ = 3 - 2*x - 6 + 6 := by ring
  _ = 3 - 2*(x + 3) + 6 := by ring
  _ ≥ 3 - 2*2 + 6 := by rel [hx]
  -- _ = 5 := by simp
  -- _ > 3 := by trivial
  _ > 3 := by omega

-- testing if implicit type declarations can still lead to contradiction.
theorem test_implicit {n m : Nat} : n + 1 = 0 → m + 1 = 0 → n = m := by
  intro h1 h2
  rw [<- h2] at h1
  exact Nat.add_right_cancel h1

theorem test_implicit_using_false {n m : Nat} : n + 1 = 0 → m + 1 = 0 → n = m := by
  intro h1
  contradiction

theorem t1 {α β : Prop}:
  ((α → β) → α) → ¬¬ α := by

  intro h1 h2
  -- have h3 : α ↔ False := by
  rw [<- false_iff α] at h2
  rw [<- h2, false_implies, true_implies] at h1
  assumption

#check false_imp_iff
#check false_iff
#check false_implies

-- 7 september
#check Nat
#check Type
#check Type 1

universe u v
def createprod {α : Type u} {β : α → Type v} (a : α) (b : β a) :
  α × β a := (a, b)

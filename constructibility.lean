import Mathlib
import SystemE.Theory.Sorts.Primitives
import SystemE.Theory.Relations

namespace LeanGeo
inductive IsOrigamiConstructible : ℝ → Type where
  | rat (q : ℚ) : IsOrigamiConstructible q
  | add {x y : ℝ} : IsOrigamiConstructible x → IsOrigamiConstructible y →
      IsOrigamiConstructible (x + y)
  | mul {x y : ℝ} : IsOrigamiConstructible x → IsOrigamiConstructible y →
      IsOrigamiConstructible (x * y)
  | neg {x : ℝ} : IsOrigamiConstructible x → IsOrigamiConstructible (-x)
  | inv {x : ℝ} : IsOrigamiConstructible x → IsOrigamiConstructible x⁻¹
  | sqrt {x : ℝ} : IsOrigamiConstructible x → IsOrigamiConstructible (Real.sqrt x)
  | cbrt {x : ℝ} : IsOrigamiConstructible x →
      IsOrigamiConstructible (x ^ ((1:ℝ)/3))

def isOrigamiConstructible (x : ℝ) : Prop :=
  Nonempty (IsOrigamiConstructible x)

def OrigamiConstructible : Set ℝ := {x | isOrigamiConstructible x}

noncomputable def origamiField : ∀ {x : ℝ}, IsOrigamiConstructible x →
    IntermediateField ℚ ℝ
  | _, .rat _ => ⊥
  | _, .add hx hy => origamiField hx ⊔ origamiField hy
  | _, .mul hx hy => origamiField hx ⊔ origamiField hy
  | _, .neg hx => origamiField hx
  | _, .inv hx => origamiField hx
  | _, .sqrt (x := y) hx =>
      origamiField hx ⊔ IntermediateField.adjoin ℚ {Real.sqrt y}
  | _, .cbrt (x := y) hx =>
      origamiField hx ⊔ IntermediateField.adjoin ℚ {y ^ ((1:ℝ)/3)}

lemma mem_origamiField {x : ℝ} (hx : IsOrigamiConstructible x) :
    x ∈ origamiField hx := by
  induction hx with
  | rat q =>
    simp [origamiField]
  | add hx hy ihx ihy =>
    simp only [origamiField]
    apply IntermediateField.add_mem
    · have h : origamiField hx ≤ origamiField hx ⊔ origamiField hy := le_sup_left
      exact h ihx
    · have h : origamiField hy ≤ origamiField hx ⊔ origamiField hy := le_sup_right
      exact h ihy
  | mul hx hy ihx ihy =>
    simp only [origamiField]
    apply IntermediateField.mul_mem
    · have h : origamiField hx ≤ origamiField hx ⊔ origamiField hy := le_sup_left
      exact h ihx
    · have h : origamiField hy ≤ origamiField hx ⊔ origamiField hy := le_sup_right
      exact h ihy
  | neg hx ihx =>
    simp only [origamiField]
    exact IntermediateField.neg_mem _ ihx
  | inv hx ihx =>
    simp only [origamiField]
    exact IntermediateField.inv_mem _ ihx
  | sqrt hx ihx =>
    rename_i x
    simp only [origamiField]
    have h : IntermediateField.adjoin ℚ {Real.sqrt x} ≤
            origamiField hx ⊔ IntermediateField.adjoin ℚ {Real.sqrt x} := le_sup_right
    exact h (IntermediateField.mem_adjoin_simple_self ℚ _)
  | cbrt hx ihx =>
    rename_i x
    simp only [origamiField]
    have h : IntermediateField.adjoin ℚ {x ^ ((1:ℝ)/3)} ≤
            origamiField hx ⊔ IntermediateField.adjoin ℚ {x ^ ((1:ℝ)/3)} := le_sup_right
    exact h (IntermediateField.mem_adjoin_simple_self ℚ _)

def isTwoThree (n : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ n → p = 2 ∨ p = 3

lemma TwoThree_divisor {n m : ℕ} (h : n ∣ m) (hm : isTwoThree m) :
    isTwoThree n := by
  intro p hprime hpn
  apply hm p hprime
  exact dvd_trans hpn h

lemma TwoThree_prod {n m : ℕ} (hn : isTwoThree n) (hm : isTwoThree m) :
    isTwoThree (n * m) := by
  rw [isTwoThree]
  intro p hp hpnm
  rcases hp.dvd_mul.mp hpnm with hpn | hpm
  · exact hn p hp hpn
  · exact hm p hp hpm

-- How to simplify the following two theorems?
lemma TwoThree_two : isTwoThree 2 := by
  intro p hp hpd
  left
  have h := Nat.le_of_dvd (by simp) hpd
  cases p with
  | zero => contradiction
  | succ n =>
    cases n with
    | zero => contradiction
    | succ m => simp at *; assumption
  -- rcases p <;> {simp; by_contra; try contradiction;}

lemma TwoThree_three : isTwoThree 3 := by
  intro p hp hpd
  right
  have h := Nat.le_of_dvd (by simp) hpd
  cases p with
  | zero => contradiction
  | succ n =>
    cases n with
    | zero => contradiction
    | succ m =>
      simp at *
      have h1 : m <= 1 := by omega
      cases m with
      | zero => contradiction
      | succ k => simp at *; assumption

-- the following 3 are true theorems, not present in MathLib.
axiom field_comp_divides_prod (K L : IntermediateField ℚ ℝ) :
    Module.finrank ℚ ↥(K ⊔ L) ∣
    Module.finrank ℚ ↥K * Module.finrank ℚ ↥L

axiom finrank_adjoin_sqrt_dvd (x : ℝ) :
    Module.finrank ℚ ↥(IntermediateField.adjoin ℚ {Real.sqrt x}) ∣ 2

axiom finrank_adjoin_cbrt_dvd (x : ℝ) :
    Module.finrank ℚ ↥(IntermediateField.adjoin ℚ {x ^ ((1:ℝ)/3)}) ∣ 3

theorem Alperin_forward {x : ℝ} (hx : IsOrigamiConstructible x) :
    isTwoThree (Module.finrank ℚ (origamiField hx)) := by
  induction hx with
  | rat q =>
    rw [origamiField]
    intro p hp hpd
    simp [IntermediateField.finrank_bot] at hpd
    rw [hpd] at hp
    have f := Nat.prime_one_false hp
    contradiction

  | add hx hy ihx ihy =>
    simp [origamiField]
    apply TwoThree_divisor _ (TwoThree_prod ihx ihy)
    exact field_comp_divides_prod _ _

  | mul hx hy ihx ihy =>
    simp [origamiField]
    apply TwoThree_divisor _ (TwoThree_prod ihx ihy)
    exact field_comp_divides_prod _ _

  | sqrt hx ihx =>
      rename_i x
      simp [origamiField]
      apply TwoThree_divisor _ (TwoThree_prod TwoThree_two ihx)

      let K := origamiField hx
      let L := IntermediateField.adjoin ℚ {Real.sqrt x}

      have h1 : Module.finrank ℚ ↥(K ⊔ L) ∣ Module.finrank ℚ ↥K * Module.finrank ℚ ↥L :=
        field_comp_divides_prod K L
      have h2 : Module.finrank ℚ ↥L ∣ 2 :=
        finrank_adjoin_sqrt_dvd x

      calc Module.finrank ℚ ↥(K ⊔ L)  ∣ Module.finrank ℚ ↥K * Module.finrank ℚ ↥L := h1
        _                             ∣ Module.finrank ℚ ↥K * 2 := Nat.mul_dvd_mul_left _ h2
        _                             = 2 * Module.finrank ℚ ↥K := by ring

    | cbrt hx ihx =>
      rename_i x
      simp [origamiField]
      apply TwoThree_divisor _ (TwoThree_prod TwoThree_three ihx)

      let K := origamiField hx
      let L := IntermediateField.adjoin ℚ {x ^ ((1:ℝ)/3)}

      have h1 : Module.finrank ℚ ↥(K ⊔ L) ∣ Module.finrank ℚ ↥K * Module.finrank ℚ ↥L :=
        field_comp_divides_prod K L
      have h2 : Module.finrank ℚ ↥L ∣ 3 :=
        finrank_adjoin_cbrt_dvd x

      calc Module.finrank ℚ ↥(K ⊔ L)  ∣ Module.finrank ℚ ↥K * Module.finrank ℚ ↥L := h1
        _                             ∣ Module.finrank ℚ ↥K * 3 := Nat.mul_dvd_mul_left _ h2
        _                             = 3 * Module.finrank ℚ ↥K := by ring

  | neg hx ihx => assumption
  | inv hx ihx => assumption


-- existence of a 2-3 tower (follows from structure theorem for Abelian groups)
axiom TwoThree_tower (K : IntermediateField ℚ ℝ)
    (hK : isTwoThree (Module.finrank ℚ ↥K)) :
    ∃ (n : ℕ) (tower : Fin (n+1) → IntermediateField ℚ ℝ),
      tower ⟨0, Nat.zero_lt_succ n⟩ = ⊥ ∧
      tower ⟨n, Nat.lt_succ_self n⟩ = K ∧
      ∀ i : Fin n,
        tower i.castSucc ≤ tower i.succ ∧
        (Module.finrank ℚ ↥(tower i.succ) =
           2 * Module.finrank ℚ ↥(tower i.castSucc) ∨
        Module.finrank ℚ ↥(tower i.succ) =
           3 * Module.finrank ℚ ↥(tower i.castSucc))

-- degree-2 extension is generated by a square root
axiom degree2_is_sqrt (K L : IntermediateField ℚ ℝ) (hKL : K ≤ L)
    (hdeg : Module.finrank ℚ ↥L = 2 * Module.finrank ℚ ↥K) :
    ∃ α : ℝ, α ∈ K ∧
      L = K ⊔ IntermediateField.adjoin ℚ {Real.sqrt α}

-- degree-3 extension is generated by a cube root
axiom degree3_is_cbrt (K L : IntermediateField ℚ ℝ) (hKL : K ≤ L)
    (hdeg : Module.finrank ℚ ↥L = 3 * Module.finrank ℚ ↥K) :
    ∃ α : ℝ, α ∈ K ∧
      L = K ⊔ IntermediateField.adjoin ℚ {α ^ ((1:ℝ)/3)}

-- elements of K(√α) are constructible if K-elements are
axiom sqrt_extension_constructible (K L : IntermediateField ℚ ℝ)
    (α : ℝ) (hαK : α ∈ K) (hL : L = K ⊔ IntermediateField.adjoin ℚ {Real.sqrt α})
    (hK : ∀ y ∈ K, isOrigamiConstructible y) :
    ∀ x ∈ L, isOrigamiConstructible x

-- elements of K(∛α) are constructible if K-elements are
axiom cbrt_extension_constructible (K L : IntermediateField ℚ ℝ)
    (α : ℝ) (hαK : α ∈ K) (hL : L = K ⊔ IntermediateField.adjoin ℚ {α ^ ((1:ℝ)/3)})
    (hK : ∀ y ∈ K, isOrigamiConstructible y) :
    ∀ x ∈ L, isOrigamiConstructible x

theorem Alperin_backward (x : ℝ)
    (K : IntermediateField ℚ ℝ)
    (hxK : x ∈ K)
    (hK : isTwoThree (Module.finrank ℚ ↥K)) :
    isOrigamiConstructible x := by
  choose n t ht using TwoThree_tower K hK
  obtain ⟨h0, hend, hsteps⟩ := ht
  suffices h : ∀ i : Fin (n+1), ∀ y ∈ t i, isOrigamiConstructible y from
    h ⟨n, Nat.lt_succ_self n⟩ x (by rw [hend]; exact hxK)
  intro i
  induction i using Fin.induction with
  | zero =>
    intro y hy
    simp at h0
    rw [h0] at hy
    obtain ⟨q, rfl⟩ := IntermediateField.mem_bot.mp hy
    exact ⟨IsOrigamiConstructible.rat q⟩
  | succ i ih =>
    intro y hy
    rcases (hsteps i).2 with h2 | h3
    · choose α hαK hL using degree2_is_sqrt (t i.castSucc) (t i.succ)
          (hsteps i).1 h2
      exact sqrt_extension_constructible _ _ α hαK hL ih y hy
    · choose α hαK hL using degree3_is_cbrt (t i.castSucc) (t i.succ)
          (hsteps i).1 h3
      exact cbrt_extension_constructible _ _ α hαK hL ih y hy

end LeanGeo

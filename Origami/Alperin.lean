import Origami.Alg
import Origami.Completeness
import Origami.Soundness

namespace Origami

-- the set of all Origami-constructible numbers is a field!
noncomputable def OCSubfield : Subfield ℝ where
  carrier := {x | AlgConstrNum x}
  add_mem' hx hy := AlgConstrNum.add hx hy
  mul_mem' hx hy := AlgConstrNum.mul hx hy
  neg_mem' hx := AlgConstrNum.neg hx
  inv_mem' _ hx := AlgConstrNum.inv hx
  one_mem' := AlgConstrNum.one
  zero_mem' := AlgConstrNum.zero

-- changing the type from Subfield ℝ to IntermediateField ℚ ℝ
-- just need to add a proof that it contains the image of ℚ
noncomputable def OCField : IntermediateField ℚ ℝ :=
  OCSubfield.toIntermediateField (by intro q; exact AlgConstrNum.rat q)

theorem mem_OCField {x : ℝ} : x ∈ OCField ↔ AlgConstrNum x := Iff.rfl

-- Reach K => K can be built by adjoining real roots of (at most) cubics to ℚ, one at a time.
inductive Reach : IntermediateField ℚ ℝ → Prop
  | bot : Reach ⊥
  | step {K : IntermediateField ℚ ℝ} {α a b c : ℝ} :
      Reach K → a ∈ K → b ∈ K → c ∈ K →
      α ^ 3 + a * α ^ 2 + b * α + c = 0 →
      Reach (K ⊔ IntermediateField.adjoin ℚ {α})

macro "in_field" : tactic =>
  `(tactic| repeat' (first
    | assumption
    | exact zero_mem _
    | exact one_mem _
    | apply sub_mem
    | apply div_mem
    | apply pow_mem
    | apply add_mem
    | apply mul_mem
    | apply neg_mem
    | apply inv_mem))

theorem mem_sup_left {K1 K2 : IntermediateField ℚ ℝ} {x : ℝ} (h : x ∈ K1) :
    x ∈ K1 ⊔ K2 := (le_sup_left : K1 ≤ K1 ⊔ K2) h

theorem mem_sup_right {K1 K2 : IntermediateField ℚ ℝ} {x : ℝ} (h : x ∈ K2) :
    x ∈ K1 ⊔ K2 := (le_sup_right : K2 ≤ K1 ⊔ K2) h

theorem mem_step (K : IntermediateField ℚ ℝ) (α : ℝ) :
    α ∈ K ⊔ IntermediateField.adjoin ℚ {α} :=
  mem_sup_right (IntermediateField.mem_adjoin_simple_self ℚ α)

theorem Reach.sup {K1 K2 : IntermediateField ℚ ℝ} (h1 : Reach K1) (h2 : Reach K2) :
    Reach (K1 ⊔ K2) := by
  induction h2 with
  | bot => rw [sup_bot_eq]; exact h1
  | @step K α a b c _ ha hb hc hr ih =>       -- @ allows us to name implicit arguments
    have : K1 ⊔ (K ⊔ IntermediateField.adjoin ℚ {α})
        = (K1 ⊔ K) ⊔ IntermediateField.adjoin ℚ {α} := (sup_assoc _ _ _).symm
    rw [this]
    exact Reach.step ih (mem_sup_right ha) (mem_sup_right hb) (mem_sup_right hc) hr

theorem fwd_one {x z : ℝ} (hx : ∃ K, Reach K ∧ x ∈ K)
    (hz : ∀ K : IntermediateField ℚ ℝ, x ∈ K → z ∈ K) : ∃ K, Reach K ∧ z ∈ K := by
  obtain ⟨K, hK, mx⟩ := hx
  exact ⟨K, hK, hz K mx⟩

theorem fwd_two {x y z : ℝ} (hx : ∃ K, Reach K ∧ x ∈ K) (hy : ∃ K, Reach K ∧ y ∈ K)
    (hz : ∀ K : IntermediateField ℚ ℝ, x ∈ K → y ∈ K → z ∈ K) :
    ∃ K, Reach K ∧ z ∈ K := by
  obtain ⟨K1, h1, m1⟩ := hx
  obtain ⟨K2, h2, m2⟩ := hy
  exact ⟨K1 ⊔ K2, h1.sup h2, hz _ (mem_sup_left m1) (mem_sup_right m2)⟩

-- using algebraic defn of OC, show that all OC numbers are in a "reachable" field.
theorem alperin_forward {x : ℝ} (h : AlgConstrNum x) : ∃ K, Reach K ∧ x ∈ K := by
  induction h with
  | rat q => exact ⟨⊥, Reach.bot, IntermediateField.mem_bot.2 ⟨q, by simp⟩⟩
  | add hx hy ihx ihy => exact fwd_two ihx ihy (by intros; in_field)
  | mul hx hy ihx ihy => exact fwd_two ihx ihy (by intros; in_field)
  | neg hx ihx => exact fwd_one ihx (by intros; in_field)
  | inv hx ihx => exact fwd_one ihx (by intros; in_field)
  | @sqrt x hx ihx =>
    obtain ⟨K, hK, mx⟩ := ihx
    exact ⟨K ⊔ IntermediateField.adjoin ℚ {Real.sqrt x},
      Reach.step hK (by in_field) (by in_field) (by in_field) (sqrt_root x),
      mem_step K _⟩
  | @cubic a b c r ha hb hc hr iha ihb ihc =>
    obtain ⟨Ka, hKa, ma⟩ := iha
    obtain ⟨Kb, hKb, mb⟩ := ihb
    obtain ⟨Kc, hKc, mc⟩ := ihc
    have hK : Reach (Ka ⊔ Kb ⊔ Kc) := (hKa.sup hKb).sup hKc
    have ma' : a ∈ Ka ⊔ Kb ⊔ Kc := mem_sup_left (mem_sup_left ma)
    have mb' : b ∈ Ka ⊔ Kb ⊔ Kc := mem_sup_left (mem_sup_right mb)
    have mc' : c ∈ Ka ⊔ Kb ⊔ Kc := mem_sup_right mc
    exact ⟨_, Reach.step hK ma' mb' mc' hr, mem_step _ _⟩

theorem reach_le_OC {K : IntermediateField ℚ ℝ} (h : Reach K) : K ≤ OCField := by
  induction h with
  | bot => exact bot_le
  | @step K α a b c _ ha hb hc hr ih =>
    have hα : AlgConstrNum α :=
      AlgConstrNum.cubic (mem_OCField.1 (ih ha)) (mem_OCField.1 (ih hb))
        (mem_OCField.1 (ih hc)) hr
    refine sup_le ih ?_
    rw [IntermediateField.adjoin_simple_le_iff]
    exact mem_OCField.2 hα

-- If x is in a "reachable" field, it is origami-constructible
theorem alperin_backward {x : ℝ} {K : IntermediateField ℚ ℝ} (h : Reach K) (hx : x ∈ K) :
    AlgConstrNum x := mem_OCField.1 (reach_le_OC h hx)

theorem alperin {x : ℝ} : AlgConstrNum x ↔ ∃ K, Reach K ∧ x ∈ K := by
  constructor
  · exact alperin_forward
  · intro hK
    obtain ⟨K, hRK, hxK⟩ := hK
    exact alperin_backward hRK hxK

def isTwoThree (n : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ n → p = 2 ∨ p = 3

lemma TwoThree_divisor {n m : ℕ} (h : n ∣ m) (hm : isTwoThree m) : isTwoThree n := by
  intro p hp hpn
  exact hm p hp (dvd_trans hpn h)

lemma TwoThree_prod {n m : ℕ} (hn : isTwoThree n) (hm : isTwoThree m) :
    isTwoThree (n * m) := by
  intro p hp hpnm
  rcases hp.dvd_mul.mp hpnm with h | h
  · exact hn p hp h
  · exact hm p hp h

lemma TwoThree_one : isTwoThree 1 := by
  intro _ hp hpd
  exact (hp.one_lt.ne' (Nat.dvd_one.1 hpd)).elim

lemma TwoThree_two : isTwoThree 2 := by
  intro _ hp hpd
  exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpd)

lemma TwoThree_three : isTwoThree 3 := by
  intro _ hp hpd
  exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpd)

theorem finrank_step (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K] {α a b c : ℝ}
    (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hr : α ^ 3 + a * α ^ 2 + b * α + c = 0) :
    FiniteDimensional ℚ ↥(K ⊔ IntermediateField.adjoin ℚ {α}) ∧
    ∃ d : ℕ, (d = 1 ∨ d = 2 ∨ d = 3) ∧
      Module.finrank ℚ ↥(K ⊔ IntermediateField.adjoin ℚ {α}) = Module.finrank ℚ ↥K * d := by
  set p : Polynomial K := Polynomial.X ^ 3 + Polynomial.C ⟨a, ha⟩ * Polynomial.X ^ 2
      + Polynomial.C ⟨b, hb⟩ * Polynomial.X + Polynomial.C ⟨c, hc⟩ with hp
  have hmonic : p.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.coeff, Polynomial.natDegree]
    monicity
    simp
    have h1 : max 3 2 = 3 := by simp
    have h2 : max 3 1 = 3 := by simp
    have h3 : max 3 0 = 3 := by simp
    rw [h1, h2, h3]
    simp
  have hroot : Polynomial.aeval α p = 0 := by simp [hp, hr]
  have hint : IsIntegral K α := ⟨p, hmonic, hroot⟩
  have hp3 : p.natDegree ≤ 3 := by rw [hp]; compute_degree
  have hdeg : (minpoly K α).natDegree ≤ 3 :=
    (Polynomial.natDegree_le_natDegree (minpoly.min K α hmonic hroot)).trans hp3
  set M := K ⊔ IntermediateField.adjoin ℚ {α} with hM
  have hKM : K ≤ M := le_sup_left
  have hαM : α ∈ M := (le_sup_right : IntermediateField.adjoin ℚ {α} ≤ M) (IntermediateField.mem_adjoin_simple_self ℚ α)
  have hL : M = (IntermediateField.adjoin K {α}).restrictScalars ℚ := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro x hx
        exact (IntermediateField.adjoin K {α}).algebraMap_mem ⟨x, hx⟩
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact IntermediateField.mem_adjoin_simple_self K α
    · have h2 : IntermediateField.adjoin K {α} ≤ K.extendScalars hKM := by
        rw [IntermediateField.adjoin_simple_le_iff]
        exact hαM
      intro x hx
      exact h2 hx
  rw [hL]
  have : FiniteDimensional K (IntermediateField.adjoin K {α}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hfr : Module.finrank K (IntermediateField.adjoin K {α}) = (minpoly K α).natDegree :=
    IntermediateField.adjoin.finrank hint
  have htower := Module.finrank_mul_finrank ℚ K (IntermediateField.adjoin K {α})
  have hpos : 0 < (minpoly K α).natDegree := minpoly.natDegree_pos hint
  refine ⟨?_, (minpoly K α).natDegree, by omega, ?_⟩
  · show FiniteDimensional ℚ (IntermediateField.adjoin K {α})
    exact Module.Finite.trans K (IntermediateField.adjoin K {α})
  · show Module.finrank ℚ (IntermediateField.adjoin K {α}) = _
    rw [← htower, hfr]

theorem reach_finrank {K : IntermediateField ℚ ℝ} (h : Reach K) :
    FiniteDimensional ℚ K ∧ isTwoThree (Module.finrank ℚ K) := by
  induction h with
  | bot =>
    refine ⟨by infer_instance, ?_⟩
    rw [IntermediateField.finrank_bot]
    exact TwoThree_one
  | @step K α a b c _ ha hb hc hr ih =>
    obtain ⟨_, hdeg⟩ := ih
    obtain ⟨hfin, _, hd, hfr⟩ := finrank_step K ha hb hc hr
    refine ⟨hfin, ?_⟩
    rw [hfr]
    refine TwoThree_prod hdeg ?_
    rcases hd with h | h | h <;>
    {rw [h]; first | exact TwoThree_one | exact TwoThree_two | exact TwoThree_three}

theorem origami_degree {x : ℝ} (h : AlgConstrNum x) :
    isTwoThree (Module.finrank ℚ ↥(IntermediateField.adjoin ℚ {x})) := by
  obtain ⟨K, hK, hx⟩ := alperin_forward h
  obtain ⟨hfin, hdeg⟩ := reach_finrank hK
  have hle : IntermediateField.adjoin ℚ {x} ≤ K := by
    rwa [IntermediateField.adjoin_simple_le_iff]
  exact TwoThree_divisor (IntermediateField.finrank_dvd_of_le_right hle) hdeg

end Origami

import Origami.Tactics
import Origami.Lemmas
import Origami.Alg

open ComplexConjugate

namespace Origami
open Line

theorem normal_of_mem (l : Line) (a b c : ℝ)
    (h : ∀ z : ℂ, z ∈ l ↔ a * z.re + b * z.im + c = 0) :
    a * l.d.re + b * l.d.im = 0 := by
  have h1 := (h l.p).1 (mem_self l)
  have h2 := (h (l.p + l.d)).1 (by rw [Line.mem_def]; to_re_im; ring)
  simp [Complex.add_re, Complex.add_im] at h2
  linarith

theorem det_ne {l m : Line} {a1 b1 c1 a2 b2 c2 : ℝ}
    (hab1 : a1 ≠ 0 ∨ b1 ≠ 0) (hab2 : a2 ≠ 0 ∨ b2 ≠ 0)
    (h1 : ∀ z : ℂ, z ∈ l ↔ a1 * z.re + b1 * z.im + c1 = 0)
    (h2 : ∀ z : ℂ, z ∈ m ↔ a2 * z.re + b2 * z.im + c2 = 0)
    (hn : ¬ l.Par m) : a1 * b2 - a2 * b1 ≠ 0 := by
  intro D
  have n1 := normal_of_mem l a1 b1 c1 h1
  have n2 := normal_of_mem m a2 b2 c2 h2
  apply hn
  have G : l.d.im * m.d.re - l.d.re * m.d.im = 0 := by cancel_comp hab1
  unfold Line.Par
  to_re_im
  linarith

theorem comp_ne (p q : ℂ) (hne : p ≠ q) :
    q.re - p.re ≠ 0 ∨ q.im - p.im ≠ 0 := by
  by_contra h
  rw [not_or, not_not, not_not] at h
  exact hne (Complex.ext (by linarith [h.1]) (by linarith [h.2]))

theorem mem_iff_of_dir (f : Line) (p : ℂ) (U V : ℝ) (hp : p ∈ f)
    (hUV : U ≠ 0 ∨ V ≠ 0) (hdir : V * f.d.re - U * f.d.im = 0) (z : ℂ) :
    z ∈ f ↔ U * (z.im - p.im) - V * (z.re - p.re) = 0 := by
  line_facts
  rw [mem_def] at hp ⊢
  to_re_im at hp ⊢
  constructor
  · intro hz
    cancel_comp f_ri
  · intro hT
    have hS : (z.im - p.im) * f.d.re - (z.re - p.re) * f.d.im = 0 := by
      cancel_comp hUV
    linear_combination hS + hp

theorem mem_congr {f g : Line} (h : f.Same g) (z : ℂ) : z ∈ f ↔ z ∈ g := by
  obtain ⟨hp, hm⟩ := h
  have hUV := d_re_or_im g
  unfold Line.Par at hp
  to_re_im at hp
  rw [mem_iff_of_dir f f.p g.d.re g.d.im (mem_self f) hUV (by linarith) z,
      mem_iff_of_dir g f.p g.d.re g.d.im hm hUV (by ring) z]

theorem dir_of_two (f : Line) (p q : ℂ) (hp : p ∈ f) (hq : q ∈ f) :
    (q.im - p.im) * f.d.re - (q.re - p.re) * f.d.im = 0 := by
  rw [mem_def] at hp hq
  to_re_im at hp hq
  linear_combination hq - hp

theorem reflect_formula {f : Line} {a b c : ℝ} (hab : a ≠ 0 ∨ b ≠ 0)
    (h : ∀ z : ℂ, z ∈ f ↔ a * z.re + b * z.im + c = 0) (p : ℂ) :
    (f.reflect p).re = p.re - 2 * (a * p.re + b * p.im + c) / (a ^ 2 + b ^ 2) * a ∧
    (f.reflect p).im = p.im - 2 * (a * p.re + b * p.im + c) / (a ^ 2 + b ^ 2) * b := by
  line_facts
  have hn := normal_of_mem f a b c h
  have hpc := (h f.p).1 (mem_self f)
  have hN : a ^ 2 + b ^ 2 ≠ 0 := by cases hab <;> positivity
  obtain ⟨t, hdr, hdi⟩ : ∃ t : ℝ, f.d.re = -b * t ∧ f.d.im = a * t := by
    use (a * f.d.im - b * f.d.re) / (a ^ 2 + b ^ 2)
    refine ⟨?_, ?_⟩
    · field_simp
      linear_combination a * hn
    · field_simp
      linear_combination b * hn
  have hc : c = -(a * f.p.re) - b * f.p.im := by linarith
  rw [hc]
  constructor <;>
  · unfold Line.reflect
    to_re_im
    grind

theorem reflect_dist_sq (f : Line) (z w : ℂ) :
    ((f.reflect z).re - (f.reflect w).re) ^ 2 + ((f.reflect z).im - (f.reflect w).im) ^ 2
      = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  have e : f.reflect z - f.reflect w = (f.d / conj f.d) * conj (z - w) := by
    unfold Line.reflect; simp [map_sub]; ring
  have hne : Complex.normSq f.d ≠ 0 := by
    have := Complex.normSq_pos.2 f.hd
    positivity
  have h1 : Complex.normSq (f.reflect z - f.reflect w) = Complex.normSq (z - w) := by
    rw [e, map_mul, map_div₀, Complex.normSq_conj, Complex.normSq_conj, div_self hne, one_mul]
  simp [Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at h1
  linarith

theorem o2_eq {f : Line} {p q : ℂ}
  (hne : p ≠ q) (hO : f.reflect p = q) :
    ∀ z : ℂ, z ∈ f ↔ (q.re - p.re) * z.re + (q.im - p.im) * z.im
      -((q.re ^ 2 + q.im ^ 2 - p.re ^ 2 - p.im ^ 2) / 2) = 0 := by
  have hUV := comp_ne p q hne
  line_facts
  have hqe : (q - f.p) * conj f.d = f.d * conj (p - f.p) := by
    rw [<- hO]
    unfold Line.reflect
    field_simp; ring_nf
  to_re_im at hqe
  obtain ⟨hr, hi⟩ := hqe
  obtain ⟨m0, hm0r, hm0i⟩ : ∃ m0 : ℂ, m0.re = (p.re + q.re) / 2 ∧ m0.im = (p.im + q.im) / 2 :=
    ⟨⟨_, _⟩, rfl, rfl⟩
  have hdir : -(q.re - p.re) * f.d.re - (q.im - p.im) * f.d.im = 0 := by cancel_dir f
  have hmid : m0 ∈ f := by
    rw [mem_def]
    to_re_im
    simp [hm0r, hm0i]
    linarith

  intro z
  rw [mem_iff_of_dir f m0 (q.im - p.im) (-(q.re - p.re)) hmid
    (hUV.symm.imp_right neg_ne_zero.mpr) hdir z]
  simp [hm0r, hm0i]
  constructor <;> intros <;> linarith

noncomputable def O6poly (a2 b2 e2 px py qx qy P Q : ℝ) : ℝ :=
  (a2 * qx + b2 * qy + e2) * ((P - px) ^ 2 + (Q - py) ^ 2)
  - 2 * ((P - px) * qx + (Q - py) * qy - (P ^ 2 + Q ^ 2 - px ^ 2 - py ^ 2) / 2)
    * (a2 * (P - px) + b2 * (Q - py))

theorem o6_E {a2 b2 e2 px py qx qy P Q R S : ℝ}
    (hNf : (P - px) ^ 2 + (Q - py) ^ 2 ≠ 0)
    (hR : R = qx - 2 * ((P - px) * qx + (Q - py) * qy
      + -((P ^ 2 + Q ^ 2 - px ^ 2 - py ^ 2) / 2)) / ((P - px) ^ 2 + (Q - py) ^ 2) * (P - px))
    (hS : S = qy - 2 * ((P - px) * qx + (Q - py) * qy
      + -((P ^ 2 + Q ^ 2 - px ^ 2 - py ^ 2) / 2)) / ((P - px) ^ 2 + (Q - py) ^ 2) * (Q - py))
    (h : a2 * R + b2 * S + e2 = 0) : O6poly a2 b2 e2 px py qx qy P Q = 0 := by
  have hR' : R * ((P - px) ^ 2 + (Q - py) ^ 2)
      = qx * ((P - px) ^ 2 + (Q - py) ^ 2)
        - 2 * ((P - px) * qx + (Q - py) * qy
          + -((P ^ 2 + Q ^ 2 - px ^ 2 - py ^ 2) / 2)) * (P - px) := by
    rw [hR]
    field_simp
  have hS' : S * ((P - px) ^ 2 + (Q - py) ^ 2)
      = qy * ((P - px) ^ 2 + (Q - py) ^ 2)
        - 2 * ((P - px) * qx + (Q - py) * qy
          + -((P ^ 2 + Q ^ 2 - px ^ 2 - py ^ 2) / 2)) * (Q - py) := by
    rw [hS]
    field_simp
  have key : ((P - px) ^ 2 + (Q - py) ^ 2) * (a2 * R + b2 * S + e2)
      = O6poly a2 b2 e2 px py qx qy P Q := by
    unfold O6poly
    linear_combination a2 * hR' + b2 * hS'
  rw [← key, h, mul_zero]

theorem o6_core {a1 b1 e1 a2 b2 e2 px py qx qy P Q : ℝ}
    (ha1 : AlgConstrNum a1) (hb1 : AlgConstrNum b1) (he1 : AlgConstrNum e1)
    (ha2 : AlgConstrNum a2) (hb2 : AlgConstrNum b2) (he2 : AlgConstrNum e2)
    (hpx : AlgConstrNum px) (hpy : AlgConstrNum py) (hqx : AlgConstrNum qx) (hqy : AlgConstrNum qy)
    (hab1 : a1 ≠ 0 ∨ b1 ≠ 0) (hD : a1 * b2 - a2 * b1 ≠ 0)
    (hP : a1 * P + b1 * Q + e1 = 0)
    (hE : O6poly a2 b2 e2 px py qx qy P Q = 0) : AlgConstrNum P ∧ AlgConstrNum Q := by
  have hN : a1 ^ 2 + b1 ^ 2 ≠ 0 := by
    cases hab1 <;> positivity
  have hw : (a1 ^ 2 + b1 ^ 2)⁻¹ ≠ 0 := inv_ne_zero hN
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, ∀ s, G s = O6poly a2 b2 e2 px py qx qy
      ((-a1 * e1 - b1 * s) / (a1 ^ 2 + b1 ^ 2)) ((-b1 * e1 + a1 * s) / (a1 ^ 2 + b1 ^ 2)) := by
      set G := fun s => O6poly a2 b2 e2 px py qx qy ((-a1 * e1 - b1 * s) / (a1 ^ 2 + b1 ^ 2)) ((-b1 * e1 + a1 * s) / (a1 ^ 2 + b1 ^ 2)) with hG
      use G
      intro s
      rfl
  have hPs : (-a1 * e1 - b1 * (-b1 * P + a1 * Q)) / (a1 ^ 2 + b1 ^ 2) = P := by
    rw [div_eq_iff hN]; linear_combination (-a1) * hP
  have hQs : (-b1 * e1 + a1 * (-b1 * P + a1 * Q)) / (a1 ^ 2 + b1 ^ 2) = Q := by
    rw [div_eq_iff hN]; linear_combination (-b1) * hP
  have hs : G (-b1 * P + a1 * Q) = 0 := by rw [hG, hPs, hQs]; exact hE
  have hsI : AlgConstrNum (-b1 * P + a1 * Q) := by
    refine AlgConstrNum.of_cubic_fn (G := G)
      (c3 := (a1 * b2 - a2 * b1) * (a1 ^ 2 + b1 ^ 2) * ((a1 ^ 2 + b1 ^ 2)⁻¹) ^ 3)
      (mul_ne_zero (mul_ne_zero hD hN) (pow_ne_zero 3 hw)) (by is_oc) ?_ ?_ ?_ ?_ hs
    · intro x
      rw [hG x, hG 1, hG (-1), hG 0]
      unfold O6poly
      ring
    · rw [hG]; unfold O6poly; is_oc
    · rw [hG]; unfold O6poly; is_oc
    · rw [hG]; unfold O6poly; is_oc
  exact ⟨by rw [← hPs]; is_oc, by rw [← hQs]; is_oc⟩

end Origami

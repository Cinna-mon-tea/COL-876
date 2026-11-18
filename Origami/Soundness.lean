import Origami.Analytic
import Origami.Alg

namespace Origami
open Line

theorem inter_aux {l m : Line} {z : ℂ} (hl : AlgConstrLine l) (hm : AlgConstrLine m)
    (hn : ¬ l.Par m) (hzl : z ∈ l) (hzm : z ∈ m) :
    AlgConstrNum z.re ∧ AlgConstrNum z.im := by
  obtain ⟨a1, b1, c1, ha1, hb1, hc1, hab1, h1⟩ := hl
  obtain ⟨a2, b2, c2, ha2, hb2, hc2, hab2, h2⟩ := hm
  have e1 := (h1 z).1 hzl
  have e2 := (h2 z).1 hzm
  have hD := det_ne hab1 hab2 h1 h2 hn
  constructor
  · have : z.re = (b1 * c2 - b2 * c1) / (a1 * b2 - a2 * b1) := by
      rw [eq_div_iff hD]
      linear_combination b2 * e1 - b1 * e2
    rw [this]
    is_oc
  · have : z.im = (a2 * c1 - a1 * c2) / (a1 * b2 - a2 * b1) := by
      rw [eq_div_iff hD]
      linear_combination a1 * e2 - a2 * e1
    rw [this]
    is_oc

theorem o1_aux {f : Line} {p q : ℂ} (hp : AlgConstrNum p.re ∧ AlgConstrNum p.im)
    (hq : AlgConstrNum q.re ∧ AlgConstrNum q.im) (hne : p ≠ q) (hO : O1 p q f) :AlgConstrLine f := by
  obtain ⟨hpx, hpy⟩ := hp
  obtain ⟨hqx, hqy⟩ := hq
  obtain ⟨h1, h2⟩ := hO
  have hUV := comp_ne p q hne
  use -(q.im - p.im), q.re - p.re, (q.im - p.im) * p.re - (q.re - p.re) * p.im
  refine ⟨by is_oc, by is_oc, by is_oc, by grind, ?_⟩
  intro z
  rw [mem_iff_of_dir f p _ _ h1 hUV (dir_of_two f p q h1 h2) z]
  grind

theorem o2_aux {f : Line} {p q : ℂ} (hp : AlgConstrNum p.re ∧ AlgConstrNum p.im)
    (hq : AlgConstrNum q.re ∧ AlgConstrNum q.im) (hne : p ≠ q) (hO : O2 p q f) : AlgConstrLine f := by
  obtain ⟨hpx, hpy⟩ := hp
  obtain ⟨hqx, hqy⟩ := hq
  unfold O2 at hO
  use q.re - p.re, q.im - p.im, -((q.re ^ 2 + q.im ^ 2 - p.re ^ 2 - p.im ^ 2) / 2)
  exact ⟨by is_oc, by is_oc, by is_oc, comp_ne p q hne, o2_eq hne hO⟩

theorem o3_eq {f l m : Line} {a1 b1 c1 a2 b2 c2 : ℝ}
    (hab1 : a1 ≠ 0 ∨ b1 ≠ 0) (hab2 : a2 ≠ 0 ∨ b2 ≠ 0)
    (h1 : ∀ z : ℂ, z ∈ l ↔ a1 * z.re + b1 * z.im + c1 = 0)
    (h2 : ∀ z : ℂ, z ∈ m ↔ a2 * z.re + b2 * z.im + c2 = 0)
    (hn : ¬ l.Same m) (hO : O3 l m f) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ z : ℂ, z ∈ f ↔
      Real.sqrt (a2 ^ 2 + b2 ^ 2) * (a1 * z.re + b1 * z.im + c1) =
      s * Real.sqrt (a1 ^ 2 + b1 ^ 2) * (a2 * z.re + b2 * z.im + c2) := by
  let p := f.p + f.d
  set s1 := (a1 * f.p.re + b1 * f.p.im + c1) * (a2 * f.p.re + b2 * f.p.im + c2) with hs1
  set s2 := (a1 * p.re + b1 * p.im + c1) * (a2 * p.re + b2 * p.im + c2) with hs2
  set s3 := cond (s1 + s2 > 0) (1) (-1) with hs3
  refine ⟨s3, ?_, ?_⟩
  by_cases h : (s1 + s2 > 0) <;> simp [h, s3]
  intro z
  constructor
  · rw [hs3]
    intro hz
    by_cases h : (s1 + s2 > 0)
    · simp [h]
      simp [hs1, hs2] at h
      simp [mem_def] at hz
      sorry
    · simp [h]
      simp [hs1, hs2] at h
      simp [mem_def] at hz
      sorry
  · rw [hs3]
    sorry

theorem o3_aux {f l m : Line} (hl : AlgConstrLine l) (hm : AlgConstrLine m)
    (hn : ¬ l.Same m) (hO : O3 l m f) : AlgConstrLine f := by
  obtain ⟨a1, b1, c1, ha1, hb1, hc1, hab1, h1⟩ := hl
  obtain ⟨a2, b2, c2, ha2, hb2, hc2, hab2, h2⟩ := hm
  obtain ⟨s, hs, hf⟩ := o3_eq hab1 hab2 h1 h2 hn hO
  have hsI : AlgConstrNum s := by
    rcases hs with h1 | h1 <;> {rw [h1]; is_oc}
  obtain ⟨A, B, C, hAI, hBI, hCI, hf'⟩ : ∃ A B C : ℝ, AlgConstrNum A ∧ AlgConstrNum B ∧ AlgConstrNum C ∧
      ∀ z : ℂ, z ∈ f ↔ A * z.re + B * z.im + C = 0 :=
    ⟨Real.sqrt (a2 ^ 2 + b2 ^ 2) * a1 - s * Real.sqrt (a1 ^ 2 + b1 ^ 2) * a2,
     Real.sqrt (a2 ^ 2 + b2 ^ 2) * b1 - s * Real.sqrt (a1 ^ 2 + b1 ^ 2) * b2,
     Real.sqrt (a2 ^ 2 + b2 ^ 2) * c1 - s * Real.sqrt (a1 ^ 2 + b1 ^ 2) * c2,
      by is_oc, by is_oc, by is_oc,
      by intro z; rw [hf z]; constructor <;> intros <;> linarith⟩
  refine ⟨A, B, C, hAI, hBI, hCI, ?_, hf'⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  simp [hA, hB] at hf'
  have hC : C = 0 := (hf' f.p).1 (mem_self f)
  obtain ⟨z, hzr, hzi⟩ : ∃ z : ℂ, z.re = f.p.re - f.d.im ∧ z.im = f.p.im + f.d.re :=
    ⟨⟨_, _⟩, rfl, rfl⟩
  have hz : z ∈ f := (hf' z).2 (by rw [hC])
  rw [mem_def] at hz
  to_re_im at hz
  simp [hzr, hzi] at hz
  have hpos := Complex.normSq_pos.2 f.hd
  rw [Complex.normSq_apply] at hpos
  linarith

theorem o4_aux {f l : Line} {p : ℂ} (hp : AlgConstrNum p.re ∧ AlgConstrNum p.im)
    (hl : AlgConstrLine l) (hO : O4 p l f) : AlgConstrLine f := by
  obtain ⟨hpx, hpy⟩ := hp
  obtain ⟨a, b, c, ha, hb, hc, hab, hz⟩ := hl
  obtain ⟨hperp, hpf⟩ := hO
  have hN := normal_of_mem l a b c hz
  have hF : f.d.re * l.d.re + f.d.im * l.d.im = 0 := by
    unfold Line.Perp at hperp
    to_re_im at hperp
    linarith
  have hdir : b * f.d.re - a * f.d.im = 0 := by cancel_dir l
  use -b, a, (b * p.re - a * p.im)
  refine ⟨by is_oc, by is_oc, by is_oc, by grind, ?_⟩
  intro z
  rw [mem_iff_of_dir f p a b hpf hab hdir z]
  grind

theorem circle_line_oc {a b e qx qy P Q R2 : ℝ} (hab : a ≠ 0 ∨ b ≠ 0)
    (ha : AlgConstrNum a) (hb : AlgConstrNum b) (he : AlgConstrNum e) (hqx : AlgConstrNum qx) (hqy : AlgConstrNum qy)
    (hR : AlgConstrNum R2) (h1 : a * P + b * Q + e = 0)
    (h2 : (P - qx) ^ 2 + (Q - qy) ^ 2 = R2) : AlgConstrNum P ∧ AlgConstrNum Q := by
  have hN : a ^ 2 + b ^ 2 ≠ 0 := by cases hab <;> positivity
  have hs : a * (P - qx) + b * (Q - qy) = -(a * qx + b * qy + e) := by linear_combination h1
  have hsI : AlgConstrNum (a * (P - qx) + b * (Q - qy)) := by rw [hs]; is_oc
  have ht : AlgConstrNum (-b * (P - qx) + a * (Q - qy)) := by
    refine AlgConstrNum.of_quad (a := 0) (b := -((a ^ 2 + b ^ 2) * R2 - (a * qx + b * qy + e) ^ 2))
      AlgConstrNum.zero (by is_oc) ?_
    linear_combination (a ^ 2 + b ^ 2) * h2
      - (a * (P - qx) + b * (Q - qy) - (a * qx + b * qy + e)) * hs
  have eP : P = qx + (a * (a * (P - qx) + b * (Q - qy))
      - b * (-b * (P - qx) + a * (Q - qy))) / (a ^ 2 + b ^ 2) := by
    rw [← sub_eq_iff_eq_add', eq_div_iff hN]; ring
  have eQ : Q = qy + (b * (a * (P - qx) + b * (Q - qy))
      + a * (-b * (P - qx) + a * (Q - qy))) / (a ^ 2 + b ^ 2) := by
    rw [← sub_eq_iff_eq_add', eq_div_iff hN]; ring
  exact ⟨by rw [eP]; is_oc, by rw [eQ]; is_oc⟩

theorem o5_aux {f l : Line} {p q : ℂ} (hp : AlgConstrNum p.re ∧ AlgConstrNum p.im)
    (hq : AlgConstrNum q.re ∧ AlgConstrNum q.im) (hl : AlgConstrLine l) (hne : p ≠ q)
    (hO : O5 p q l f) : AlgConstrLine f := by
  obtain ⟨hpl, hqf⟩ := hO
  by_cases hfix : f.reflect p = p
  · exact o1_aux hp hq hne ⟨(reflect_eq_self_iff f p).1 hfix, hqf⟩
  · obtain ⟨hpx, hpy⟩ := hp
    obtain ⟨hqx, hqy⟩ := hq
    obtain ⟨a, b, e, ha, hb, he, hab, hl'⟩ := hl
    have hd := reflect_dist_sq f p q
    rw [(reflect_eq_self_iff f q).2 hqf] at hd
    obtain ⟨hP, hQ⟩ := circle_line_oc hab ha hb he hqx hqy (by is_oc) ((hl' _).1 hpl) hd
    exact o2_aux ⟨hpx, hpy⟩ ⟨hP, hQ⟩ (fun h => hfix h.symm) rfl

theorem o6_aux {f l m : Line} {p q : ℂ} (hp : AlgConstrNum p.re ∧ AlgConstrNum p.im)
    (hq : AlgConstrNum q.re ∧ AlgConstrNum q.im) (hl : AlgConstrLine l) (hm : AlgConstrLine m)
    (hpl : p ∉ l) (hn : ¬ l.Par m) (hO : O6 p q l m f) : AlgConstrLine f := by
  obtain ⟨a1, b1, c1, ha1, hb1, hc1, hab1, hm⟩ := hm
  obtain ⟨a2, b2, c2, ha2, hb2, hc2, hab2, hl⟩ := hl
  obtain ⟨hpl2, hqm2⟩ := hO
  obtain ⟨hpx, hpy⟩ := hp
  obtain ⟨hqx, hqy⟩ := hq
  have hD := det_ne hab2 hab1 hl hm hn
  have hne : p ≠ f.reflect p := fun h => hpl (by rwa [← h] at hpl2)
  have hAB := comp_ne p (f.reflect p) hne
  have hNf : ((f.reflect p).re - p.re) ^ 2 + ((f.reflect p).im - p.im) ^ 2 ≠ 0 := by
    cases hAB <;> positivity
  have hline : ∀ z : ℂ, z ∈ f ↔
      ((f.reflect p).re - p.re) * z.re + ((f.reflect p).im - p.im) * z.im
        + -(((f.reflect p).re ^ 2 + (f.reflect p).im ^ 2 - p.re ^ 2 - p.im ^ 2) / 2) = 0 := by
    intro z
    rw [o2_eq hne rfl z]
    constructor <;> intro h <;> linarith
  obtain ⟨er, ei⟩ := reflect_formula hAB hline q
  have hE := o6_E hNf er ei ((hm _).1 hqm2)
  obtain ⟨hPI, hQI⟩ := o6_core ha2 hb2 hc2 ha1 hb1 hc1 hpx hpy hqx hqy hab2 hD
    ((hl _).1 hpl2) hE
  refine ⟨(f.reflect p).re - p.re, (f.reflect p).im - p.im,
    -(((f.reflect p).re ^ 2 + (f.reflect p).im ^ 2 - p.re ^ 2 - p.im ^ 2) / 2),
    ?_, ?_, ?_, ?_, ?_⟩
  · is_oc
  · is_oc
  · is_oc
  · exact hAB
  · exact hline

theorem o7_aux {f l m : Line} {p : ℂ} (hp : AlgConstrNum p.re ∧ AlgConstrNum p.im)
    (hl : AlgConstrLine l) (hm : AlgConstrLine m) (hn : ¬ l.Par m)
    (hO : O7 p l m f) : AlgConstrLine f := by
  obtain ⟨hpx, hpy⟩ := hp
  obtain ⟨a, b, c, ha, hb, hc, hab, hl'⟩ := hl
  obtain ⟨A, B, C, hA, hB, hC, hAB, hm'⟩ := hm
  obtain ⟨hperp, hrefl⟩ := hO
  have hD := det_ne hab hAB hl' hm' hn
  have hNm := normal_of_mem m A B C hm'
  have hF : f.d.re * m.d.re + f.d.im * m.d.im = 0 := by
    unfold Line.Perp at hperp; to_re_im at hperp; linarith
  have hdir : B * f.d.re - A * f.d.im = 0 := by cancel_dir m
  have hf : ∀ z : ℂ, z ∈ f ↔ -B * z.re + A * z.im + (B * f.p.re - A * f.p.im) = 0 := by
    intro z
    rw [mem_iff_of_dir f f.p A B (mem_self f) hAB hdir z]
    constructor <;> intros <;> linarith
  have hN : (-B) ^ 2 + A ^ 2 ≠ 0 := by
    rw [neg_sq]; cases hAB <;> positivity
  have hrefl' := (hl' _).1 hrefl
  obtain ⟨e1, e2⟩ := reflect_formula (hAB.symm.imp_left neg_ne_zero.mpr) hf p
  rw [e1, e2] at hrefl'
  obtain ⟨q, hq1, hq2⟩ : ∃ q : ℝ,
      q * ((-B) ^ 2 + A ^ 2) = 2 * (-B * p.re + A * p.im + (B * f.p.re - A * f.p.im)) ∧
      q = -(a * p.re + b * p.im + c) / (a * B - A * b) :=
    ⟨2 * (-B * p.re + A * p.im + (B * f.p.re - A * f.p.im)) / ((-B) ^ 2 + A ^ 2),
      by grind, by rw [eq_div_iff hD]; linear_combination hrefl'⟩
  rw [hq2] at hq1
  have hK : B * f.p.re - A * f.p.im = B * p.re - A * p.im
    - (a * p.re + b * p.im + c) * (A ^ 2 + B ^ 2) / (a * B - A * b) / 2 := by
    linear_combination (-1 / 2 : ℝ) * hq1
  use -B, A, B * p.re - A * p.im - (a * p.re + b * p.im + c) * (A ^ 2 + B ^ 2) / (a * B - A * b) / 2
  refine ⟨by is_oc, hA, by is_oc, hAB.symm.imp_left neg_ne_zero.mpr, ?_⟩
  intro z
  rw [hf z, hK]

theorem reflect_aux {p : ℂ} {f : Line} (hp : AlgConstrNum p.re ∧ AlgConstrNum p.im)
    (hf : AlgConstrLine f) : AlgConstrNum (f.reflect p).re ∧ AlgConstrNum (f.reflect p).im := by
  obtain ⟨a, b, c, ha, hb, hc, hab, h⟩ := hf
  obtain ⟨e1, e2⟩ := reflect_formula hab h p
  rw [e1, e2]
  is_oc

end Origami

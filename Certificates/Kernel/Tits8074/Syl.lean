module

public import Certificates.Kernel.Tits8074.Glue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelT8074

open CFSG.KC.Tits8074 CFSG.Quasithin CFSG.Certificates CFSG.Monster.B.Co2 Equiv

theorem zfix : fixes L [0, 3] zc = true := by quickRfl

theorem zmove : bIf(Nat.beq (ap L zc 24) 24, false, true) = true := by quickRfl

theorem codes_lt : ∀ c ∈ codes, c < 24 := by decide

theorem fin_ext_ap {c : Nat} (hc : c < 24) {q r : Fin 1755} (h : ap L c q = r) : gl c q = r :=
  Fin.ext (by rw [← ap_fin hc]; exact h)

@[expose] def Sg : Subgroup (Perm (Fin 1755)) where
  carrier := {g | g ∈ P ∧ g 0 = 0 ∧ ((g 3 = 3 ∧ g 4 = 4) ∨ (g 3 = 4 ∧ g 4 = 3))}
  mul_mem' := by
    rintro x y ⟨hx, x0, hx'⟩ ⟨hy, y0, hy'⟩
    refine ⟨P.mul_mem hx hy, by rw [Perm.mul_apply, y0, x0], ?_⟩
    rcases hx' with ⟨x3, x4⟩ | ⟨x3, x4⟩ <;> rcases hy' with ⟨y3, y4⟩ | ⟨y3, y4⟩ <;>
      simp [Perm.mul_apply, x3, x4, y3, y4]
  one_mem' := ⟨P.one_mem, rfl, Or.inl ⟨rfl, rfl⟩⟩
  inv_mem' := by
    rintro x ⟨hx, x0, hx'⟩
    refine ⟨P.inv_mem hx, Perm.inv_eq_iff_eq.2 x0.symm, ?_⟩
    rcases hx' with ⟨x3, x4⟩ | ⟨x3, x4⟩
    · exact Or.inl ⟨Perm.inv_eq_iff_eq.2 x3.symm, Perm.inv_eq_iff_eq.2 x4.symm⟩
    · exact Or.inr ⟨Perm.inv_eq_iff_eq.2 x4.symm, Perm.inv_eq_iff_eq.2 x3.symm⟩

theorem sc_lt : sc < 24 := ws_facts.2.2.2.2.2.2.2.2.2.2

theorem zc_lt : zc < 24 := ws_facts.2.2.2.2.2.2.2.2.2.1

theorem s_facts : gl sc 0 = 0 ∧ gl sc 3 = 4 ∧ gl sc 4 = 3 := by
  obtain ⟨-, h0, h3, h4⟩ := pairK_spec pair
  exact ⟨fin_ext_ap sc_lt h0, fin_ext_ap sc_lt h3, fin_ext_ap sc_lt h4⟩

theorem s_mem : gl sc ∈ Sg :=
  ⟨gl_mem sc_lt, s_facts.1, Or.inr ⟨s_facts.2.1, s_facts.2.2⟩⟩

theorem mem_take2 : ((0 : Fin 1755) : ℕ) ∈ bs.take 2 ∧ ((3 : Fin 1755) : ℕ) ∈ bs.take 2 := by
  decide

theorem level2_fix4 {g : Perm (Fin 1755)} (hg : g ∈ titsPairQ.levelSubgroup 2) : g 4 = 4 := by
  have hle : titsPairQ.levelSubgroup 2 ≤ MulAction.stabilizer (Perm (Fin 1755)) (4 : Fin 1755) := by
    refine (Subgroup.closure_le _).2 fun s hs => ?_
    obtain ⟨c, hc, rfl, hfix⟩ := level_gen hs
    have hpre : ∀ p ∈ bs.take 2, p < 1755 := fun p hp => bs_lt p (List.mem_of_mem_take hp)
    have h4 := (pairK_spec pair).1 c (codes_of c hc) (fix_nat hc hpre hfix)
    exact fin_ext_ap hc h4
  exact hle hg

theorem level2_le : titsPairQ.levelSubgroup 2 ≤ Sg := by
  intro g hg
  obtain ⟨hP, hfix⟩ := (level_mem_iff (by norm_num) g).1 hg
  exact ⟨hP, hfix 0 mem_take2.1, Or.inl ⟨hfix 3 mem_take2.2, level2_fix4 hg⟩⟩

theorem level2_of {g : Perm (Fin 1755)} (hP : g ∈ P) (h0 : g 0 = 0) (h3 : g 3 = 3) :
    g ∈ titsPairQ.levelSubgroup 2 := by
  refine (level_mem_iff (by norm_num) g).2 ⟨hP, fun q hq => ?_⟩
  have hq' : (q : ℕ) = 0 ∨ (q : ℕ) = 3 := by
    have e : bs.take 2 = [0, 3] := rfl
    rw [e] at hq
    simpa using hq
  rcases hq' with hq' | hq'
  · rw [show q = 0 from Fin.ext hq', h0]
  · rw [show q = 3 from Fin.ext hq', h3]

theorem Sg_cases {g : Perm (Fin 1755)} (hg : g ∈ Sg) :
    g ∈ titsPairQ.levelSubgroup 2 ∨ (gl sc)⁻¹ * g ∈ titsPairQ.levelSubgroup 2 := by
  obtain ⟨hP, h0, ⟨h3, -⟩ | ⟨h3, -⟩⟩ := hg
  · exact Or.inl (level2_of hP h0 h3)
  · refine Or.inr (level2_of (P.mul_mem (P.inv_mem (gl_mem sc_lt)) hP) ?_ ?_)
    · rw [Perm.mul_apply, h0, Perm.inv_eq_iff_eq, s_facts.1]
    · rw [Perm.mul_apply, h3, Perm.inv_eq_iff_eq, s_facts.2.1]

theorem card_Sg : Nat.card Sg = 2048 := by
  let L2 : Set (Perm (Fin 1755)) := titsPairQ.levelSubgroup 2
  have hset : (Sg : Set (Perm (Fin 1755))) = L2 ∪ (fun h => gl sc * h) '' L2 := by
    ext g
    constructor
    · intro hg
      rcases Sg_cases hg with h | h
      · exact Or.inl h
      · exact Or.inr ⟨_, h, by group⟩
    · rintro (h | ⟨h, hh, rfl⟩)
      · exact level2_le h
      · exact Sg.mul_mem s_mem (level2_le hh)
  have hdis : Disjoint L2 ((fun h => gl sc * h) '' L2) := by
    rw [Set.disjoint_left]
    rintro g hg ⟨h, hh, rfl⟩
    have e1 := ((level_mem_iff (by norm_num) _).1 hg).2 3 mem_take2.2
    have e2 := ((level_mem_iff (by norm_num) _).1 hh).2 3 mem_take2.2
    rw [Perm.mul_apply, e2, s_facts.2.1] at e1
    exact absurd e1 (by decide)
  have hL2 : L2.ncard = 1024 := by
    rw [← Nat.card_coe_set_eq]
    exact card_level2
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset,
    Set.ncard_union_eq hdis (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ (mul_right_injective (gl sc)), hL2]

theorem Sg_le : Sg ≤ P := fun _ hg => hg.1

theorem z_mem : gl zc ∈ Sg := by
  refine level2_le (level2_of (gl_mem zc_lt) ?_ ?_)
  · exact fin_ext_ap zc_lt (fixes_spec zfix 0 (by decide))
  · exact fin_ext_ap zc_lt (fixes_spec zfix 3 (by decide))

theorem z_ne_one : gl zc ≠ 1 := by
  intro h
  have e := ap_fin zc_lt 24
  rw [h, Perm.one_apply] at e
  have e' : ap L zc 24 = 24 := e
  have hm := zmove
  rw [e', Nat.beq_refl] at hm
  exact Bool.false_ne_true hm

theorem comm_of_base {x y : Perm (Fin 1755)} (hx : x ∈ P) (hy : y ∈ P)
    {f g : Nat → Nat} (hf : ∀ q : Fin 1755, f q = (x q : ℕ)) (hg : ∀ q : Fin 1755, g q = (y q : ℕ))
    (h : ∀ p ∈ bs, f (g p) = g (f p)) : x * y = y * x := by
  refine eq_of_base (P.mul_mem hx hy) (P.mul_mem hy hx) fun q hq => Fin.ext ?_
  rw [Perm.mul_apply, Perm.mul_apply, ← hf, ← hg, ← hg, ← hf]
  exact h q hq

theorem z_comm_level1 {g : Perm (Fin 1755)} (hg : g ∈ titsPairQ.levelSubgroup 1) :
    gl zc * g = g * gl zc := by
  have hle : titsPairQ.levelSubgroup 1 ≤ Subgroup.centralizer {gl zc} := by
    refine (Subgroup.closure_le _).2 fun s hs => ?_
    obtain ⟨c, hc, rfl, hfix⟩ := level_gen hs
    have hpre : ∀ p ∈ bs.take 1, p < 1755 := fun p hp => bs_lt p (List.mem_of_mem_take hp)
    have h := cenZ_spec cen c (codes_of c hc) (fixes_of (fix_nat hc hpre hfix))
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (comm_of_base (gl_mem zc_lt) (gl_mem hc) (ap_fin zc_lt) (ap_fin hc) h).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm

theorem Sg_le_level1 {g : Perm (Fin 1755)} (hg : g ∈ Sg) : g ∈ titsPairQ.levelSubgroup 1 := by
  obtain ⟨hP, h0, -⟩ := hg
  refine (level_mem_iff (by norm_num) g).2 ⟨hP, fun q hq => ?_⟩
  have e : bs.take 1 = [0] := rfl
  rw [e, List.mem_singleton] at hq
  rw [show q = 0 from Fin.ext hq, h0]

theorem z_comm {t : Perm (Fin 1755)} (ht : t ∈ Sg) : gl zc * t = t * gl zc :=
  z_comm_level1 (Sg_le_level1 ht)

theorem center_of_zOne {c : Perm (Fin 1755)} (hc : c ∈ Sg) (hcc : ∀ t ∈ Sg, c * t = t * c)
    {f : Nat → Nat} (hf : ∀ q : Fin 1755, f q = (c q : ℕ)) (h : zOne L zc sc f = true) :
    c = 1 ∨ c = gl zc := by
  have hcP := Sg_le hc
  have hs : ∀ p ∈ bs, f (ap L sc p) = ap L sc (f p) := by
    intro p hp
    have e := congrArg (fun y : Perm (Fin 1755) => (y ⟨p, bs_lt p hp⟩ : ℕ)) (hcc _ s_mem)
    simp only [Perm.mul_apply] at e
    have e1 := ap_fin sc_lt ⟨p, bs_lt p hp⟩
    have e2 := hf ⟨p, bs_lt p hp⟩
    change ap L sc p = _ at e1
    change f p = _ at e2
    rw [e1, hf, e2, ap_fin sc_lt, e]
  have hcl : ∀ c' ∈ codes, (∀ p ∈ [0, 3], ap L c' p = p) →
      ∀ p ∈ bs, f (ap L c' p) = ap L c' (f p) := by
    intro c' hc' hfix p hp
    have hlt := codes_lt c' hc'
    have hm : gl c' ∈ Sg := level2_le (level2_of (gl_mem hlt)
      (fin_ext_ap hlt (hfix 0 (by decide))) (fin_ext_ap hlt (hfix 3 (by decide))))
    have e := congrArg (fun y : Perm (Fin 1755) => (y ⟨p, bs_lt p hp⟩ : ℕ)) (hcc _ hm)
    simp only [Perm.mul_apply] at e
    have e1 := ap_fin hlt ⟨p, bs_lt p hp⟩
    have e2 := hf ⟨p, bs_lt p hp⟩
    change ap L c' p = _ at e1
    change f p = _ at e2
    rw [e1, hf, e2, ap_fin hlt, e]
  rcases zOne_spec h hs hcl with h1 | h1
  · refine Or.inl (eq_of_base hcP P.one_mem fun q hq => Fin.ext ?_)
    rw [Perm.one_apply, ← hf]
    exact h1 q hq
  · refine Or.inr (eq_of_base hcP (gl_mem zc_lt) fun q hq => Fin.ext ?_)
    rw [← hf, ← ap_fin zc_lt]
    exact h1 q hq

theorem ev5 {u₂ u₃ u₄ u₅ u₆ : List Nat} (h₂ : ∀ c ∈ u₂, c < 24) (h₃ : ∀ c ∈ u₃, c < 24)
    (h₄ : ∀ c ∈ u₄, c < 24) (h₅ : ∀ c ∈ u₅, c < 24) (h₆ : ∀ c ∈ u₆, c < 24) (q : Fin 1755) :
    ev L u₂ (ev L u₃ (ev L u₄ (ev L u₅ (ev L u₆ q)))) =
      ((wv gl u₂ * wv gl u₃ * wv gl u₄ * wv gl u₅ * wv gl u₆) q : ℕ) := by
  rw [ev_fin h₆, ev_fin h₅, ev_fin h₄, ev_fin h₃, ev_fin h₂]
  simp only [Perm.mul_apply]

theorem center_Sg {c : Perm (Fin 1755)} (hc : c ∈ Sg) (hcc : ∀ t ∈ Sg, c * t = t * c) :
    c = 1 ∨ c = gl zc := by
  obtain ⟨-, l2, l3, l4, l5, l6, -, -, -, -, -⟩ := ws_facts
  rcases Sg_cases hc with h | h
  · obtain ⟨u₂, h₂, u₃, h₃, u₄, h₄, u₅, h₅, u₆, h₆, e⟩ := cover h
    refine center_of_zOne hc hcc (fun q => ?_) (zsK_spec zs0 u₂ h₂ u₃ h₃ u₄ h₄ u₅ h₅ u₆ h₆)
    change ev L u₂ (ev L u₃ (ev L u₄ (ev L u₅ (ev L u₆ q)))) = _
    rw [ev5 (l2 u₂ h₂) (l3 u₃ h₃) (l4 u₄ h₄) (l5 u₅ h₅) (l6 u₆ h₆), e]
  · obtain ⟨u₂, h₂, u₃, h₃, u₄, h₄, u₅, h₅, u₆, h₆, e⟩ := cover h
    refine center_of_zOne hc hcc (fun q => ?_) (zsK_spec zs1 u₂ h₂ u₃ h₃ u₄ h₄ u₅ h₅ u₆ h₆)
    change ap L sc (ev L u₂ (ev L u₃ (ev L u₄ (ev L u₅ (ev L u₆ q))))) = _
    rw [ev5 (l2 u₂ h₂) (l3 u₃ h₃) (l4 u₄ h₄) (l5 u₅ h₅) (l6 u₆ h₆), ← e, ap_fin sc_lt,
      ← Perm.mul_apply, mul_inv_cancel_left]

end CertificateChecks.KernelT8074

end

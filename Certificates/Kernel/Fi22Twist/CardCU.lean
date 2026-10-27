module

public import Certificates.Kernel.Fi22Twist.CgFacts
public import Certificates.Kernel.Fi22Twist.NfChk
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist CFSG.KS CFSG.KS.E27Lie
open CFSG.KS.Fi22Twist CFSG.KC.Fi22Rk CFSG.KC.BfsPin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CertificateChecks.KernelFi22Rank.Q2 CFSG.KS.Raw
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CertificateChecks.KernelSpor

set_option maxRecDepth 400000

@[expose] noncomputable def baseImg (g : Equiv.Perm (Fin 3510)) : ℕ :=
  pt (MonoidHom.id _) g (bp 0) + pt (MonoidHom.id _) g (bp 1) * 2 ^ 12 +
    pt (MonoidHom.id _) g (bp 2) * 2 ^ 24 + pt (MonoidHom.id _) g (bp 3) * 2 ^ 36 +
    pt (MonoidHom.id _) g (bp 4) * 2 ^ 48 + pt (MonoidHom.id _) g (bp 5) * 2 ^ 60

theorem cg_sum6 (f : ℕ → ℕ) (hf : ∀ l < 6, f l < 4096) {l : ℕ} (hl : l < 6) :
    cg (f 0 + f 1 * 2 ^ 12 + f 2 * 2 ^ 24 + f 3 * 2 ^ 36 + f 4 * 2 ^ 48 + f 5 * 2 ^ 60) l =
      f l := by
  have h0 := hf 0 (by norm_num)
  have h1 := hf 1 (by norm_num)
  have h2 := hf 2 (by norm_num)
  have h3 := hf 3 (by norm_num)
  have h4 := hf 4 (by norm_num)
  have h5 := hf 5 (by norm_num)
  rw [cg_eq]
  interval_cases l <;> simp only [Nat.reducePow, Nat.reduceMul] <;> omega

theorem cg_baseImg (g : Equiv.Perm (Fin 3510)) {l : ℕ} (hl : l < 6) :
    cg (baseImg g) l = pt (MonoidHom.id _) g (bp l) :=
  cg_sum6 (fun l => pt (MonoidHom.id _) g (bp l))
    (fun l hl => lt_trans (pt_lt _ _ (bp_lt6 l hl)) (by norm_num)) hl

theorem baseImg_one : baseImg 1 = baseKey := by
  unfold baseImg
  simp only [pt_one]
  decide

theorem kAp_congr (g : ℕ) {c c' : ℕ} (h : ∀ l < 6, cg c l = cg c' l) : kAp g c = kAp g c' := by
  rw [kAp_sum, kAp_sum, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num),
    h 3 (by norm_num), h 4 (by norm_num), h 5 (by norm_num)]

theorem kAp_baseImg {p : ℕ} {g : Equiv.Perm (Fin 3510)}
    (hp : CFSG.KS.E27Lie.PRep 3510 12 (MonoidHom.id _) p g) (h : Equiv.Perm (Fin 3510)) :
    kAp p (baseImg h) = baseImg (g * h) := by
  have e : ∀ l < 6, ap p (cg (baseImg h) l) = pt (MonoidHom.id _) (g * h) (bp l) := by
    intro l hl
    rw [cg_baseImg h hl, ap_eq hp (pt_lt _ _ (bp_lt6 l hl)), pt_mul]
  rw [kAp_sum, e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num),
    e 4 (by norm_num), e 5 (by norm_num)]
  rfl


theorem baseImg_inj {g g' : Equiv.Perm (Fin 3510)} (hg : g ∈ fi22P) (hg' : g' ∈ fi22P)
    (h : baseImg g = baseImg g') : g = g' := by
  refine Fi22Base.eq_on_base hg hg' fun b hb hmem => ?_
  have hl : ∃ l < 6, bp l = b := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩, ⟨2, by norm_num, rfl⟩,
      ⟨3, by norm_num, rfl⟩, ⟨4, by norm_num, rfl⟩, ⟨5, by norm_num, rfl⟩]
  obtain ⟨l, hl, rfl⟩ := hl
  have k : cg (baseImg g) l = cg (baseImg g') l := by rw [h]
  rw [cg_baseImg g hl, cg_baseImg g' hl] at k
  unfold pt at k
  rw [dif_pos hb, dif_pos hb] at k
  exact k

theorem orb_card {KT G : ℕ → ℕ} {gof ng off sz : ℕ} (hsz : 0 < sz)
    (h : ∀ i < sz, orbK KT G gof ng off sz i = true) (gp : ℕ → Equiv.Perm (Fin 3510))
    (hrep : ∀ m < ng, CFSG.KS.E27Lie.PRep 3510 12 (MonoidHom.id _) (G (Nat.add gof m)) (gp m))
    (hP : ∀ m < ng, gp m ∈ fi22P) :
    (∀ i < sz, ∃ g ∈ Subgroup.closure {g | ∃ m < ng, gp m = g},
        baseImg g = fld(KT (Nat.add off i), 0, m72)) ∧
    (∀ g ∈ Subgroup.closure {g | ∃ m < ng, gp m = g},
        ∃ i < sz, fld(KT (Nat.add off i), 0, m72) = baseImg g) ∧
    Nat.card (Subgroup.closure {g | ∃ m < ng, gp m = g}) = sz := by
  have hHP : Subgroup.closure {g | ∃ m < ng, gp m = g} ≤ fi22P := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨m, hm, rfl⟩
    exact hP m hm
  have h1 : ∀ i < sz, ∃ g ∈ Subgroup.closure {g | ∃ m < ng, gp m = g},
      baseImg g = fld(KT (Nat.add off i), 0, m72) := by
    refine orbK_mem h (fun c => ∃ g ∈ Subgroup.closure {g | ∃ m < ng, gp m = g}, baseImg g = c)
      ⟨1, Subgroup.one_mem _, baseImg_one⟩ ?_
    rintro m hm c ⟨g, hg, rfl⟩
    exact ⟨gp m * g, mul_mem (Subgroup.subset_closure ⟨m, hm, rfl⟩) hg,
      (kAp_baseImg (hrep m hm) g).symm⟩
  have hstep : ∀ y ∈ Subgroup.closure {g | ∃ m < ng, gp m = g}, ∀ x : Equiv.Perm (Fin 3510),
      (∃ i < sz, fld(KT (Nat.add off i), 0, m72) = baseImg x) →
      ∃ i < sz, fld(KT (Nat.add off i), 0, m72) = baseImg (y * x) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      rintro x ⟨i, hi, hx⟩
      obtain ⟨i', hi', e⟩ := orbK_closed h i hi m hm
      refine ⟨i', hi', ?_⟩
      rw [e, hx]
      exact kAp_baseImg (hrep m hm) x
    | one =>
      intro x hx
      rwa [one_mul]
    | mul a b _ _ iha ihb =>
      intro x hx
      rw [mul_assoc]
      exact iha _ (ihb x hx)
    | inv a _ iha =>
      have hpow : ∀ n : ℕ, ∀ x : Equiv.Perm (Fin 3510),
          (∃ i < sz, fld(KT (Nat.add off i), 0, m72) = baseImg x) →
          ∃ i < sz, fld(KT (Nat.add off i), 0, m72) = baseImg (a ^ n * x) := by
        intro n
        induction n with
        | zero =>
          intro x hx
          rwa [pow_zero, one_mul]
        | succ n ihn =>
          intro x hx
          rw [pow_succ, mul_assoc]
          exact ihn _ (iha x hx)
      have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
      intro x hx
      rw [hinv]
      exact hpow _ x hx
  have h2 : ∀ g ∈ Subgroup.closure {g | ∃ m < ng, gp m = g},
      ∃ i < sz, fld(KT (Nat.add off i), 0, m72) = baseImg g := by
    obtain ⟨g0, hg0, e0⟩ := h1 0 hsz
    intro g hg
    have := hstep (g * g0⁻¹) (mul_mem hg (inv_mem hg0)) g0 ⟨0, hsz, e0.symm⟩
    rwa [inv_mul_cancel_right] at this
  refine ⟨h1, h2, ?_⟩
  let f : Fin sz → Subgroup.closure {g | ∃ m < ng, gp m = g} := fun i =>
    ⟨Classical.choose (h1 i i.2), (Classical.choose_spec (h1 i i.2)).1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i i' e
      have e' : baseImg (f i : Equiv.Perm (Fin 3510)) = baseImg (f i' : Equiv.Perm (Fin 3510)) := by
        rw [e]
      change baseImg (Classical.choose (h1 i i.2)) = baseImg (Classical.choose (h1 i' i'.2)) at e'
      rw [(Classical.choose_spec (h1 i i.2)).2, (Classical.choose_spec (h1 i' i'.2)).2] at e'
      exact Fin.ext (orbK_inj h i i.2 i' i'.2 e')
    · rintro ⟨g, hg⟩
      obtain ⟨i, hi, e⟩ := h2 g hg
      refine ⟨⟨i, hi⟩, Subtype.ext ?_⟩
      exact baseImg_inj (hHP (Classical.choose_spec (h1 i hi)).1) (hHP hg)
        ((Classical.choose_spec (h1 i hi)).2.trans e)
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem ob_spec {j k l : ℕ} (hl : l < 64) (h : ch431009ob_ (32 * j + k) = true) (hk : k < 32) :
    (64 * k + l < t12 szC j →
      orbK CK CG (t12 gofC j) (t12 ngC j) (t12 offC j) (t12 szC j) (64 * k + l) = true) ∧
    (64 * k + l < t12 szU j →
      orbK UK UG (t12 gofU j) (t12 ngU j) (t12 offU j) (t12 szU j) (64 * k + l) = true ∧
        subK UK CK (t12 offU j) (t12 offC j) (t12 szC j) (64 * k + l) = true) := by
  have ej : Nat.div (32 * j + k) (nat_lit 32) = j := by
    have e : (32 * j + k) / 32 = j := by omega
    exact e
  have ek : Nat.mod (32 * j + k) (nat_lit 32) = k := by
    have e : (32 * j + k) % 32 = k := by omega
    exact e
  unfold ch431009ob_ at h
  simp only [CFSG.KC.Fi22Twist.strictB_eq, ej, ek] at h
  have e := CFSG.KS.allBlk_spec h l hl
  beta_reduce at e
  have hI : Nat.add (Nat.mul (nat_lit 64) k) l = 64 * k + l := rfl
  rw [hI] at e
  obtain ⟨e1, e2⟩ := (CFSG.KS.bAnd_iff _ _).1 e
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  · simp only [blt_tt hi] at e1
    exact e1
  · simp only [blt_tt hi] at e2
    exact (CFSG.KS.bAnd_iff _ _).1 e2

theorem ob_blk {j k : ℕ} (hj : j < 5) (hk : 64 * k < t12 szC j) :
    ch431009ob_ (32 * j + k) = true := by
  interval_cases j
  · have e : t12 szC 0 = 162 := by decide
    rw [e] at hk
    have hk' : k < 3 := by omega
    interval_cases k
    exacts [ch431009ob_0, ch431009ob_1, ch431009ob_2]
  · have e : t12 szC 1 = 972 := by decide
    rw [e] at hk
    have hk' : k < 16 := by omega
    interval_cases k
    exacts [ch431009ob_32, ch431009ob_33, ch431009ob_34, ch431009ob_35, ch431009ob_36,
      ch431009ob_37, ch431009ob_38, ch431009ob_39, ch431009ob_40, ch431009ob_41, ch431009ob_42,
      ch431009ob_43, ch431009ob_44, ch431009ob_45, ch431009ob_46, ch431009ob_47]
  · have e : t12 szC 2 = 486 := by decide
    rw [e] at hk
    have hk' : k < 8 := by omega
    interval_cases k
    exacts [ch431009ob_64, ch431009ob_65, ch431009ob_66, ch431009ob_67, ch431009ob_68,
      ch431009ob_69, ch431009ob_70, ch431009ob_71]
  · have e : t12 szC 3 = 1458 := by decide
    rw [e] at hk
    have hk' : k < 23 := by omega
    interval_cases k
    exacts [ch431009ob_96, ch431009ob_97, ch431009ob_98, ch431009ob_99, ch431009ob_100,
      ch431009ob_101, ch431009ob_102, ch431009ob_103, ch431009ob_104, ch431009ob_105,
      ch431009ob_106, ch431009ob_107, ch431009ob_108, ch431009ob_109, ch431009ob_110,
      ch431009ob_111, ch431009ob_112, ch431009ob_113, ch431009ob_114, ch431009ob_115,
      ch431009ob_116, ch431009ob_117, ch431009ob_118]
  · have e : t12 szC 4 = 486 := by decide
    rw [e] at hk
    have hk' : k < 8 := by omega
    interval_cases k
    exacts [ch431009ob_128, ch431009ob_129, ch431009ob_130, ch431009ob_131, ch431009ob_132,
      ch431009ob_133, ch431009ob_134, ch431009ob_135]

theorem szU_le {j : ℕ} (hj : j < 5) : t12 szU j ≤ t12 szC j := by
  interval_cases j <;> decide

theorem ob_row {j i : ℕ} (hj : j < 5) (hi : i < t12 szC j) :
    orbK CK CG (t12 gofC j) (t12 ngC j) (t12 offC j) (t12 szC j) i = true ∧
    (i < t12 szU j → orbK UK UG (t12 gofU j) (t12 ngU j) (t12 offU j) (t12 szU j) i = true ∧
      subK UK CK (t12 offU j) (t12 offC j) (t12 szC j) i = true) := by
  have hs : t12 szC j ≤ 1458 := by
    interval_cases j <;> decide
  have hb := ob_blk hj (k := i / 64) (by omega)
  have h := ob_spec (l := i % 64) (Nat.mod_lt _ (by norm_num)) hb (by omega)
  rw [Nat.div_add_mod] at h
  exact ⟨h.1 hi, h.2⟩

@[expose] noncomputable def ugP (j t : ℕ) : Equiv.Perm (Fin 3510) :=
  permOfArr 3510 (unpack 3510 12 (UG (t12 gofU j + t)))

@[expose] noncomputable def uSub (j : ℕ) : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure {g | ∃ t < t12 ngU j, ugP j t = g}

theorem ugIdx_lt {j t : ℕ} (hj : j < 5) (ht : t < t12 ngU j) : t12 gofU j + t < 25 := by
  have h : t12 gofU j + t12 ngU j ≤ 25 := by
    interval_cases j <;> decide
  omega

theorem szC_pos {j : ℕ} (hj : j < 5) : 0 < t12 szC j := by
  interval_cases j <;> decide

theorem szU_pos {j : ℕ} (hj : j < 5) : 0 < t12 szU j := by
  interval_cases j <;> decide

theorem orbC {j : ℕ} (hj : j < 5) :
    (∀ i < t12 szC j, ∃ g ∈ cSub j, baseImg g = fld(CK (Nat.add (t12 offC j) i), 0, m72)) ∧
    (∀ g ∈ cSub j, ∃ i < t12 szC j, fld(CK (Nat.add (t12 offC j) i), 0, m72) = baseImg g) ∧
    Nat.card (cSub j) = t12 szC j :=
  orb_card (szC_pos hj) (fun i hi => (ob_row hj hi).1) (cgP j)
    (fun m hm => prep_of_PP (cg_PP (cgIdx_lt hj hm))) (fun m hm => cg_memP (cgIdx_lt hj hm))

theorem orbU {j : ℕ} (hj : j < 5) :
    (∀ i < t12 szU j, ∃ g ∈ uSub j, baseImg g = fld(UK (Nat.add (t12 offU j) i), 0, m72)) ∧
    (∀ g ∈ uSub j, ∃ i < t12 szU j, fld(UK (Nat.add (t12 offU j) i), 0, m72) = baseImg g) ∧
    Nat.card (uSub j) = t12 szU j :=
  orb_card (szU_pos hj) (fun i hi => ((ob_row hj (lt_of_lt_of_le hi (szU_le hj))).2 hi).1)
    (ugP j) (fun t ht => prep_of_PP (ug_PP (ugIdx_lt hj ht)))
    (fun t ht => ug_memP (ugIdx_lt hj ht))

theorem uSub_le_P {j : ℕ} (hj : j < 5) : uSub j ≤ fi22P := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨t, ht, rfl⟩
  exact ug_memP (ugIdx_lt hj ht)

theorem card_cSub {j : ℕ} (hj : j < 5) :
    Nat.card (cSub j) = [162, 972, 486, 1458, 486][j]! := by
  rw [(orbC hj).2.2]
  interval_cases j <;> decide

theorem card_uSub {j : ℕ} (hj : j < 5) :
    Nat.card (uSub j) = 3 ^ [4, 5, 5, 6, 5][j]! := by
  rw [(orbU hj).2.2]
  interval_cases j <;> decide

theorem card_cSub_mul {j : ℕ} (hj : j < 5) :
    Nat.card (cSub j) = [2, 4, 2, 2, 2][j]! * Nat.card (uSub j) := by
  rw [(orbC hj).2.2, (orbU hj).2.2]
  interval_cases j <;> decide

theorem uSub_le_cSub {j : ℕ} (hj : j < 5) : uSub j ≤ cSub j := by
  intro y hy
  obtain ⟨i, hi, e⟩ := (orbU hj).2.1 y hy
  have hs := ((ob_row hj (lt_of_lt_of_le hi (szU_le hj))).2 hi).2
  obtain ⟨x, hx, ex⟩ := subK_sound hs
  obtain ⟨g, hg, eg⟩ := (orbC hj).1 x hx
  have hgy : g = y := baseImg_inj (cSub_le_P hj hg) (uSub_le_P hj hy) (eg.trans (ex.trans e))
  rw [← hgy]
  exact hg

theorem jx_normK {j m : ℕ} (hj : j < 5) (hm : m < t12 ngC j) :
    normK NF CG UG UK j m (t12 gofC j) (t12 gofU j) (t12 ngU j) (t12 offU j) (t12 szU j) =
      true := by
  have h := jx431009All j hj
  unfold ch431009jx_ at h
  beta_reduce at h
  obtain ⟨h1, -⟩ := (bAnd_iff _ _).1 h
  exact ((bAnd_iff _ _).1 (allBlk_spec0 h1 m hm)).2

#kc_forall_tree nf431009All (fun j => ch431009nf_ j = true) 5
  CertificateChecks.KernelFi22Twist.ch431009nf_

theorem nf_lt {j m l : ℕ} (hj : j < 5) (hm : m < t12 ngC j) (hl : l < 6) :
    cg (fld(NF (Nat.add (Nat.mul 8 j) m), 0, m72)) l < 3510 := by
  have h := nf431009All j hj
  unfold ch431009nf_ at h
  have e := allBlk_spec0 h m hm
  beta_reduce at e
  rw [CFSG.KC.Fi22Twist.strictB_eq] at e
  exact Nat.le_of_ble_eq_true (allBlk_spec0 e l hl)

theorem conj_gen_mem {j m t : ℕ} (hj : j < 5) (hm : m < t12 ngC j) (ht : t < t12 ngU j) :
    cgP j m * ugP j t * (cgP j m)⁻¹ ∈ uSub j := by
  obtain ⟨h0, h1⟩ := normK_sound (jx_normK hj hm)
  have hcR : CFSG.KS.E27Lie.PRep 3510 12 (MonoidHom.id _) (CG (Nat.add (t12 gofC j) m)) (cgP j m) :=
    prep_of_PP (cg_PP (cgIdx_lt hj hm))
  have huR : CFSG.KS.E27Lie.PRep 3510 12 (MonoidHom.id _) (UG (Nat.add (t12 gofU j) t)) (ugP j t) :=
    prep_of_PP (ug_PP (ugIdx_lt hj ht))
  have hci : ∀ l < 6, cg (fld(NF (Nat.add (Nat.mul 8 j) m), 0, m72)) l =
      cg (baseImg (cgP j m)⁻¹) l := by
    intro l hl
    have hx := nf_lt hj hm hl
    have k : cg (kAp (CG (Nat.add (t12 gofC j) m)) (fld(NF (Nat.add (Nat.mul 8 j) m), 0, m72))) l =
        cg baseKey l := by rw [h0]
    rw [kAp_cg _ _ hl, cg_baseKey, ap_eq hcR hx] at k
    rw [cg_baseImg _ hl, ← k, ← pt_mul, inv_mul_cancel, pt_one]
  obtain ⟨x, hx, ex⟩ := h1 t ht
  rw [kAp_congr _ hci, kAp_baseImg huR, kAp_baseImg hcR] at ex
  obtain ⟨w, hw, ew⟩ := (orbU hj).1 x hx
  have hmem : cgP j m * (ugP j t * (cgP j m)⁻¹) ∈ fi22P :=
    mul_mem (cg_memP (cgIdx_lt hj hm)) (mul_mem (ug_memP (ugIdx_lt hj ht))
      (inv_mem (cg_memP (cgIdx_lt hj hm))))
  have hwe : w = cgP j m * (ugP j t * (cgP j m)⁻¹) :=
    baseImg_inj (uSub_le_P hj hw) hmem (ew.trans ex)
  rw [mul_assoc, ← hwe]
  exact hw

theorem mem_normalizer_of_conj {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let φ : H → H := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    have e := congrArg Subtype.val hab
    simpa [φ] using e
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hφ ⟨_, hx⟩
  have e := congrArg Subtype.val hy
  have e' : (y : G) = x := by simpa [φ] using e
  rw [← e']
  exact y.2

theorem cSub_le_normalizer {j : ℕ} (hj : j < 5) :
    cSub j ≤ Subgroup.normalizer (uSub j : Set (Equiv.Perm (Fin 3510))) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨m, hm, rfl⟩
  refine mem_normalizer_of_conj fun x hx => ?_
  unfold uSub at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    exact conj_gen_mem hj hm ht
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  | mul a b _ _ ha hb =>
    have e : cgP j m * (a * b) * (cgP j m)⁻¹ =
        cgP j m * a * (cgP j m)⁻¹ * (cgP j m * b * (cgP j m)⁻¹) := by group
    rw [e]
    exact mul_mem ha hb
  | inv a _ ha =>
    have e : cgP j m * a⁻¹ * (cgP j m)⁻¹ = (cgP j m * a * (cgP j m)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

theorem uSub_normal {j : ℕ} (hj : j < 5) : ((uSub j).subgroupOf (cSub j)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (uSub_le_cSub hj)]
  intro x c hx hc
  exact ((Subgroup.mem_normalizer_iff.1 (cSub_le_normalizer hj hc)) x).1 hx

end CertificateChecks.KernelFi22Twist

end

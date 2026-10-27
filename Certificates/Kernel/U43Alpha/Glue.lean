
module

public import Certificates.Kernel.U43Alpha.Checks
public import Certificates.Kernel.U43Mod.OutGlue
public import CFSG.Certificates.Kernel.U43Alpha.Sound
public import CFSG.Certificates.Kernel.U43Alpha.Count
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.AlphaU43.SoundBase
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43F3

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Alpha

open CFSG.KC.Enum CFSG.KC.U43Inv CFSG.KC.U43Out CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.U43Mod
  CFSG.KS.U43Inv CFSG.KS.U43Out CFSG.KS.U43Mod.LieOdd CertificateChecks.KernelU43Inv
  CertificateChecks.KernelU43Out CFSG.KC.U43Alpha CFSG.KS.U43Alpha
  CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Out
  CFSG.RankThree.PartTwo.Sec6.Res611Res6.U43P
  CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.AlphaU43

@[expose] noncomputable def fpt (g : Gp) (q : ℕ) : ℕ := if h : q < 820 then (g ⟨q, h⟩ : ℕ) else q

theorem fpt_eq (g : Gp) {q : ℕ} (hq : q < 820) : fpt g q = (g ⟨q, hq⟩ : ℕ) := by
  unfold fpt
  rw [dif_pos hq]

theorem fpt_lt (g : Gp) {q : ℕ} (hq : q < 820) : fpt g q < 820 := by
  rw [fpt_eq g hq]
  exact (g _).2

theorem fpt_mul (g h : Gp) {q : ℕ} (hq : q < 820) : fpt (g * h) q = fpt g (fpt h q) := by
  rw [fpt_eq _ hq, fpt_eq h hq, fpt_eq g (h _).2, Fin.eta, Equiv.Perm.mul_apply]

theorem fpt_one {q : ℕ} (hq : q < 820) : fpt 1 q = q := by
  rw [fpt_eq _ hq]
  rfl

theorem fpt_inv_cancel (g : Gp) {q : ℕ} (hq : q < 820) : fpt g⁻¹ (fpt g q) = q := by
  rw [← fpt_mul _ _ hq, inv_mul_cancel, fpt_one hq]

theorem fpt_cancel_inv (g : Gp) {q : ℕ} (hq : q < 820) : fpt g (fpt g⁻¹ q) = q := by
  rw [← fpt_mul _ _ hq, mul_inv_cancel, fpt_one hq]

theorem mem_fixS {f : ℕ → ℕ} {q : ℕ} : q ∈ fixS 820 f ↔ q < 820 ∧ f q = q := by
  unfold fixS
  rw [Finset.mem_filter, Finset.mem_range]

theorem card_fixS_conj (m t : Gp) :
    (fixS 820 (fpt (m * t * m⁻¹))).card = (fixS 820 (fpt t)).card := by
  refine Finset.card_bij' (fun a _ => fpt m⁻¹ a) (fun a _ => fpt m a) (fun a ha => ?_) (fun a ha => ?_)
    (fun a ha => fpt_cancel_inv m (mem_fixS.1 ha).1) (fun a ha => fpt_inv_cancel m (mem_fixS.1 ha).1)
  · obtain ⟨ha1, ha2⟩ := mem_fixS.1 ha
    refine mem_fixS.2 ⟨fpt_lt _ ha1, ?_⟩
    rw [fpt_mul _ _ ha1, fpt_mul _ _ (fpt_lt _ ha1)] at ha2
    have := congrArg (fpt m⁻¹) ha2
    rwa [fpt_inv_cancel _ (fpt_lt _ (fpt_lt _ ha1))] at this
  · obtain ⟨ha1, ha2⟩ := mem_fixS.1 ha
    refine mem_fixS.2 ⟨fpt_lt _ ha1, ?_⟩
    rw [fpt_mul _ _ (fpt_lt _ ha1), fpt_inv_cancel _ ha1, fpt_mul _ _ ha1, ha2]

theorem cntFix_fpt {f : ℕ → ℕ} {g : Gp} (hf : ∀ q (hq : q < 820), f q = (g ⟨q, hq⟩ : ℕ)) :
    cntFix f 820 = (fixS 820 (fpt g)).card := by
  rw [cntFix_eq]
  unfold fixS
  congr 1
  refine Finset.filter_congr fun q hq => ?_
  rw [hf q (Finset.mem_range.1 hq), fpt_eq g (Finset.mem_range.1 hq)]

theorem fixIn_spec {c : ℕ} (h : fixIn c = true) : c = 20 ∨ c = 40 ∨ c = 92 := by
  unfold fixIn at h
  cases h1 : Nat.beq c 20
  · rw [h1] at h
    dsimp only at h
    cases h2 : Nat.beq c 40
    · rw [h2] at h
      dsimp only at h
      exact Or.inr (Or.inr (Nat.eq_of_beq_eq_true h))
    · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2))
  · exact Or.inl (Nat.eq_of_beq_eq_true h1)

theorem rep_fix {i : ℕ} (hi : i < 14) :
    Nat.land (RP i) 1023 < 1024 ∧ ((fixS 820 (fpt (tElt (Nat.land (RP i) 1023)))).card = 20 ∨
      (fixS 820 (fpt (tElt (Nat.land (RP i) 1023)))).card = 40 ∨
      (fixS 820 (fpt (tElt (Nat.land (RP i) 1023)))).card = 92) := by
  have hj : Nat.land (RP i) 1023 < 1024 := Nat.lt_succ_of_le Nat.and_le_right
  have h := allN_spec ch12650fix i hi
  unfold repOK at h
  rw [sbEq, bAnd_iff, beq_iff] at h
  refine ⟨hj, ?_⟩
  rw [← cntFix_fpt fun q hq => (ET_eq hj q hq).1, h.2]
  exact fixIn_spec h.1

theorem conj_pt {k j m q : ℕ} (hk : k < 1024) (hj : j < 1024) (hm : m < 1024) (hq : q < 820)
    (e : ET m (ET j (ETi m q)) = ET k q) :
    (tElt k ⟨q, hq⟩ : ℕ) = (tElt m * tElt j * (tElt m)⁻¹) ⟨q, hq⟩ := by
  rw [← (ET_eq hk q hq).1, ← e, (ET_eq hm q hq).2, (ET_eq hj _ (Fin.is_lt _)).1, Fin.eta,
    (ET_eq hm _ (Fin.is_lt _)).1, Fin.eta]
  rfl

theorem tag_one {k : ℕ} (hk : k < 1024) (h1 : Nat.land (KernelU43Out.FR k) (nat_lit 3) = 1) :
    ∃ x < 820, ET k (ET k x) ≠ x := by
  have h := allN_spec kF k hk
  unfold fRec at h
  rw [sbEq, sbEq, sbEq] at h
  generalize Nat.shiftRight (KernelU43Out.FR k) (nat_lit 2) = x at h
  generalize Nat.land (KernelU43Out.FR k) (nat_lit 3) = t at h h1
  subst h1
  cases h0 : Nat.beq 1 0 <;> rw [h0] at h <;> dsimp only at h
  · cases h1' : Nat.beq 1 1 <;> rw [h1'] at h <;> dsimp only at h
    · exact absurd h1' (by decide)
    · simp only [bAnd_iff, blt_iff, bNot_iff, beq_false_iff] at h
      exact ⟨x, h.1, h.2⟩
  · exact absurd h0 (by decide)

theorem tag_conj {k : ℕ} (hk : k < 1024) (h2 : 2 ≤ Nat.land (KernelU43Out.FR k) (nat_lit 3)) :
    ∃ i < 14, ∃ m < 1024, tElt k = tElt m * tElt (Nat.land (RP i) 1023) * (tElt m)⁻¹ := by
  have h := allN_spec ch12650cj k hk
  unfold cjOK at h
  have hnl : ¬ Nat.land (KernelU43Out.FR k) (nat_lit 3) < nat_lit 2 := by
    intro h'
    change Nat.land (KernelU43Out.FR k) 3 < 2 at h'
    change 2 ≤ Nat.land (KernelU43Out.FR k) 3 at h2
    omega
  rw [blt_false hnl] at h
  dsimp only at h
  rw [sbEq, sbEq, sbEq, sbEq] at h
  simp only [bAnd_iff, blt_iff] at h
  obtain ⟨hi, hm, e0, e1, e9, e84⟩ := h
  have hj : Nat.land (RP (Nat.land (CJ k) 15)) 1023 < 1024 := Nat.lt_succ_of_le Nat.and_le_right
  refine ⟨_, hi, _, hm, ?_⟩
  unfold cjAt at e0 e1 e9 e84
  rw [beq_iff] at e0 e1 e9 e84
  have hT : ∀ x, tElt x ∈ Nrm := tElt_Nrm
  exact sep4 (hT k) (Nrm.mul_mem (Nrm.mul_mem (hT _) (hT _)) (Nrm.inv_mem (hT _)))
    (conj_pt hk hj hm _ e0) (conj_pt hk hj hm _ e1) (conj_pt hk hj hm _ e9) (conj_pt hk hj hm _ e84)

theorem outer_invol_fix {t : Gp} (ht : t ∈ Nrm) (hN : t ∉ Nsub) (h2 : t * t = 1) :
    (fixS 820 (fpt t)).card = 20 ∨ (fixS 820 (fpt t)).card = 40 ∨ (fixS 820 (fpt t)).card = 92 := by
  have h2' : (⟨t, ht⟩ : (Nrm : Subgroup Gp)) * ⟨t, ht⟩ = 1 := Subtype.ext h2
  obtain ⟨c, hc, -⟩ := exists_conj_mem_tSub autFacts ⟨t, ht⟩ ⟨t, ht⟩ h2' h2' rfl
  obtain ⟨k, hk, hke⟩ := tSurj _ hc
  have hke' : tElt k = (c : Gp) * t * (c : Gp)⁻¹ := by
    rw [hke]
    rfl
  have hcard : (fixS 820 (fpt t)).card = (fixS 820 (fpt (tElt k))).card := by
    rw [hke', card_fixS_conj]
  have hkN : tElt k ∉ Nsub := by
    intro hin
    apply hN
    have := conj_mem_Nsub (Nrm.inv_mem c.2) hin
    rwa [hke', show ((c : Gp))⁻¹ * ((c : Gp) * t * (c : Gp)⁻¹) * ((c : Gp))⁻¹⁻¹ = t by group] at this
  have hk2 : tElt k * tElt k = 1 := by
    rw [hke']
    calc (c : Gp) * t * (c : Gp)⁻¹ * ((c : Gp) * t * (c : Gp)⁻¹) = (c : Gp) * (t * t) * (c : Gp)⁻¹ := by
          group
      _ = 1 := by rw [h2]; group
  rcases Nat.lt_or_ge (Nat.land (KernelU43Out.FR k) (nat_lit 3)) 2 with hlt | hge
  · exfalso
    rcases Nat.lt_or_ge (Nat.land (KernelU43Out.FR k) (nat_lit 3)) 1 with h0 | h1
    · rcases fRec_cases hk with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact hkN (inner_mem hk h)
      · omega
      · omega
      · omega
    · obtain ⟨x, hx, hne⟩ := tag_one hk (by omega)
      apply hne
      rw [(ET_eq hk _ hx).1, (ET_eq hk _ (Fin.is_lt _)).1, Fin.eta, ← Equiv.Perm.mul_apply, hk2]
      rfl
  · obtain ⟨i, hi, m, hm, he⟩ := tag_conj hk hge
    obtain ⟨-, hfix⟩ := rep_fix hi
    rw [hcard, he, card_fixS_conj]
    exact hfix

@[expose] noncomputable def KP (l j : ℕ) : Gp := permOfArr 820 (unpack 820 10 (KS l j))

theorem orb_ok {l : ℕ} (hl : l < 4) : orbPart 820 (KS l) 4 (L l) (W l) (RO l) (NB l) (SZ l) = true := by
  interval_cases l
  · exact ch12650orb0
  · exact ch12650orb1
  · exact ch12650orb2
  · exact ch12650orb3

theorem KP_facts {l j : ℕ} (hl : l < 4) (hj : j < 4) :
    (∀ q (hq : q < 820), pg 10 1023 (KS l j) q = (KP l j ⟨q, hq⟩ : ℕ)) ∧ KP l j ∈ Nsub := by
  have hp := allN_spec (allN_spec ch12650perm l hl) j hj
  have hr := rep_permOfArr (isInvA_unpack hp)
  have hX : PRep 820 10 (KS l j) (KP l j) := prep_of_rep hr.1
  exact ⟨fun q hq => hX ⟨q, hq⟩,
    KernelU43Aut3962.mem_of_inN hX (allN_spec (allN_spec ch12650inN l hl) j hj)⟩

theorem KP_zero {l : ℕ} (hl : l < 4) : KP l 0 = psi (ev (repW (l + 1))) := by
  obtain ⟨hpt, ⟨y, hy⟩⟩ := KP_facts hl (by norm_num : 0 < 4)
  have h := allN_spec ch12650rep l hl
  unfold base3A at h
  simp only [bAnd_iff, beq_iff] at h
  obtain ⟨b0, b1, b9⟩ := h
  rw [← hy]
  congr 1
  refine hsep _ _ ?_ ?_ ?_
  · rw [hy, ← hpt 0 (by norm_num), b0]
    exact (act_spec (repW (l + 1)) ⟨0, by norm_num⟩).symm
  · rw [hy, ← hpt 1 (by norm_num), b1]
    exact (act_spec (repW (l + 1)) ⟨1, by norm_num⟩).symm
  · rw [hy, ← hpt 9 (by norm_num), b9]
    exact (act_spec (repW (l + 1)) ⟨9, by norm_num⟩).symm

theorem KP_comm {l j : ℕ} (hl : l < 4) (hj : j < 4) : KP l j * KP l 0 = KP l 0 * KP l j := by
  obtain ⟨hpj, ⟨y, hy⟩⟩ := KP_facts hl hj
  obtain ⟨hp0, ⟨z, hz⟩⟩ := KP_facts hl (by norm_num : 0 < 4)
  have h := allN_spec (allN_spec ch12650comm l hl) j hj
  simp only [bAnd_iff] at h
  obtain ⟨c0, c1, c9⟩ := h
  unfold commAt at c0 c1 c9
  rw [beq_iff] at c0 c1 c9
  have pt : ∀ q (hq : q < 820), pg 10 1023 (KS l j) (pg 10 1023 (KS l 0) q) =
        pg 10 1023 (KS l 0) (pg 10 1023 (KS l j) q) →
      ((KP l j * KP l 0) ⟨q, hq⟩ : ℕ) = (KP l 0 * KP l j) ⟨q, hq⟩ := by
    intro q hq e
    rw [hp0 q hq, hpj _ (Fin.is_lt _), Fin.eta, hpj q hq, hp0 _ (Fin.is_lt _), Fin.eta] at e
    exact e
  rw [← hy, ← hz, ← map_mul, ← map_mul]
  congr 1
  refine hsep _ _ ?_ ?_ ?_
  · rw [map_mul, map_mul, hy, hz]
    exact pt 0 (by norm_num) c0
  · rw [map_mul, map_mul, hy, hz]
    exact pt 1 (by norm_num) c1
  · rw [map_mul, map_mul, hy, hz]
    exact pt 9 (by norm_num) c9

theorem fix_not {l : ℕ} (hl : l < 4) {n : Gp} (h2 : n * n = 1) (hc : ∀ j < 4, n * KP l j = KP l j * n) :
    (fixS 820 (fpt n)).card ≠ 20 ∧ (fixS 820 (fpt n)).card ≠ 40 ∧ (fixS 820 (fpt n)).card ≠ 92 := by
  have ho := orb_ok hl
  set f := fpt n with hfdef
  have hf : ∀ x < 820, f x < 820 := fun x hx => fpt_lt n hx
  have hff : ∀ x < 820, f (f x) = x := fun x hx => by
    rw [hfdef, ← fpt_mul _ _ hx, h2, fpt_one hx]
  have hpg : ∀ j < 4, ∀ x < 820, pg 10 1023 (KS l j) x = fpt (KP l j) x := fun j hj x hx => by
    rw [(KP_facts hl hj).1 x hx, fpt_eq _ hx]
  have hfg : ∀ j < 4, ∀ x < 820, f (pg 10 1023 (KS l j) x) = pg 10 1023 (KS l j) (f x) :=
    fun j hj x hx => by
      rw [hpg j hj x hx, hpg j hj _ (hf x hx), hfdef, ← fpt_mul _ _ hx, ← fpt_mul _ _ hx, hc j hj]
  have hfix : ∀ x < 820, ∀ y < 820, labOf (L l) x = labOf (L l) y → f x = x → f y = y := by
    intro x hx y hy hl' hfx
    refine orbPart_conn ho (fun z => f z = z) (fun z hz j hj => ?_) hx hy hl' hfx
    rw [hfg j hj z hz, hpg j hj _ (hf z hz), hpg j hj z hz]
    constructor
    · intro e
      have := congrArg (fpt (KP l j)⁻¹) e
      rwa [fpt_inv_cancel _ (hf z hz), fpt_inv_cancel _ hz] at this
    · intro e
      rw [e]
  have hlab : ∀ x < 820, ∀ y < 820, labOf (L l) x = labOf (L l) y →
      labOf (L l) (f x) = labOf (L l) (f y) := by
    intro x hx y hy hl'
    have := orbPart_conn ho (fun z => labOf (L l) (f z) = labOf (L l) (f x)) (fun z hz j hj => by
      change labOf (L l) (f (pg 10 1023 (KS l j) z)) = _ ↔ labOf (L l) (f z) = _
      rw [hfg j hj z hz, orbPart_inv ho (hf z hz) hj]) hx hy hl' rfl
    exact this.symm
  have hcls : ∀ i < NB l, (cls 820 (labOf (L l)) i).card = szOf (SZ l) i := fun i hi =>
    orbPart_card ho hi
  have hnb : ∀ x < 820, labOf (L l) x < NB l := fun x hx => orbPart_lab_lt ho hx
  by_cases h3 : l < 3
  · have hsum := card_fix_eq_sum hf hff hfix
    have himg : (fixS 820 f).image (labOf (L l)) ⊆ Finset.range (NB l) := by
      intro i hi
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
      exact Finset.mem_range.2 (hnb x (mem_fixS.1 hx).1)
    have hsum' : (fixS 820 f).card = ∑ i ∈ (fixS 820 f).image (labOf (L l)), szOf (SZ l) i := by
      rw [hsum]
      exact Finset.sum_congr rfl fun i hi => hcls i (Finset.mem_range.1 (himg hi))
    have hns : noFixSum (SZ l) (NB l) = true := by
      interval_cases l
      · exact ch12650sum0
      · exact ch12650sum1
      · exact ch12650sum2
    rw [hsum']
    exact noFixSum_sound hns _ himg
  · have hl3 : l = 3 := by omega
    subst hl3
    have hodd := ch12650odd
    simp only [bAnd_iff, beq_iff] at hodd
    obtain ⟨-, o1, o3, o9, o81⟩ := hodd
    have hcnt : ∀ s, ((Finset.range (NB 3)).filter fun i => (cls 820 (labOf (L 3)) i).card = s).card =
        cntSz (SZ 3) (NB 3) s := by
      intro s
      rw [cntSz_eq]
      exact congrArg Finset.card (Finset.filter_congr fun i hi => by rw [hcls i (Finset.mem_range.1 hi)])
    let g : ℕ → ℕ := fun x => (cls 820 (labOf (L 3)) (labOf (L 3) x)).card
    have lb : ∀ s, s % 2 = 1 → cntSz (SZ 3) (NB 3) s % 2 = 1 →
        s ≤ ((fixS 820 f).filter fun x => g x = s).card :=
      fun s hs hc => le_card_fix_size hf hff hfix hlab hnb (Nat.odd_iff.2 hs)
        (Nat.odd_iff.2 (by rw [hcnt]; exact hc))
    have l1 := lb 1 rfl o1
    have l3 := lb 3 rfl o3
    have l9 := lb 9 rfl o9
    have l81 := lb 81 rfl o81
    have hB := Finset.card_eq_sum_card_fiberwise (f := g) (t := ({1, 3, 9, 81} : Finset ℕ))
      (s := (fixS 820 f).filter fun x => g x ∈ ({1, 3, 9, 81} : Finset ℕ))
      (fun x hx => (Finset.mem_filter.1 hx).2)
    have hfib : ∀ b ∈ ({1, 3, 9, 81} : Finset ℕ),
        (((fixS 820 f).filter fun x => g x ∈ ({1, 3, 9, 81} : Finset ℕ)).filter fun x => g x = b) =
          (fixS 820 f).filter fun x => g x = b := by
      intro b hb
      rw [Finset.filter_filter]
      exact Finset.filter_congr fun x _ => ⟨fun h => h.2, fun h => ⟨h ▸ hb, h⟩⟩
    rw [Finset.sum_congr rfl fun b hb => congrArg Finset.card (hfib b hb)] at hB
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at hB
    have hle : ((fixS 820 f).filter fun x => g x ∈ ({1, 3, 9, 81} : Finset ℕ)).card ≤
        (fixS 820 f).card := Finset.card_filter_le _ _
    refine ⟨?_, ?_, ?_⟩ <;> omega

theorem class_claim {l : ℕ} (hl : l < 4) : ClassClaim l := by
  intro n hn hnN h2 hρ
  refine Classical.byContradiction fun hcon => ?_
  have hc : ∀ j < 4, n * KP l j = KP l j * n := by
    intro j hj
    refine Classical.byContradiction fun hne => ?_
    have key : ∀ ρ, KP l 0 = ρ → KP l j * ρ = ρ * KP l j := by
      intro ρ e
      subst e
      exact KP_comm hl hj
    exact hcon ⟨KP l j, (KP_facts hl hj).2, key _ (KP_zero hl), hne⟩
  obtain ⟨a, b, c⟩ := fix_not hl h2 hc
  rcases outer_invol_fix hn hnN h2 with h | h | h
  · exact a h
  · exact b h
  · exact c h

theorem outer_not_fix_kernel : ∀ b : X₀, orderOf b = 3 → ∀ τ : MulAut X₀, τ ^ 2 = 1 →
    τ ∉ (MulAut.conj : X₀ →* MulAut X₀).range →
      ¬ ∀ c ∈ Subgroup.centralizer ({b} : Set X₀), τ c = c :=
  fun _ hb τ hτ2 hτo => outer_not_fix_of_claim (fun _ hl => class_claim hl) hb τ hτ2 hτo

end CertificateChecks.KernelU43Alpha

end

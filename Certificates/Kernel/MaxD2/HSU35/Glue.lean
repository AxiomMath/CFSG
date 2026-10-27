module

public import Certificates.Kernel.MaxD2.HSU35.Checks
public import Certificates.Kernel.MaxD2.HSW0.Glue
public import Certificates.Kernel.MaxD2.HSU.Glue
public import Certificates.Kernel.MaxD2.McLP.CentGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.HSU35

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CFSG.PSL3Four.Native Certificates.FusD2Perm Certificates.MaxD2Perm Certificates.MaxD2Heis
  Certificates.HSOver Certificates.HSU35
open CertificateChecks.KernelMaxD2.HSW0 (wP_u hn found_rec)

theorem HC : HypsC dataU HSU.KH := HSU.hypsH.toHypsBC.toHypsC

theorem wU_u {wd : List Int} {r : Nat}
    (h : wordEqK 100 7 (mask 7) (pidn 100 7) HSU.GP HSU.GPI 2 wd r = true) :
    wT dataU wd = unpack 100 7 r := c_wT_u HC h

theorem notIn_ne {cnt : Nat} {T : Nat → Nat} {x : Nat} (h : notInK cnt T x = true) :
    ∀ i < cnt, T i ≠ x := by
  intro i hi e
  unfold notInK at h
  have h' := (PK.allN_iff.1 h) i hi
  beta_reduce at h'
  rw [e, Nat.beq_refl] at h'
  exact absurd h' (by decide)

theorem found_false {cnt : Nat} {T PL : Nat → Nat} {X : Nat} (hT : ∀ i < cnt, Cn 100 7 (T i))
    (hX : Cn 100 7 X) (h : ∀ i < cnt, T i ≠ X) :
    found (indexOf (penumRec 100 7 cnt T PL).tabs) (penumRec 100 7 cnt T PL).tabs
      (unpack 100 7 X) = false := by
  rw [Bool.eq_false_iff, ne_eq, found_iff]
  rintro ⟨i, hi, e⟩
  rw [rec_size] at hi
  rw [rec_get hi] at e
  exact h i hi (u_inj (hT i hi) hX e)

theorem beq_pw {p : Nat} (hp : Cn 100 7 p) (e : Nat) :
    (powT 100 (unpack 100 7 p) e == idTab 100) = Nat.beq (pw 100 7 p e) (pidn 100 7) := by
  rw [powT_u hn hp e, id_u hn, eq_u (pw_canon hn hp e) (pidn_canon hn)]

theorem beq_id {p : Nat} (hp : Cn 100 7 p) :
    (unpack 100 7 p == idTab 100) = Nat.beq p (pidn 100 7) := by
  rw [id_u hn, eq_u hp (pidn_canon hn)]

theorem k_wds : wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsOverTW (HSU.TT 0) = true ∧
    wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsOverWW (HSU.REP 1) = true ∧
    wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsOverCW (QT 0) = true ∧
    wordEqK 100 7 (mask 7) (pidn 100 7) HSU.GP HSU.GPI 2 xyCW (QT 0) = true ∧
    permOK 100 7 (mask 7) (100 * 7) (QT 0) (QT 1) = true ∧
    wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsOverE1W (EE.G 0) = true ∧
    wordEqK 100 7 (mask 7) (pidn 100 7) HSU.GP HSU.GPI 2 xyE1W (EE.G 0) = true ∧
    wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsOverE2W (EE.G 1) = true ∧
    wordEqK 100 7 (mask 7) (pidn 100 7) HSU.GP HSU.GPI 2 xyE2W (EE.G 1) = true ∧
    allN 2 (fun j => canonK 100 7 (mask 7) (100 * 7) (EE.G j)) = true := by
  have h := k_wd
  unfold wdK at h
  simp only [Bool.and_eq_true] at h
  exact h

theorem cGP : Cn 100 7 (HSU.GP 0) ∧ Cn 100 7 (HSU.GP 1) :=
  ⟨(perm_canon (c_gp_perm HC (j := 0) (by decide)) hn).1,
    (perm_canon (c_gp_perm HC (j := 1) (by decide)) hn).1⟩

theorem cT : Cn 100 7 (HSU.TT 0) := (perm_canon HSU.k_tp hn).1

theorem pW : permOK 100 7 (mask 7) (100 * 7) (HSU.REP 1) (HSU.REPI 1) = true :=
  HC.hRi 1 (by decide)

theorem cW : Cn 100 7 (HSU.REP 1) ∧ Cn 100 7 (HSU.REPI 1) := perm_canon pW hn

theorem cC : Cn 100 7 (QT 0) ∧ Cn 100 7 (QT 1) := perm_canon k_wds.2.2.2.2.1 hn

theorem tabX_eq : tabX = unpack 100 7 (HSU.GP 0) := wP_u ((PK.allN_iff.1 HSU.k_xy) 0 (by decide))

theorem tabY_eq : tabY = unpack 100 7 (HSU.GP 1) := wP_u ((PK.allN_iff.1 HSU.k_xy) 1 (by decide))

theorem tabT_eq : tabT = unpack 100 7 (HSU.TT 0) := wP_u k_wds.1

theorem tabW_eq : tabW = unpack 100 7 (HSU.REP 1) := wP_u k_wds.2.1

theorem tabC_eq : tabC = unpack 100 7 (QT 0) := wP_u k_wds.2.2.1

theorem wi_eq : invTab 100 (unpack 100 7 (HSU.REP 1)) = unpack 100 7 (HSU.REPI 1) :=
  inv_u pW

theorem ci_eq : invTab 100 (unpack 100 7 (QT 0)) = unpack 100 7 (QT 1) := inv_u k_wds.2.2.2.2.1

theorem rE : hrEnum dataU = penumRec 100 7 HSU.RE.cnt HSU.RE.T HSU.RE.PL :=
  (h_rEnum_eq HSU.hypsH).1

theorem nE : nEnum dataU = penumRec 100 7 HSU.NE.cnt HSU.NE.T HSU.NE.PL := (c_nEnum_eq HC).1

theorem rt_canon {i : Nat} (hi : i < HSU.RE.cnt) : Cn 100 7 (HSU.RE.T i) := h_rt_canon HSU.hypsH hi

theorem nt_canon {i : Nat} (hi : i < HSU.NE.cnt) : Cn 100 7 (HSU.NE.T i) := c_nt_canon HC hi

theorem orders_ok : checkOrders = true := by
  obtain ⟨cx, cy⟩ := cGP
  have h := k_ord
  unfold ordK at h
  unfold checkOrders
  rw [tabX_eq, tabY_eq, tabT_eq, comp_u cx cy, beq_pw cx 8, beq_pw cx 4, beq_pw cy 3, beq_id cy,
    beq_pw (cc cx cy) 7, beq_id (cc cx cy), beq_pw cT 8, beq_pw cT 4]
  simp only [Bool.and_eq_true, and_assoc] at h ⊢
  exact h

theorem ident_ok : checkIdent = true := by
  unfold checkIdent
  rw [wU_u (wd := xyU0W) HSU.k_rg0, wP_u (wd := hsFiveUW) HSW0.k_all.2.2.2.2.2.2.1,
    wU_u (wd := xyV0W) HSU.k_rg1, wP_u (wd := hsFiveVW) HSW0.k_all.2.2.2.2.2.2.2.1,
    wU_u (wd := xyTW) HSU.k_tw, tabT_eq,
    wU_u (wd := xyWW) (r := HSU.REP 1) ((PK.allN_iff.1 HSU.k_rw) 0 (by decide)), tabW_eq,
    wU_u k_wds.2.2.2.1, tabC_eq, wU_u k_wds.2.2.2.2.2.2.1, wP_u k_wds.2.2.2.2.2.1,
    wU_u k_wds.2.2.2.2.2.2.2.2.1, wP_u k_wds.2.2.2.2.2.2.2.1]
  simp only [beq_self_eq_true, Bool.and_self]

theorem tcent_ok : checkTCent = true := by
  unfold checkTCent
  simp only []
  rw [rE, rec_size, allBelow_iff']
  intro k hk
  beta_reduce
  have ck := rt_canon hk
  rw [rec_get hk, tabT_eq, comp_u cT ck, comp_u ck cT, eq_u (cc cT ck) (cc ck cT), beq_id ck]
  exact (PK.allN_iff.1 k_tc) k hk

theorem k_ws : notInK HSU.NE.cnt HSU.NE.T (HSU.REP 1) = true ∧ Nat.blt (r32 QH 0) 8 = true ∧
    Nat.beq (pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (HSU.REP 1) (HSU.TT 0)) (HSU.REPI 1))
      (pw 100 7 (HSU.TT 0) (r32 QH 0)) = true := by
  have h := k_w
  unfold wK at h
  simp only [Bool.and_eq_true] at h
  exact h

theorem w_ok : checkW = true := by
  obtain ⟨h1, h2, h3⟩ := k_ws
  obtain ⟨c0, c1⟩ := cW
  unfold checkW
  simp only []
  rw [nE, tabW_eq, wi_eq, tabT_eq]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨by simp [size_u], ?_⟩, ?_⟩, ?_⟩
  · rw [inv_comp pW, id_u hn]
    exact beq_self_eq_true _
  · rw [Bool.not_eq_true', found_false (fun i hi => nt_canon hi) c0 (notIn_ne h1)]
  · rw [anyBelow_iff]
    refine ⟨r32 QH 0, Nat.blt_eq.mp h2, ?_⟩
    rw [comp_u c0 cT, comp_u (cc c0 cT) c1, powT_u hn cT,
      eq_u (cc (cc c0 cT) c1) (pw_canon hn cT _)]
    exact h3

theorem rep_test {D : Certificates.MaxD2Perm.Data} {K : Pk} (H : HypsC D K) {i k : Nat} (h0 : 0 < i) (hi : i < K.nr)
    (hk : k < K.cnt) :
    (∃ e < K.cnt, K.NT e = pcomp K.n K.w (mask K.w)
      (pcomp K.n K.w (mask K.w) (K.REPI i) (K.NT k)) (K.REP i)) ↔
      Nat.land (r32 K.H (Nat.add (Nat.mul K.cnt i) k)) 1 = 1 := by
  have ht := H.hTest i h0 hi
  unfold repK at ht
  simp only [PK.strictB_eq] at ht
  obtain ⟨hrb, hts⟩ := band_e ht
  exact testK_spec H.hn (fun e he => c_nt_canon H he) H.hS (fun t ht => (H.hPts.2 t ht).2)
    (H.hRi i hi) (fun t ht => Nat.eq_of_beq_eq_true ((PK.allN_iff.1 hrb) t ht)) hk
    ((PK.allN_iff.1 hts) k hk)

theorem wconj_iff {k : Nat} (hk : k < HSU.NE.cnt) :
    (∃ e < HSU.NE.cnt, HSU.NE.T e =
      pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (HSU.REPI 1) (HSU.NE.T k)) (HSU.REP 1)) ↔
      Nat.land (r32 HSU.H (Nat.add (Nat.mul HSU.NE.cnt 1) k)) 1 = 1 :=
  rep_test (K := HSU.KH) HC (i := 1) (by decide) (by decide) hk

theorem kernel_ok : checkKernel = true := by
  obtain ⟨c0, c1⟩ := cW
  obtain ⟨d0, d1⟩ := cC
  unfold checkKernel
  simp only []
  rw [nE, tabW_eq, wi_eq, tabC_eq, ci_eq]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨by simp [size_u], ?_⟩, by simp [size_u]⟩, ?_⟩, ?_⟩
  · rw [inv_comp pW, id_u hn]
    exact beq_self_eq_true _
  · rw [inv_comp k_wds.2.2.2.2.1, id_u hn]
    exact beq_self_eq_true _
  rw [rec_size, allBelow_iff']
  intro k hk
  beta_reduce
  have ck := nt_canon hk
  have hT : ∀ i < HSU.NE.cnt, Cn 100 7 (HSU.NE.T i) := fun i hi => nt_canon hi
  rw [rec_get hk, comp_u c1 ck, comp_u (cc c1 ck) c0, comp_u d1 ck, comp_u (cc d1 ck) d0,
    beq_id ck]
  have hk' := (PK.allN_iff.1 k_ker) k hk
  beta_reduce at hk'
  by_cases hA : ∃ e < HSU.NE.cnt, HSU.NE.T e =
      pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (HSU.REPI 1) (HSU.NE.T k)) (HSU.REP 1)
  · have hb : Nat.beq (Nat.land (r32 HSU.H (Nat.add (Nat.mul HSU.NE.cnt 1) k)) 1) 1 = true := by
      rw [(wconj_iff hk).1 hA]
      rfl
    have h := bif_t hb hk'
    rw [Bool.or_eq_true] at h
    rcases h with h1 | h2
    · rw [h1, Bool.or_true]
    · rw [found_false hT (cc (cc d1 ck) d0) (notIn_ne h2)]
      simp only [Bool.and_false, Bool.not_false, Bool.true_or]
  · rw [found_false hT (cc (cc c1 ck) c0) fun i hi e => hA ⟨i, hi, e⟩]
    simp only [Bool.false_and, Bool.not_false, Bool.true_or]

theorem k_e9s : penumHdK (pidn 100 7) EE.cnt 9 EE.T EE.PL = true ∧
    penumSlK 100 7 (mask 7) (100 * 7) false EE.G EE.GI EE.k EE.cnt EE.T EE.PL EE.POS EE.SRT EE.SRI 0
      9 = true ∧ Nat.beq EE.cnt 9 = true ∧
    allN 9 (fun i => allN 9 fun j => Nat.beq (pcomp 100 7 (mask 7) (EE.T i) (EE.T j))
      (pcomp 100 7 (mask 7) (EE.T j) (EE.T i))) = true ∧
    allN 9 (fun i => Nat.beq (pw 100 7 (EE.T i) 3) (pidn 100 7)) = true := by
  have h := k_e9
  unfold e9K at h
  simp only [Bool.and_eq_true] at h
  exact h

theorem ek : EE.k = 2 := rfl

theorem e_gens : GensOK 100 7 EE.k EE.G e9Gens := by
  refine ⟨by simp [e9Gens, e9Words, ek], fun j hj => ⟨?_, (PK.allN_iff.1 k_wds.2.2.2.2.2.2.2.2.2) j
    (by rw [ek] at hj; exact hj)⟩⟩
  rw [ek] at hj
  unfold e9Gens
  rw [map_get _ (by simpa [e9Words] using hj)]
  interval_cases j
  · exact wP_u k_wds.2.2.2.2.2.1
  · exact wP_u k_wds.2.2.2.2.2.2.2.1

theorem e9_ok : checkE9 e9Enum = true := by
  obtain ⟨hh, hsl, hc, hcm, hcu⟩ := k_e9s
  have hp : ∀ i < EE.cnt, penumPtK 100 7 (mask 7) (100 * 7) false EE.G EE.GI EE.k EE.cnt EE.T EE.PL
      EE.POS EE.SRT EE.SRI i = true :=
    fun i hi => penumSl_spec hsl i (Nat.zero_le _) (by exact hi) hi
  obtain ⟨e, hok⟩ := penumK_left_sound hn e_gens hh hp
  have ce : ∀ i < EE.cnt, Cn 100 7 (EE.T i) := fun i hi => (pt_spec (hp i hi)).1
  have hc' : EE.cnt = 9 := Nat.eq_of_beq_eq_true hc
  unfold checkE9 e9Enum
  rw [e, hok, rec_size]
  simp only [Bool.and_eq_true, Bool.true_and]
  refine ⟨⟨by rw [hc']; rfl, ?_⟩, ?_⟩
  · rw [allBelow_iff']
    intro i hi
    beta_reduce
    rw [allBelow_iff']
    intro j hj
    beta_reduce
    rw [rec_get hi, rec_get hj, comp_u (ce i hi) (ce j hj), comp_u (ce j hj) (ce i hi),
      eq_u (cc (ce i hi) (ce j hj)) (cc (ce j hj) (ce i hi))]
    rw [hc'] at hi hj
    exact (PK.allN_iff.1 ((PK.allN_iff.1 hcm) i hi)) j hj
  · rw [allBelow_iff']
    intro i hi
    beta_reduce
    rw [rec_get hi, beq_pw (ce i hi)]
    rw [hc'] at hi
    exact (PK.allN_iff.1 hcu) i hi

theorem k_uas : allN 5 (fun l => permOK 100 7 (mask 7) (100 * 7) (uaL l) (uaLI l)) = true ∧
    wordEqK 100 7 (mask 7) (pidn 100 7) uaL uaLI 5 uaXW (HSU.GP 0) = true ∧
    wordEqK 100 7 (mask 7) (pidn 100 7) uaL uaLI 5 uaYW (HSU.GP 1) = true := by
  have h := k_ua
  unfold uaK at h
  simp only [Bool.and_eq_true] at h
  exact h

theorem ua_bind : uaGens.size = 5 ∧ ∀ l < 5, uaGens[l]! = unpack 100 7 (uaL l) := by
  refine ⟨by simp [uaGens, uaWords], fun l hl => ?_⟩
  unfold uaGens
  rw [map_get _ (by simpa [uaWords] using hl)]
  interval_cases l
  · exact wP_u HSW0.k_all.2.2.2.2.2.2.1
  · exact wP_u HSW0.k_all.2.2.2.2.2.2.2.1
  · exact wP_u (HSP.hypsC.hNG 2 (by decide)).1
  · exact wP_u (HSP.hypsC.hNG 3 (by decide)).1
  · exact wP_u HSW0.k_all.2.2.1

theorem ua_ok : checkUA = true := by
  obtain ⟨hp, hx, hy⟩ := k_uas
  unfold checkUA
  rw [wordT_u ua_bind hp hx, wordT_u ua_bind hp hy, tabX_eq, tabY_eq,
    McLP.invsOK_of ua_bind (PK.allN_iff.1 hp)]
  simp only [beq_self_eq_true, Bool.and_self]

theorem hs_u35_check : check19852 = true := by
  unfold check19852
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, orders_ok⟩, ident_ok⟩, tcent_ok⟩, w_ok⟩, kernel_ok⟩, e9_ok⟩, ua_ok⟩
  rw [HSW0.checkInv_congr HSW0.pn HSW0.pg]
  exact c_checkInv_of HSP.hypsC

end CertificateChecks.KernelMaxD2.HSU35

end

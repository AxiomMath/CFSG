module

public import Certificates.Kernel.SporSch.PairHS.HS2272Facts
public import CFSG.Sporadic.SmallOddCore.HSCheckInputs
public import CFSG.Sporadic.SmallOddCore.TableFacts

public section

set_option maxRecDepth 4000

namespace CertificateChecks.KernelSporSch.HS72

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.HS2272 CFSG.KD.LQT.C4126
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Monster.B.Co2 Subgroup
open CertificateChecks.KernelSporSch

theorem oddL_mem {bs : List Nat} {L : Nat → Nat → Nat} :
    ∀ {ods : List (Nat × List (List Nat) × List (List Nat × Nat))}, oddL bs L ods = true →
      ∀ e ∈ ods, oddE bs L e = true
  | [], _, e, he => absurd he (List.not_mem_nil)
  | o :: ods, h, e, he => by
    have h' : Bool.rec (motive := fun _ => Bool) false (oddL bs L ods) (oddE bs L o) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rcases List.mem_cons.1 he with rfl | he
    · exact h1
    · exact oddL_mem h2 e he

theorem fact_eq {n p k m : Nat} (hp : p.Prime) (hn : n = p ^ k * m) (hm : ¬ p ∣ m) :
    n.factorization p = k := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  rw [hn, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hm]
  simp

section HS


theorem oddCore_rec {ri : Nat} (hri : ri < 4) {row : ClassRow}
    (hcg : row.centGens = (List.range (ncg ri)).map (fun j => hsCentTbl (cb ri + j)))
    (hprimes : ∀ p : Nat, p.Prime → p ≠ 2 → p ∣ cnto ri → ∃ e ∈ HSD.od.getD ri [], e.1 = p ∧
      (cnto ri).factorization p = e.2.1.length) :
    CFSG.oddCore ↥(hsP ⊓ centralizer ({T (rt ri)} : Set (Equiv.Perm (Fin 3850)))) = ⊥ := by
  have hNP : clsz ri * cnto ri = 44352000 := by
    have := cnto_vals
    have := clsz_vals
    interval_cases ri <;> simp_all
  obtain ⟨hC, hcard, -⟩ := rec_main hri hcg hNP
  set K := hsP ⊓ centralizer ({T (rt ri)} : Set (Equiv.Perm (Fin 3850)))
  have hKR : K ≤ hsR := inf_le_left.trans P_le_R
  have hg : ∀ k, gC ri k ∈ K := fun k => hC ▸ gC_memC hri hcg k
  have hL := fun k => LC_rep ri k hri
  have hi := gC_inv ri
  have hodd := oddL_mem (rec_parts hri).2.2.2.2.2
  refine oddCore_eq_bot_of_sylow K (WK K) (fun x hx => hx) fun p hp hp2 hdvd => ?_
  rw [hcard] at hdvd ⊢
  obtain ⟨e, he, hep, hfac⟩ := hprimes p hp hp2 hdvd
  have hE := hodd e he
  by_cases hlen : e.2.1.length = 1
  · obtain ⟨hord, hw⟩ := oddE_cyc hKR hL hi hg hE hlen (hep ▸ hp)
    set Y := wordVal (gC ri) (e.2.1.getD 0 [])
    refine ⟨zpowers Y, zpowers_le.2 (wordVal_mem hg _), ?_, fun y hy hy1 => ?_⟩
    · rw [Nat.card_zpowers, hord, hep, hfac, hlen, pow_one]
    · exact ⟨Y, hw, mem_zpowers_of_prime (hord ▸ hep ▸ hp) hy hy1⟩
  · obtain ⟨he3, o1, o2, hc, hnz, w1, w2, w3, w4⟩ := oddE_nine hKR hL hi hg hE hlen
    have hlen2 : e.2.1.length = 2 := by
      have h' := hE
      unfold oddE at h'
      have hb : Nat.beq e.2.1.length 1 = false := by
        cases e' : Nat.beq e.2.1.length 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e') hlen
      rw [hb] at h'
      exact Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 h').1
    obtain ⟨h9, hcov⟩ := closure_pair_nine o1 o2 hc hnz
    refine ⟨closure {wordVal (gC ri) (e.2.1.getD 0 []), wordVal (gC ri) (e.2.1.getD 1 [])},
      (closure_le _).2 ?_, ?_, fun y hy hy1 => ?_⟩
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact wordVal_mem hg _
      · exact wordVal_mem hg _
    · rw [h9, ← hep, he3]
      rw [← hep, he3] at hfac
      rw [hfac, hlen2]
      norm_num
    · obtain ⟨x, hx, hxy⟩ := hcov y hy hy1
      refine ⟨x, ?_, hxy⟩
      rcases hx with rfl | rfl | rfl | rfl
      · exact w1
      · exact w2
      · exact w3
      · exact w4

theorem permOK_T {k : Nat} (hk : k < 43) : permOK 3850 (hsCentTbl k) = true := by
  obtain ⟨h1, h2⟩ := invEqK_sound (allN_spec hc_perms k hk)
  unfold CFSG.Sporadic.SmallOddCore.permOK
  rw [hsCentTbl_eq hk, h1]
  exact h2

theorem rec_all {ri : Nat} (hri : ri < 4) {row : ClassRow}
    (hrep : row.rep = hsCentTbl (rt ri)) (hout : row.outer = decide (2 ≤ ri))
    (hcg : row.centGens = (List.range (ncg ri)).map (fun j => hsCentTbl (cb ri + j)))
    (hcs : row.classSize = clsz ri) (hco : row.centOrder = cnto ri)
    (hprimes : ∀ p : Nat, p.Prime → p ≠ 2 → p ∣ cnto ri → ∃ e ∈ HSD.od.getD ri [], e.1 = p ∧
      (cnto ri).factorization p = e.2.1.length) :
    permOK 3850 row.rep = true ∧ tp 3850 row.rep ∈ hsR ∧
      orderOf (tp 3850 row.rep) = 2 ∧ (row.outer = true ↔ tp 3850 row.rep ∉ hsP) ∧
      CFSG.Sporadic.SmallOddCore.hsC row =
        hsP ⊓ centralizer ({tp 3850 row.rep} : Set (Equiv.Perm (Fin 3850))) ∧
      Nat.card ↥(hsP ⊓ centralizer ({tp 3850 row.rep} : Set (Equiv.Perm (Fin 3850)))) =
        row.centOrder ∧
      (conjClass hsP (tp 3850 row.rep)).ncard = row.classSize ∧
      CFSG.oddCore ↥(hsP ⊓ centralizer ({tp 3850 row.rep} : Set (Equiv.Perm (Fin 3850)))) = ⊥ := by
  have hNP : clsz ri * cnto ri = 44352000 := by
    have := cnto_vals
    have := clsz_vals
    interval_cases ri <;> simp_all
  have ht : tp 3850 row.rep = T (rt ri) := by rw [hrep]
  obtain ⟨h1, h2, h3⟩ := rec_main hri hcg hNP
  rw [ht, hout, hcs, hco]
  exact ⟨hrep ▸ permOK_T (rt_lt ri hri), t_mem hri, t_ord hri, t_outer hri, h1, h2, h3,
    oddCore_rec hri hcg hprimes⟩

theorem row_of (r : Nat) (hr : r < 4) : ∃ row ∈ hsRows, row.rep = hsCentTbl (rt r) := by
  obtain ⟨e0, e1, e2, e3⟩ := rt_vals
  unfold hsRows
  interval_cases r
  · exact ⟨_, List.mem_cons_self, by rw [e0]⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [e1]⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by rw [e2]⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)), by rw [e3]⟩

theorem S_cover {s : Equiv.Perm (Fin 3850)} (hs : s ∈ hsS) (hs2 : orderOf s = 2) :
    ∃ r < 4, ∃ c ∈ hsP, c * s * c⁻¹ = T (rt r) := by
  obtain ⟨i, hi, rfl⟩ := S_enum s hs
  have hsR := S_le_R (eS_mem i)
  have hsq : eS i * eS i = 1 := by rw [← sq, ← hs2, pow_orderOf_eq_one]
  have hne : eS i ≠ 1 := fun h => by rw [h, orderOf_one] at hs2; exact absurd hs2 (by norm_num)
  have c1 : eqOnL bsR (fun x => wv LS (HSD.sw.getD i []) (wv LS (HSD.sw.getD i []) x))
      (fun x => x) = true :=
    eqOnL_of_eq bsR_lt ((eS_rep i).comp (eS_rep i)) (hsq ▸ RepF.one)
  have c2 : neL bsR (wv LS (HSD.sw.getD i [])) (fun x => x) = true := by
    unfold neL
    cases e : eqOnL bsR (wv LS (HSD.sw.getD i [])) (fun x => x)
    · rfl
    · exact absurd (eqR (eS_rep i) RepF.one hsR (one_mem _) e) hne
  obtain ⟨hr, hc⟩ := (s_parts hi).2.2 ⟨c1, c2⟩
  set c := HSD.sc.getD i (0, [])
  refine ⟨c.1, hr, wordVal gP c.2, wordVal_mem gP_mem _, ?_⟩
  have hrep := cjv_rep (fun k => LP_rep k) gP_inv (eS_rep i) c.2
  have hT := tR_rep (ri := c.1) hr
  exact eqR hrep hT (mul_mem (mul_mem (P_le_R (wordVal_mem gP_mem _)) hsR)
    (inv_mem (P_le_R (wordVal_mem gP_mem _)))) (t_mem hr) hc

theorem uc_conj {r : Nat} (hr : r < 4) :
    ∃ r' < 4, ∃ d ∈ hsP, d * (hsU * T (rt r) * hsU) * d⁻¹ = T (rt r') := by
  obtain ⟨-, -, h1, h2⟩ := data_parts hr
  set c := HSD.uc.getD r (0, [])
  refine ⟨c.1, h1, wordVal gP c.2, wordVal_mem gP_mem _, ?_⟩
  have hu : RepF 3850 (fun x => uP (tR r (uP x))) (hsU * T (rt r) * hsU) := by
    rw [mul_assoc]
    exact U_rep.comp ((tR_rep hr).comp U_rep)
  have hrep := cjv_rep (fun k => LP_rep k) gP_inv hu c.2
  have hd := P_le_R (wordVal_mem gP_mem c.2)
  exact eqR hrep (tR_rep h1) (mul_mem (mul_mem hd (mul_mem (mul_mem U_mem_R (t_mem hr))
    U_mem_R)) (inv_mem hd)) (t_mem h1) h2

theorem card_R : Nat.card hsR = 88704000 := by
  have := card_sup_zpowers U_sq' U_conj U_notMem
  rw [card_hsP] at this
  exact this

theorem R_cover {t : Equiv.Perm (Fin 3850)} (ht : t ∈ hsR) (ht2 : orderOf t = 2) :
    ∃ r < 4, ∃ g ∈ hsP, t = g * T (rt r) * g⁻¹ := by
  have hS : Nat.card hsS = 2 ^ (Nat.card hsR).factorization 2 := by
    rw [card_S, card_R, show (88704000 : Nat) = 2 ^ 10 * 86625 by norm_num,
      factorization_two_pow_mul (by norm_num)]
    norm_num
  obtain ⟨x, hx, hxs⟩ := exists_conj_mem_of_card S_le_R hS ht ht2
  have hs2 : orderOf (x⁻¹ * t * x) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj x⁻¹) t
    rw [MulAut.conj_apply, inv_inv] at this
    rw [this, ht2]
  obtain ⟨r, hr, c, hc, hcs⟩ := S_cover hxs hs2
  have ht' : t = (x * c⁻¹) * T (rt r) * (x * c⁻¹)⁻¹ := by
    rw [← hcs]
    group
  have hy : x * c⁻¹ ∈ hsR := mul_mem hx (inv_mem (P_le_R hc))
  rcases memR.1 hy with hyP | hyU
  · exact ⟨r, hr, _, hyP, ht'⟩
  · obtain ⟨r', hr', d, hd, hde⟩ := uc_conj hr
    refine ⟨r', hr', (x * c⁻¹ * hsU) * d⁻¹, mul_mem hyU (inv_mem hd), ?_⟩
    rw [ht', ← hde]
    have e1 : x * c⁻¹ = x * c⁻¹ * hsU * hsU := by rw [mul_assoc (x * c⁻¹), U_sq, mul_one]
    have e2 : hsU⁻¹ = hsU := U_inv
    calc x * c⁻¹ * T (rt r) * (x * c⁻¹)⁻¹
        = (x * c⁻¹ * hsU * hsU) * T (rt r) * (x * c⁻¹ * hsU * hsU)⁻¹ := by rw [← e1]
      _ = x * c⁻¹ * hsU * d⁻¹ * (d * (hsU * T (rt r) * hsU) * d⁻¹) *
            (x * c⁻¹ * hsU * d⁻¹)⁻¹ := by
          simp only [mul_inv_rev, e2]
          group

theorem allBlk_false {b : Nat} {f : Nat → Bool} :
    ∀ {len : Nat}, allBlk b f len = false → ∃ l < len, f (Nat.add b l) = false
  | 0, h => Bool.noConfusion h
  | len + 1, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) =
      false := h
    cases e : f (Nat.add b len)
    · exact ⟨len, Nat.lt_succ_self len, e⟩
    · rw [e] at h'
      obtain ⟨l, hl, hf⟩ := allBlk_false h'
      exact ⟨l, Nat.lt_succ_of_lt hl, hf⟩

theorem strong_mem {j : Nat} (hj : j < 8) : PHSCheck.g j ∈ hsP := by
  have hsc : hsChain.strongCount = 8 := by
    rw [hsChain, CFSG.Certificates.RawSchreierDatum.ofArrays_strongCount]
    simp [hsStrongArrs]
  have h := CFSG.Certificates.RawSchreierDatum.strong_get_mem_originalSubgroup hsChain
    hsChain_valid.1 ⟨j, hsc ▸ hj⟩
  rw [← hsP_eq_original, hsChain_strong_get] at h
  have e : hsStrongPerm j = PHSCheck.g j := by
    unfold hsStrongPerm PHSCheck.g
    rw [PHSCheck.arr_eq j hj]
  rwa [e] at h

theorem stab_parts : stabF 0 = true ∧ stabX = true := (bAnd_iff _ _).1 stab

theorem bIf_else {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true)
    (hc : c = false) : e = true := by
  subst hc
  exact h

theorem stabF_spec {x : Nat} (h : stabF x = true) :
    ∀ j < 6, pg 12 (mask 12) (PHSC.S (j + 2)) x = x := by
  intro j hj
  have h' : allBlk 0 (fun j => Nat.beq (pg 12 (mask 12) (PHSC.S (Nat.add j 2)) x) x) 6 = true := h
  have := allBlk_spec h' j hj
  rw [show Nat.add 0 j = j from Nat.zero_add j] at this
  exact Nat.eq_of_beq_eq_true this

theorem stabF_false {x : Nat} (h : stabF x = false) :
    ∃ j < 6, pg 12 (mask 12) (PHSC.S (j + 2)) x ≠ x := by
  have h' : allBlk 0 (fun j => Nat.beq (pg 12 (mask 12) (PHSC.S (Nat.add j 2)) x) x) 6 = false := h
  obtain ⟨j, hj, hf⟩ := allBlk_false h'
  rw [show Nat.add 0 j = j from Nat.zero_add j] at hf
  refine ⟨j, hj, fun e => ?_⟩
  have : Nat.beq (pg 12 (mask 12) (PHSC.S (j + 2)) x) x = true := Nat.beq_eq.mpr e
  rw [show Nat.beq (pg 12 (mask 12) (PHSC.S (Nat.add j 2)) x) x =
    Nat.beq (pg 12 (mask 12) (PHSC.S (j + 2)) x) x from rfl, this] at hf
  exact Bool.noConfusion hf

theorem hs_stab_facts : ∀ x : Fin 3850, x ≠ 0 → ∃ s ∈ hsP, s 0 = 0 ∧ s x ≠ x := by
  obtain ⟨h1, h2⟩ := stab_parts
  intro x hx
  have hx0 : Nat.beq x.val 0 = false := by
    cases e : Nat.beq x.val 0
    · rfl
    · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true e)) hx
  have h3 : bIf(Nat.beq x.val 0, true, bIf(stabF x.val, false, true)) = true :=
    allN_spec h2 x.val x.2
  have h4 : stabF x.val = false := by
    have h5 := bIf_else h3 hx0
    cases e : stabF x.val
    · rfl
    · rw [e] at h5
      exact Bool.noConfusion h5
  obtain ⟨j, hj, hjx⟩ := stabF_false h4
  have h0 := stabF_spec h1 j hj
  have hrep := repF_unpack (PHSCheck.rep_g (j + 2) (by omega)).1
  have e0 : pg 12 (mask 12) (PHSC.S (j + 2)) 0 =
      ((PHSCheck.g (j + 2)) ⟨0, by norm_num⟩ : Nat) := hrep 0 (by norm_num)
  have e1 : pg 12 (mask 12) (PHSC.S (j + 2)) x.val =
      ((PHSCheck.g (j + 2)) ⟨x.val, x.isLt⟩ : Nat) := hrep x.val x.isLt
  rw [Fin.eta] at e1
  have hz : (0 : Fin 3850) = ⟨0, by norm_num⟩ := rfl
  refine ⟨PHSCheck.g (j + 2), strong_mem (by omega), ?_, fun he => hjx ?_⟩
  · rw [hz]
    exact Fin.ext (e0.symm.trans h0)
  · rw [e1, he]

theorem rep_a_ok : (permOK 3850 (hsCentTbl 5) &&
    CFSG.Sporadic.Schreier.Native.tblEq 3850 (hsCentTbl 5) hsPGTbls[0]!) = true := by
  have hp := permOK_T (k := 5) (by norm_num)
  rw [hp, Bool.true_and]
  have hT : T 5 = hsGen 0 := by
    rw [T_eq (by norm_num), Nat.eq_of_beq_eq_true rep_a]
    change _ = permOfArr 3850 hsStrongArrs[0]!
    rw [PHSCheck.arr_eq 0 (by norm_num)]
  have hr : CFSG.Sporadic.Th.Rep 3850 hsPGTbls[0]! (hsGen 0) := by
    rw [show hsPGTbls[0]! = hsStrongArrs[0]!.map UInt32.ofNat by simp [hsPGTbls]]
    exact rep_arrayMap_ofNat (by norm_num) (rep_hsStrongPerm (by norm_num))
  rw [tblEq_iff_eq (rep_tp hp) hr]
  exact hT

theorem wd_facts : ∃ x ∈ hsP ⊓ centralizer ({tp 3850 (hsCentTbl 34)} : Set (Equiv.Perm (Fin 3850))),
    orderOf x = 5 ∧
    ∃ y ∈ hsP ⊓ centralizer ({tp 3850 (hsCentTbl 34)} : Set (Equiv.Perm (Fin 3850))),
      orderOf (x * (y * x * y⁻¹)) = 6 := by
  have e3 : rt 3 = 34 := rt_vals.2.2.2
  have hT : tp 3850 (hsCentTbl 34) = T (rt 3) := by rw [e3]
  rw [hT]
  set K := hsP ⊓ centralizer ({T (rt 3)} : Set (Equiv.Perm (Fin 3850)))
  have hg : ∀ k, gC 3 k ∈ K := gC_memK (by norm_num)
  have hKR : K ≤ hsR := inf_le_left.trans P_le_R
  have h := wd_ok
  unfold wdB at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hL := fun k => LC_rep 3 k (by norm_num)
  have hx := wordVal_mem hg (HSD.wd.getD 0 [])
  have hy := wordVal_mem hg (HSD.wd.getD 1 [])
  refine ⟨_, hx, (ordPL_iff faithR bsR_lt (wv_rep hL _) (hKR hx) (by norm_num)).1 h1, _, hy,
    ord6L_spec faithR bsR_lt (conjProd_rep hL (gC_inv 3) _ _)
      (hKR (mul_mem hx (mul_mem (mul_mem hy hx) (inv_mem hy)))) h2⟩

theorem od_shape : (HSD.od.getD 0 []).map (fun e => (e.1, e.2.1.length)) = [(3, 1), (5, 1)] ∧
    (HSD.od.getD 1 []).map (fun e => (e.1, e.2.1.length)) = [(3, 2), (5, 1)] ∧
    (HSD.od.getD 2 []).map (fun e => (e.1, e.2.1.length)) = [(3, 2), (5, 1), (7, 1)] ∧
    (HSD.od.getD 3 []).map (fun e => (e.1, e.2.1.length)) = [(3, 1), (5, 1)] := by
  decide +kernel

theorem primes_of {ri : Nat} {fs : List (Nat × Nat)} (hfs : ∀ f ∈ fs, f.1.Prime)
    (hc : cnto ri = (fs.map fun f => f.1 ^ f.2).prod)
    (hod : ∀ f ∈ fs, f.1 ≠ 2 → ∃ e ∈ HSD.od.getD ri [], e.1 = f.1 ∧
      (cnto ri).factorization f.1 = e.2.1.length) :
    ∀ p : Nat, p.Prime → p ≠ 2 → p ∣ cnto ri → ∃ e ∈ HSD.od.getD ri [], e.1 = p ∧
      (cnto ri).factorization p = e.2.1.length := by
  intro p hp hp2 hdvd
  rw [hc] at hdvd
  obtain ⟨f, hf, rfl⟩ := eq_of_prime_dvd_prod hp fs hfs hdvd
  exact hod f hf hp2

theorem od_entry {ri : Nat} (p k : Nat) (h : (p, k) ∈ (HSD.od.getD ri []).map
    (fun e => (e.1, e.2.1.length))) (hf : (cnto ri).factorization p = k) :
    ∃ e ∈ HSD.od.getD ri [], e.1 = p ∧ (cnto ri).factorization p = e.2.1.length := by
  obtain ⟨e, he, hek⟩ := List.mem_map.1 h
  simp only [Prod.mk.injEq] at hek
  exact ⟨e, he, hek.1, by rw [hf, hek.2]⟩

theorem primes_all : ∀ ri < 4, ∀ p : Nat, p.Prime → p ≠ 2 → p ∣ cnto ri →
    ∃ e ∈ HSD.od.getD ri [], e.1 = p ∧ (cnto ri).factorization p = e.2.1.length := by
  obtain ⟨c0, c1, c2, c3⟩ := cnto_vals
  obtain ⟨o0, o1, o2, o3⟩ := od_shape
  have p7 : Nat.Prime 7 := by norm_num
  intro ri hri
  interval_cases ri
  · have f3 : (cnto 0).factorization 3 = 1 := by
      rw [c0]
      exact fact_eq Nat.prime_three (show 7680 = 3 ^ 1 * 2560 by norm_num) (by norm_num)
    have f5 : (cnto 0).factorization 5 = 1 := by
      rw [c0]
      exact fact_eq Nat.prime_five (show 7680 = 5 ^ 1 * 1536 by norm_num) (by norm_num)
    refine primes_of (fs := [(2, 9), (3, 1), (5, 1)]) (by decide) (by rw [c0]; norm_num) ?_
    intro f hf hf2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact absurd rfl hf2
    · exact od_entry 3 1 (by rw [o0]; simp) f3
    · exact od_entry 5 1 (by rw [o0]; simp) f5
  · have f3 : (cnto 1).factorization 3 = 2 := by
      rw [c1]
      exact fact_eq Nat.prime_three (show 2880 = 3 ^ 2 * 320 by norm_num) (by norm_num)
    have f5 : (cnto 1).factorization 5 = 1 := by
      rw [c1]
      exact fact_eq Nat.prime_five (show 2880 = 5 ^ 1 * 576 by norm_num) (by norm_num)
    refine primes_of (fs := [(2, 6), (3, 2), (5, 1)]) (by decide) (by rw [c1]; norm_num) ?_
    intro f hf hf2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact absurd rfl hf2
    · exact od_entry 3 2 (by rw [o1]; simp) f3
    · exact od_entry 5 1 (by rw [o1]; simp) f5
  · have f3 : (cnto 2).factorization 3 = 2 := by
      rw [c2]
      exact fact_eq Nat.prime_three (show 40320 = 3 ^ 2 * 4480 by norm_num) (by norm_num)
    have f5 : (cnto 2).factorization 5 = 1 := by
      rw [c2]
      exact fact_eq Nat.prime_five (show 40320 = 5 ^ 1 * 8064 by norm_num) (by norm_num)
    have f7 : (cnto 2).factorization 7 = 1 := by
      rw [c2]
      exact fact_eq p7 (show 40320 = 7 ^ 1 * 5760 by norm_num) (by norm_num)
    refine primes_of (fs := [(2, 7), (3, 2), (5, 1), (7, 1)]) (by decide) (by rw [c2]; norm_num) ?_
    intro f hf hf2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact absurd rfl hf2
    · exact od_entry 3 2 (by rw [o2]; simp) f3
    · exact od_entry 5 1 (by rw [o2]; simp) f5
    · exact od_entry 7 1 (by rw [o2]; simp) f7
  · have f3 : (cnto 3).factorization 3 = 1 := by
      rw [c3]
      exact fact_eq Nat.prime_three (show 1920 = 3 ^ 1 * 640 by norm_num) (by norm_num)
    have f5 : (cnto 3).factorization 5 = 1 := by
      rw [c3]
      exact fact_eq Nat.prime_five (show 1920 = 5 ^ 1 * 384 by norm_num) (by norm_num)
    refine primes_of (fs := [(2, 7), (3, 1), (5, 1)]) (by decide) (by rw [c3]; norm_num) ?_
    intro f hf hf2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact absurd rfl hf2
    · exact od_entry 3 1 (by rw [o3]; simp) f3
    · exact od_entry 5 1 (by rw [o3]; simp) f5

theorem rows_all : ∀ r ∈ hsRows, permOK 3850 r.rep = true ∧ tp 3850 r.rep ∈ hsR ∧
    orderOf (tp 3850 r.rep) = 2 ∧ (r.outer = true ↔ tp 3850 r.rep ∉ hsP) ∧
    CFSG.Sporadic.SmallOddCore.hsC r = hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) ∧
    Nat.card ↥(hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) = r.centOrder ∧
    (conjClass hsP (tp 3850 r.rep)).ncard = r.classSize ∧
    CFSG.oddCore ↥(hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) = ⊥ := by
  obtain ⟨t0, t1, t2, t3⟩ := rt_vals
  obtain ⟨b0, b1, b2, b3⟩ := cb_vals
  obtain ⟨n0, n1, n2, n3⟩ := ncg_vals
  obtain ⟨s0, s1, s2, s3⟩ := clsz_vals
  obtain ⟨o0, o1, o2, o3⟩ := cnto_vals
  intro r hr
  unfold hsRows at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact rec_all (ri := 0) (by norm_num) (by rw [t0]) (by decide)
      (by rw [n0, b0]; simp [List.range_succ]) (by rw [s0]) (by rw [o0])
      (primes_all 0 (by norm_num))
  · exact rec_all (ri := 1) (by norm_num) (by rw [t1]) (by decide)
      (by rw [n1, b1]; simp [List.range_succ]) (by rw [s1]) (by rw [o1])
      (primes_all 1 (by norm_num))
  · exact rec_all (ri := 2) (by norm_num) (by rw [t2]) (by decide)
      (by rw [n2, b2]; simp [List.range_succ]) (by rw [s2]) (by rw [o2])
      (primes_all 2 (by norm_num))
  · exact rec_all (ri := 3) (by norm_num) (by rw [t3]) (by decide)
      (by rw [n3, b3]; simp [List.range_succ]) (by rw [s3]) (by rw [o3])
      (primes_all 3 (by norm_num))

theorem cover_all : ∀ t ∈ hsR, orderOf t = 2 →
    ∃ r ∈ hsRows, ∃ g ∈ hsP, t = g * tp 3850 r.rep * g⁻¹ := by
  intro t ht ht2
  obtain ⟨r, hr, g, hg, e⟩ := R_cover ht ht2
  obtain ⟨row, hrow, hrep⟩ := row_of r hr
  exact ⟨row, hrow, g, hg, by rw [hrep]; exact e⟩

theorem facts2272 : (∀ x : Fin 3850, x ≠ 0 → ∃ s ∈ hsP, s 0 = 0 ∧ s x ≠ x)
    ∧ ((permOK 3850 (hsCentTbl 5) &&
      CFSG.Sporadic.Schreier.Native.tblEq 3850 (hsCentTbl 5) hsPGTbls[0]!) = true)
    ∧ (hsU ^ 2 = 1 ∧ hsU ≠ 1 ∧ hsU ∉ hsP ∧ ∀ p ∈ hsP, hsU * p * hsU⁻¹ ∈ hsP)
    ∧ (∀ r ∈ hsRows, permOK 3850 r.rep = true ∧ tp 3850 r.rep ∈ hsR ∧
        orderOf (tp 3850 r.rep) = 2 ∧ (r.outer = true ↔ tp 3850 r.rep ∉ hsP) ∧
        CFSG.Sporadic.SmallOddCore.hsC r =
          hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) ∧
        Nat.card ↥(hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) =
          r.centOrder ∧
        (conjClass hsP (tp 3850 r.rep)).ncard = r.classSize ∧
        CFSG.oddCore ↥(hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) = ⊥)
    ∧ (hsS ≤ hsR ∧ Nat.card hsS = 1024)
    ∧ (∀ t ∈ hsR, orderOf t = 2 → ∃ r ∈ hsRows, ∃ g ∈ hsP, t = g * tp 3850 r.rep * g⁻¹)
    ∧ (∃ x ∈ hsP ⊓ centralizer ({tp 3850 (hsCentTbl 34)} : Set (Equiv.Perm (Fin 3850))),
        orderOf x = 5 ∧
        ∃ y ∈ hsP ⊓ centralizer ({tp 3850 (hsCentTbl 34)} : Set (Equiv.Perm (Fin 3850))),
          orderOf (x * (y * x * y⁻¹)) = 6) :=
  ⟨hs_stab_facts, rep_a_ok, ⟨U_sq', U_ne, U_notMem, U_conj⟩, rows_all, ⟨S_le_R, card_S⟩,
    cover_all, wd_facts⟩

end HS

end CertificateChecks.KernelSporSch.HS72

end

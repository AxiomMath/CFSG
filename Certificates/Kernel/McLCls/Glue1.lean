module

public import Certificates.Kernel.McLCls.Checks
public import Certificates.Kernel.McLCls.Enum
public import Certificates.Kernel.McLAS.Glue
public import Certificates.Data.McLClsFacts
public import CFSG.Sporadic.SmallOddCore.McLLocal
public import CFSG.Certificates.Kernel.ListBridge.PackSound
public import CFSG.Quasithin.Vol2.KGFactC31WordBasis

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLCls

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.M305
  CertificateChecks.KernelLC.McLC CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.Quasithin.KGC31
  CFSG.SectionRank.QTK.Insp443.McLCls CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore.Native CFSG.KS.MulH

theorem band {a b : Bool} : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> simp

theorem bif_iff {a b c : Bool} : bIf(a, b, c) = true ↔ (a = true ∧ b = true) ∨ (a = false ∧ c = true) := by
  cases a <;> simp

theorem prep_eq {P : Nat} {g h : Equiv.Perm (Fin 275)} (hg : PRep 275 9 P g)
    (hh : PRep 275 9 P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem eq_of_beq {P Q : Nat} {g h : Equiv.Perm (Fin 275)} (hP : PRep 275 9 P g)
    (hQ : PRep 275 9 Q h) (e : Nat.beq P Q = true) : g = h := by
  rw [Nat.eq_of_beq_eq_true e] at hP
  exact prep_eq hP hQ

theorem prep_mul {P Q : Nat} {g h : Equiv.Perm (Fin 275)} (hP : PRep 275 9 P g)
    (hQ : PRep 275 9 Q h) : PRep 275 9 (m305mul P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

theorem prep_one : PRep 275 9 m305id 1 := prep_pidn (by norm_num) (by norm_num)

theorem canon_mul {P Q : Nat} (hP : canonK 275 9 (mask 9) (275 * 9) P = true)
    (hQ : canonK 275 9 (mask 9) (275 * 9) Q = true) :
    canonK 275 9 (mask 9) (275 * 9) (m305mul P Q) = true :=
  CFSG.KC.BfsPin.canonK_pcomp hP hQ

theorem canon_one : canonK 275 9 (mask 9) (275 * 9) m305id = true := by
  decide +kernel

theorem ne_of_beq {P Q : Nat} {g h : Equiv.Perm (Fin 275)}
    (cP : canonK 275 9 (mask 9) (275 * 9) P = true) (cQ : canonK 275 9 (mask 9) (275 * 9) Q = true)
    (hP : PRep 275 9 P g) (hQ : PRep 275 9 Q h) (e : Nat.beq P Q = false) : g ≠ h := by
  rintro rfl
  have := CFSG.ClassicalInvolution.ListBridge.eq_of_prep cP cQ hP hQ
  rw [this, Nat.beq_refl] at e
  exact Bool.noConfusion e

theorem prep_word {S : Nat → Nat} {gs : Nat → Equiv.Perm (Fin 275)}
    (hS : ∀ j, PRep 275 9 (S j) (gs j)) : ∀ wd : List Nat,
      PRep 275 9 (m305word S wd) (wd.map gs).prod
  | [] => prep_one
  | j :: wd => by
    have e : m305word S (j :: wd) = m305mul (S j) (m305word S wd) := by
      change strictN (m305word S wd) (fun acc => pcomp 275 9 (mask 9) (S j) acc) = _
      rw [CFSG.KS.PEnum.strictN_app']
      rfl
    rw [e, List.map_cons, List.prod_cons]
    exact prep_mul (hS j) (prep_word hS wd)

theorem prep_prod : ∀ {bs : List Nat} {vs : List (Equiv.Perm (Fin 275))},
    List.Forall₂ (PRep 275 9) bs vs → ∀ c : Nat,
      PRep 275 9 (m305prod bs c) (eElt (fun i : Fin vs.length => vs[i]) (bitVec vs.length c))
  | [], [], _, c => by
    have e : ∀ (f : Fin ([] : List (Equiv.Perm (Fin 275))).length → Equiv.Perm (Fin 275))
        (d : Fin ([] : List (Equiv.Perm (Fin 275))).length → ZMod 2), eElt f d = 1 := by
      intro f d
      simp [eElt]
    rw [e]
    exact prep_one
  | b :: bs, v :: vs, h, c => by
    obtain ⟨hb, h⟩ := List.forall₂_cons.mp h
    have ih := prep_prod h (c / 2)
    change PRep 275 9 (m305prod (b :: bs) c) (eElt (n := vs.length + 1)
      (fun i => (v :: vs)[i]) (bitVec (vs.length + 1) c))
    rw [eElt_succ, bitVec_succ, bitVec_zero]
    have e2 : (fun i : Fin vs.length => (v :: vs)[(i.succ : Fin (vs.length + 1))]) =
        fun i => vs[i] := by
      funext i
      rfl
    rw [e2]
    change PRep 275 9 _
      (v ^ ((c % 2 : ℕ) : ZMod 2).val * eElt (fun i => vs[i]) (bitVec vs.length (c / 2)))
    have hval : ((c % 2 : ℕ) : ZMod 2).val = c % 2 := ZMod.val_cast_of_lt (Nat.mod_lt _ (by norm_num))
    rw [hval]
    have hc : c / 2 = Nat.div c 2 := rfl
    change PRep 275 9 (Bool.rec (motive := fun _ => Nat) (m305prod bs (Nat.div c 2))
      (m305mul b (m305prod bs (Nat.div c 2))) (Nat.beq (Nat.mod c 2) 1)) _
    rw [← hc]
    rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
    · have : Nat.beq (Nat.mod c 2) 1 = false := by
        change Nat.beq (c % 2) 1 = false
        rw [h0]
        rfl
      rw [this, h0, pow_zero, one_mul]
      exact ih
    · have : Nat.beq (Nat.mod c 2) 1 = true := by
        change Nat.beq (c % 2) 1 = true
        rw [h1]
        rfl
      rw [this, h1, pow_one]
      exact prep_mul hb ih

theorem perm_parts : allN 9 (fun k => pOK (CT.F k) (CI k)) = true ∧ pOK (MC.F 0) (MI 0) = true ∧
    pOK (MC.F 4) (MI 1) = true ∧ pOK (MC.F 5) (MI 2) = true ∧ pOK (MC.F 6) (MI 3) = true := by
  have h := perms
  simp only [band] at h
  exact h

theorem pOK_parts {p q : Nat} (h : pOK p q = true) : canonK 275 9 (mask 9) (275 * 9) p = true ∧
    invEqK 275 9 (mask 9) (275 * 9) p q = true := by
  unfold pOK at h
  simp only [band] at h
  exact ⟨h.1, h.2.2⟩

theorem permOK_tbl {T : Table} {X XI : Nat}
    (hT : CFSG.Sporadic.SmallOddCore.Native.natArr T = unpack 275 9 X)
    (h : invEqK 275 9 (mask 9) (275 * 9) X XI = true) :
    CFSG.Sporadic.SmallOddCore.permOK 275 T = true := by
  obtain ⟨h1, h2⟩ := invEqK_sound h
  unfold CFSG.Sporadic.SmallOddCore.permOK
  rw [hT, h1]
  exact h2

theorem prep_tbl {T : Table} {X XI : Nat}
    (hT : CFSG.Sporadic.SmallOddCore.Native.natArr T = unpack 275 9 X)
    (h : invEqK 275 9 (mask 9) (275 * 9) X XI = true) : PRep 275 9 X (tp 275 T) := by
  intro x
  have r := rep_tp (permOK_tbl hT h) x x.2
  rw [← unpack_get x.2, ← hT, natArr_getElem!, r, idx_of_lt _ x.2]
  rfl

theorem cls_pOK {k : Nat} (hk : k < 9) : pOK (CT.F k) (CI k) = true :=
  CFSG.KS.Raw.Orb.allN_iff.1 perm_parts.1 k hk

theorem prep_cls {k : Nat} (hk : k < 9) : PRep 275 9 (CT.F k) (tp 275 (clsTbl k)) :=
  prep_tbl (clsTbl_eq hk) (pOK_parts (cls_pOK hk)).2

theorem canon_cls {k : Nat} (hk : k < 9) : canonK 275 9 (mask 9) (275 * 9) (CT.F k) = true :=
  (pOK_parts (cls_pOK hk)).1

theorem prep_cen0 : PRep 275 9 (MC.F 0) (tp 275 (mclCentTbl 0)) :=
  prep_tbl (natArr_cent 0 (by norm_num)) (pOK_parts perm_parts.2.1).2

theorem prep_cen4 : PRep 275 9 (MC.F 4) (tp 275 (mclCentTbl 4)) :=
  prep_tbl (natArr_cent 4 (by norm_num)) (pOK_parts perm_parts.2.2.1).2

theorem prep_cen5 : PRep 275 9 (MC.F 5) (tp 275 (mclCentTbl 5)) :=
  prep_tbl (natArr_cent 5 (by norm_num)) (pOK_parts perm_parts.2.2.2.1).2

theorem prep_cen6 : PRep 275 9 (MC.F 6) (tp 275 (mclCentTbl 6)) :=
  prep_tbl (natArr_cent 6 (by norm_num)) (pOK_parts perm_parts.2.2.2.2).2

theorem canon_cen4 : canonK 275 9 (mask 9) (275 * 9) (MC.F 4) = true :=
  (pOK_parts perm_parts.2.2.1).1

@[expose] noncomputable def gH (j : Nat) : Equiv.Perm (Fin 275) :=
  Nat.rec (motive := fun _ => Equiv.Perm (Fin 275)) (tp 275 (mclCentTbl 5))
    (fun _ _ => tp 275 (mclCentTbl 6)) j

theorem prep_hL (j : Nat) : PRep 275 9 (hL j) (gH j) := by
  cases j
  · exact prep_cen5
  · exact prep_cen6

theorem c56_mem (j : Nat) : gH j ∈ F.H := by
  have h := mclT0_facts.2.2.1
  change gH j ∈ mclCt
  rw [← h]
  apply Subgroup.subset_closure
  cases j
  · exact ⟨mclCentTbl 5, by simp, rfl⟩
  · exact ⟨mclCentTbl 6, by simp, rfl⟩

theorem word_mem (wd : List Nat) : (wd.map gH).prod ∈ F.H :=
  F.H.list_prod_mem fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    exact c56_mem j

end CertificateChecks.KernelMcLCls

namespace CertificateChecks.KernelMcLCls

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.M305
  CertificateChecks.KernelLC.McLC CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.Quasithin.KGC31
  CFSG.SectionRank.QTK.Insp443.McLCls CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore.Native CFSG.KS.MulH

theorem m305all_iff {f : Nat → Bool} : ∀ L : List Nat, m305all f L = true ↔ ∀ x ∈ L, f x = true
  | [] => ⟨fun _ x hx => absurd hx List.not_mem_nil, fun _ => rfl⟩
  | x :: L => by
    change bAnd(f x, m305all f L) = true ↔ _
    rw [band, m305all_iff L]
    simp

theorem natRec_and {f : Nat → Bool} : ∀ N : Nat,
    Nat.rec (motive := fun _ => Bool) true (fun c acc => bAnd(f c, acc)) N = true ↔
      ∀ c < N, f c = true
  | 0 => ⟨fun _ c hc => absurd hc (Nat.not_lt_zero c), fun _ => rfl⟩
  | N + 1 => by
    change bAnd(f N, Nat.rec (motive := fun _ => Bool) true (fun c acc => bAnd(f c, acc)) N) =
      true ↔ _
    rw [band, natRec_and N]
    constructor
    · rintro ⟨h1, h2⟩ c hc
      rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
      · exact h2 c hc
      · exact h1
    · intro h
      exact ⟨h N (Nat.lt_succ_self N), fun c hc => h c (Nat.lt_succ_of_lt hc)⟩

theorem words_forall₂ {S : Nat → Nat} : ∀ {wds : List (List Nat)} {Ts : List Nat},
    m305words S wds Ts = true → List.Forall₂ (fun wd T => Nat.beq (m305word S wd) T = true) wds Ts
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | wd :: wds, T :: Ts, h => by
    change bAnd(Nat.beq (m305word S wd) T, m305words S wds Ts) = true at h
    rw [band] at h
    exact List.Forall₂.cons h.1 (words_forall₂ h.2)

theorem canon_prod : ∀ {bs : List Nat}, (∀ b ∈ bs, canonK 275 9 (mask 9) (275 * 9) b = true) →
    ∀ c, canonK 275 9 (mask 9) (275 * 9) (m305prod bs c) = true
  | [], _, _ => canon_one
  | b :: bs, h, c => by
    have ih := canon_prod (bs := bs) (fun x hx => h x (List.mem_cons_of_mem b hx)) (Nat.div c 2)
    change canonK 275 9 (mask 9) (275 * 9) (Bool.rec (motive := fun _ => Nat)
      (m305prod bs (Nat.div c 2)) (m305mul b (m305prod bs (Nat.div c 2)))
      (Nat.beq (Nat.mod c 2) 1)) = true
    cases Nat.beq (Nat.mod c 2) 1
    · exact ih
    · exact canon_mul (h b List.mem_cons_self) ih

theorem rep_cls {k : Nat} (hk : k < 9) : Rep 275 (clsTbl k) (tp 275 (clsTbl k)) :=
  rep_tp (permOK_tbl (clsTbl_eq hk) (pOK_parts (cls_pOK hk)).2)

theorem rep_cen {k : Nat} (hk : k < 22) {XI : Nat}
    (h : invEqK 275 9 (mask 9) (275 * 9) (MC.F k) XI = true) :
    Rep 275 (mclCentTbl k) (tp 275 (mclCentTbl k)) :=
  rep_tp (permOK_tbl (natArr_cent k hk) h)

theorem words_H : tp 275 (mclCentTbl 4) ∈ F.H ∧ tp 275 (clsTbl 0) ∈ F.H ∧
    tp 275 (clsTbl 1) ∈ F.H ∧ tp 275 (clsTbl 2) ∈ F.H ∧ tp 275 (clsTbl 6) ∈ F.H ∧
    tp 275 (clsTbl 7) ∈ F.H ∧ tp 275 (clsTbl 8) ∈ F.H := by
  have h := words_forall₂ hWords
  unfold hWd hTb at h
  obtain ⟨h0, h⟩ := List.forall₂_cons.mp h
  obtain ⟨h1, h⟩ := List.forall₂_cons.mp h
  obtain ⟨h2, h⟩ := List.forall₂_cons.mp h
  obtain ⟨h3, h⟩ := List.forall₂_cons.mp h
  obtain ⟨h4, h⟩ := List.forall₂_cons.mp h
  obtain ⟨h5, h⟩ := List.forall₂_cons.mp h
  obtain ⟨h6, -⟩ := List.forall₂_cons.mp h
  have m := fun wd => word_mem (wd := wd)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← eq_of_beq (prep_word prep_hL _) prep_cen4 h0]
    exact m _
  · rw [← eq_of_beq (prep_word prep_hL _) (prep_cls (k := 0) (by norm_num)) h1]
    exact m _
  · rw [← eq_of_beq (prep_word prep_hL _) (prep_cls (k := 1) (by norm_num)) h2]
    exact m _
  · rw [← eq_of_beq (prep_word prep_hL _) (prep_cls (k := 2) (by norm_num)) h3]
    exact m _
  · rw [← eq_of_beq (prep_word prep_hL _) (prep_cls (k := 6) (by norm_num)) h4]
    exact m _
  · rw [← eq_of_beq (prep_word prep_hL _) (prep_cls (k := 7) (by norm_num)) h5]
    exact m _
  · rw [← eq_of_beq (prep_word prep_hL _) (prep_cls (k := 8) (by norm_num)) h6]
    exact m _

theorem sift_mem {k : Nat} (hk : k < 9) (h : siftC (CT.F k) = true) : tp 275 (clsTbl k) ∈ mclP := by
  have e1 : clsTbl k = tabT (unpack 275 9 (CT.F k)) := by
    rw [← clsTbl_eq hk, CFSG.KS.MulH.tabT_natArr]
  have hs : mclSift (clsTbl k) = true := by
    rw [e1, CertificateChecks.KernelMcLAS.sift_eq (canon_cls hk)]
    exact h
  exact (mcl_groupData.sift _ _ (rep_cls hk)).mp hs

theorem tbls_fact : (∀ T ∈ allTbls, Rep 275 T (tp 275 T) ∧ tp 275 T ∈ mclP) ∧
    Rep 275 mclOuterTbl mclU := by
  have hH : F.H ≤ mclP := inf_le_left
  obtain ⟨w0, w1, w2, w3, w4, w5, w6⟩ := words_H
  refine ⟨fun T hT => ?_, rep_cen (by norm_num) (pOK_parts perm_parts.2.1).2⟩
  simp only [allTbls, eB, gT, mGens, sGens, cGens, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rep_cen (by norm_num) (pOK_parts perm_parts.2.2.1).2, hH w0⟩
  · exact ⟨rep_cls (by norm_num), hH w1⟩
  · exact ⟨rep_cls (by norm_num), hH w2⟩
  · exact ⟨rep_cls (by norm_num), hH w3⟩
  · exact ⟨rep_cls (by norm_num), sift_mem (by norm_num) sift0⟩
  · exact ⟨rep_cls (by norm_num), sift_mem (by norm_num) sift1⟩
  · exact ⟨rep_cls (by norm_num), sift_mem (by norm_num) sift2⟩
  · exact ⟨rep_cls (by norm_num), hH w4⟩
  · exact ⟨rep_cls (by norm_num), hH w5⟩
  · exact ⟨rep_cls (by norm_num), hH w6⟩
  · exact ⟨rep_cen (by norm_num) (pOK_parts perm_parts.2.2.2.1).2, hH (c56_mem 0)⟩
  · exact ⟨rep_cen (by norm_num) (pOK_parts perm_parts.2.2.2.2).2, hH (c56_mem 1)⟩

end CertificateChecks.KernelMcLCls

namespace CertificateChecks.KernelMcLCls

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.M305
  CertificateChecks.KernelLC.McLC CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.Quasithin.KGC31
  CFSG.SectionRank.QTK.Insp443.McLCls CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore.Native CFSG.KS.MulH

@[expose] noncomputable def vs : List (Equiv.Perm (Fin 275)) :=
  [tp 275 (mclCentTbl 4), tp 275 (clsTbl 0), tp 275 (clsTbl 1), tp 275 (clsTbl 2)]

theorem bs_vs : List.Forall₂ (PRep 275 9) bs vs :=
  List.Forall₂.cons prep_cen4 (List.Forall₂.cons (prep_cls (by norm_num))
    (List.Forall₂.cons (prep_cls (by norm_num)) (List.Forall₂.cons (prep_cls (by norm_num))
      List.Forall₂.nil)))

theorem v_eq : F.v = fun i : Fin 4 => vs[i] := by
  funext i
  fin_cases i <;> rfl

@[expose] noncomputable def bsF (i : Fin 4) : Nat := bs[i]

theorem prep_bsF (i : Fin 4) : PRep 275 9 (bsF i) vs[i] := by
  fin_cases i
  · exact prep_cen4
  · exact prep_cls (k := 0) (by norm_num)
  · exact prep_cls (k := 1) (by norm_num)
  · exact prep_cls (k := 2) (by norm_num)

theorem mem_bsF (i : Fin 4) : bsF i ∈ bs := List.getElem_mem _

theorem canon_bs : ∀ b ∈ bs, canonK 275 9 (mask 9) (275 * 9) b = true := by
  intro b hb
  simp only [bs, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact canon_cen4
  · exact canon_cls (by norm_num)
  · exact canon_cls (by norm_num)
  · exact canon_cls (by norm_num)

theorem basis_fact : EBasis F.v := by
  have hb := basis
  unfold m305basis at hb
  rw [band, band] at hb
  obtain ⟨h1, h2, h3⟩ := hb
  have hsq := (m305all_iff bs).1 h1
  have hcm := (m305all_iff bs).1 h2
  have hnz := (natRec_and (f := fun c => bIf(Nat.beq c 0, true,
    bIf(Nat.beq (m305prod bs c) m305id, false, true))) (Nat.pow 2 (List.length bs))).1 h3
  rw [v_eq]
  refine ⟨fun i => ?_, fun i j => ?_, fun c hc => ?_⟩
  · exact eq_of_beq (prep_mul (prep_bsF i) (prep_bsF i)) prep_one
      ((band.1 (hsq _ (mem_bsF i))).2)
  · exact eq_of_beq (prep_mul (prep_bsF i) (prep_bsF j)) (prep_mul (prep_bsF j) (prep_bsF i))
      ((m305all_iff bs).1 (hcm _ (mem_bsF i)) _ (mem_bsF j))
  · obtain ⟨m, hm, rfl⟩ := exists_bitVec c
    by_contra hne
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hne
      funext i
      simp [bitVec]
    have h := hnz m (by simpa [bs] using hm)
    have e0 : Nat.beq m 0 = false := Bool.eq_false_iff.mpr fun h => hm0 (Nat.eq_of_beq_eq_true h)
    rw [e0] at h
    cases e : Nat.beq (m305prod bs m) m305id
    · exact ne_of_beq (canon_prod canon_bs m) canon_one (prep_prod bs_vs m) prep_one e hc
    · rw [e] at h
      exact Bool.false_ne_true h

@[expose] noncomputable def sP : List (Equiv.Perm (Fin 275)) :=
  [tp 275 (clsTbl 6), tp 275 (clsTbl 7), tp 275 (clsTbl 8)]

theorem S_eq : F.S = closure {s | s ∈ sP} := by
  change closure (tp 275 '' {x | x ∈ sGens.toArray}) = _
  congr 1
  ext g
  simp [sP, sGens, eq_comm]

theorem sTwo_fact : F.S ≤ F.H ∧ Nat.card F.S = 128 := by
  obtain ⟨-, -, -, -, w4, w5, w6⟩ := words_H
  refine ⟨?_, ?_⟩
  · rw [S_eq, closure_le]
    intro g hg
    simp only [sP, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact w4
    · exact w5
    · exact w6
  · have hG : ∀ k < SE.ng, PRep 275 9 (SE.G k) (sP.getD k 1) := by
      intro k hk
      have hk3 : k < 3 := hk
      interval_cases k
      · have e : SE.G 0 = CT.F 6 := by decide +kernel
        rw [e]
        exact prep_cls (k := 6) (by norm_num)
      · have e : SE.G 1 = CT.F 7 := by decide +kernel
        rw [e]
        exact prep_cls (k := 7) (by norm_num)
      · have e : SE.G 2 = CT.F 8 := by decide +kernel
        rw [e]
        exact prep_cls (k := 8) (by norm_num)
    have h := (CFSG.ClassicalInvolution.ListBridge.enum_closure SE.ok rfl hG).2
    rw [S_eq, h]
    rfl

end CertificateChecks.KernelMcLCls

end

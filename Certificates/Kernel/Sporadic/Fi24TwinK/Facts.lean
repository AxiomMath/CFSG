module

public import Certificates.Kernel.Sporadic.Fi24TwinK.R0
public import Certificates.Kernel.Sporadic.Fi24TwinK.R1
public import Certificates.Kernel.Sporadic.Fi24TwinK.R2
public import Certificates.Kernel.Sporadic.Fi24ThreeO.Facts
public import CFSG.Certificates.Kernel.Spor.Fi24TwinKSound

public section

namespace CFSG.KD.Fi24TwinK

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO
  CFSG.KC.Fi24TwinK CFSG.KS.Fi24Net CFSG.KS.Fi24NetPt CFSG.KS.Fi24Kit CFSG.KS.Fi24ThreeO
  CFSG.KS.Fi24TwinK CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

theorem vn : VN NW NT := CFSG.KD.Fi24ThreeO.vn

structure TwinN (r : Nat) : Prop where
  m_pos : 1 ≤ m r
  m_le : m r ≤ 2048
  F0 : pt (F r) 0 = 0
  inc : ∀ i j, i < j → j < m r → pt (F r) i < pt (F r) j
  fix : ∀ y, (y < 306936 ∧ cP NW NT (wr r) y = y) ↔ ∃ i < m r, pt (F r) i = y
  lt_len : (lt r).length = (hc r).length + (bw r).length
  bw_len : (bw r).length = (bp r).length
  letters : ∀ j < (lt r).length, ∀ i < m r, ent (nthL 0 (lt r) j) i < m r ∧
    cP NW NT (dW (nthL [] (lw r) j)) (pt (F r) i) = pt (F r) (ent (nthL 0 (lt r) j) i)
  lw_lt : ∀ W ∈ lw r, ∀ c ∈ W, c < 26
  hc0 : hc r ≠ [] ∧ nthL [1] (hc r) 0 = []
  hc_pts : ∀ W ∈ hc r, ∃ i < m r, pt (F r) i = cP NW NT W 0
  bp_pts : ∀ k < (bp r).length, nthL 0 (bp r) k < m r ∧
    pt (F r) (nthL 0 (bp r) k) = cP NW NT (nthL [] (bw r) k) 0
  bp_ne : bp r ≠ []
  cd_ok : cdOK (c0 r).length (cd r) = true
  gw_lt : ∀ u ∈ gw r, ∀ l ∈ u, l < (lt r).length
  gw_b : ∀ k < (bp r).length, nthL [] (gw r) k = [0, (hc r).length + k]
  bp_le : (bp r).length ≤ (gw r).length
  nw_len : (nw r).length = (hc r).length
  cover : ∀ i < m r, ∃ v, InW ((hc r).map dW) v ∧ cP NW NT v (pt (F r) i) = 0
  rows : ∀ e ∈ (cl r).tail, ent (nthL 0 (lt r) 0) e.1 ≠ e.1 ∧
    ∀ i < m r, i ≠ 0 → i ≠ e.1 → (ent (nthL 0 (lt r) 0) i = i ↔ ent e.2 i = i)
  head : nthP (cl r) 0 = (0, nthL 0 (lt r) 0)
  tests : (∀ W ∈ xt r, cP NW NT W 0 ≠ 0 ∧ cP NW NT [26] (cP NW NT W 0) = cP NW NT W 0 ∧
      ∃ i < m r, pt (F r) i = cP NW NT W 0) ∧
    ∀ i < m r, cP NW NT [26] (pt (F r) i) ≠ pt (F r) i →
      (∀ W ∈ xt r, cP NW NT [26] (cP NW NT (invC W) (pt (F r) i)) = cP NW NT (invC W) (pt (F r) i)) →
        ∃ e ∈ cl r, pt (F r) e.1 = pt (F r) i
  xt_lt : ∀ W ∈ xt r, ∀ c ∈ W, c < 26
  norm : ∀ c < (nw r).length, (nthL [] (nw r) c).length = (gw r).length ∧
      ∀ k < (gw r).length, (∀ e ∈ nthL [] (nthL [] (nw r) c) k, e / 2 < (gw r).length) ∧
        ∀ i < m r, ent (nthL 0 (lt r) c) (gF (lt r) (gw r) k (ent (nthL 0 (lt r) c) i)) =
          sF (lt r) (gw r) (nthL [] (nthL [] (nw r) c) k) i
  comm : (ab r = true → ∀ i < (gw r).length, ∀ j < (gw r).length, ∀ x < m r,
      gF (lt r) (gw r) i (gF (lt r) (gw r) j x) = gF (lt r) (gw r) j (gF (lt r) (gw r) i x)) ∧
    (ab r = false → ∀ i < (gw r).length, ∀ j < (gw r).length, i < j → ∀ l < (gw r).length,
      ∀ x < m r,
      gFI (lt r) (gw r) i (gFI (lt r) (gw r) j (gF (lt r) (gw r) i (gF (lt r) (gw r) j
        (gF (lt r) (gw r) l x)))) =
        gF (lt r) (gw r) l (gFI (lt r) (gw r) i (gFI (lt r) (gw r) j (gF (lt r) (gw r) i
          (gF (lt r) (gw r) j x)))))
  conj : (gt r).length + 1 = (cl r).length ∧ ∀ k < (gt r).length,
    cP NW NT (nthL [] (gt r) k) 0 = 0 ∧
      cP NW NT (nthL [] (gt r) k) (pt (F r) (nthP (cl r) (k + 1)).1) = 305530
  gt_lt : ∀ W ∈ gt r, ∀ c ∈ W, c < 26

theorem nthL_eq {α : Type} (d : α) : ∀ (l : List α) (i : Nat) (hi : i < l.length), nthL d l i = l[i]
  | [], _, hi => absurd hi (by simp)
  | a :: l, 0, _ => rfl
  | a :: l, i + 1, hi => nthL_eq d l i (by simpa using hi)

theorem nthL_mem {α : Type} (d : α) {l : List α} {i : Nat} (hi : i < l.length) : nthL d l i ∈ l := by
  rw [nthL_eq d l i hi]
  exact List.getElem_mem hi

theorem nthL_ge {α : Type} (d : α) : ∀ (l : List α) (i : Nat), l.length ≤ i → nthL d l i = d
  | [], _, _ => rfl
  | a :: l, 0, h => absurd h (by simp)
  | a :: l, i + 1, h => nthL_ge d l i (by simpa using h)

theorem eqL_spec : ∀ {u v : List Nat}, eqL u v = true → u = v
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | a :: u, b :: v, h => by
    obtain ⟨h1, h2⟩ := CFSG.KC.Benes.andB_true h
    rw [Nat.eq_of_beq_eq_true h1, eqL_spec h2]

theorem cBuild_prefix (m : Nat) : ∀ (cd : List (Nat × Nat)) (C : List (Nat × Nat)),
    ∃ D, cBuild m C cd = C ++ D
  | [], C => ⟨[], by rw [List.append_nil]; rfl⟩
  | d :: cd, C => by
    obtain ⟨D, hD⟩ := cBuild_prefix m cd (C ++ [(ent (nthP C d.1).2 (nthP C d.2).1,
      cmpT m (cmpT m (nthP C d.1).2 (nthP C d.2).2) (nthP C d.1).2)])
    exact ⟨_ :: D, by
      change cBuild m (C ++ _) cd = _
      rw [hD, List.append_assoc, List.singleton_append]⟩

theorem hL_of {m : Nat} (hm : 1 ≤ m) {L : List Nat}
    (h : ∀ j < L.length, ∀ i < m, ent (nthL 0 L j) i < m) : ∀ l, ∀ i < m, ent (nthL 0 L l) i < m := by
  intro l i hi
  by_cases hl : l < L.length
  · exact h l hl i hi
  · rw [nthL_ge 0 L l (by omega)]
    rw [ent_eq, Nat.zero_div, Nat.zero_mod]
    omega

theorem twinN_of {r : Nat} (hfs : fs r = true) (htb : ∀ j < (lt r).length, tb r j = true)
    (hpp : pp r = true) (hcv : cv r = true) (hro : ro r = true) (hk2 : k2 r = true)
    (hnm : nm r = true) (hc2 : c2 r = true) (hcj : cj r = true)
    (hd1 : (lt r).length = (hc r).length + (bw r).length ∧ (bw r).length = (bp r).length ∧
      (∀ W ∈ lw r, ∀ c ∈ W, c < 26) ∧ hc r ≠ [] ∧ bp r ≠ [] ∧ (bp r).length ≤ (gw r).length ∧
      (∀ W ∈ xt r, ∀ c ∈ W, c < 26) ∧ (∀ W ∈ gt r, ∀ c ∈ W, c < 26))
    (hgw : (gw r).length ≤ 64) : TwinN r := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := hd1
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := fsOK_spec vn hfs
  have hL : ∀ j < (lt r).length, ∀ i < m r, ent (nthL 0 (lt r) j) i < m r ∧
      cP NW NT (dW (nthL [] (lw r) j)) (pt (F r) i) = pt (F r) (ent (nthL 0 (lt r) j) i) :=
    fun j hj => tabOK_spec vn f2 f4 (htb j hj)
  have hL' := hL_of f1 fun j hj i hi => (hL j hj i hi).1
  have hxt : ∀ W ∈ xt r, ∀ i < m r, cP NW NT (invC W) (pt (F r) i) < 306936 := by
    intro W hW i hi
    refine CFSG.KD.Fi24ThreeO.cP_pts (cs := invC W) (fun c hc => ?_)
      ((f6 (pt (F r) i)).2 ⟨i, hi, rfl⟩).1
    have := CFSG.KD.Fi24ThreeO.invC_lt (d7 W hW) c hc
    omega
  unfold pp at hpp
  rw [CFSG.KS.Fi24Net.letB_eq'] at hpp
  obtain ⟨p1, hpp⟩ := CFSG.KC.Benes.andB_true hpp
  obtain ⟨p2, hpp⟩ := CFSG.KC.Benes.andB_true hpp
  obtain ⟨p3, hpp⟩ := CFSG.KC.Benes.andB_true hpp
  obtain ⟨p4, hpp⟩ := CFSG.KC.Benes.andB_true hpp
  obtain ⟨p5, hpp⟩ := CFSG.KC.Benes.andB_true hpp
  obtain ⟨p6, hpp⟩ := CFSG.KC.Benes.andB_true hpp
  obtain ⟨p7, p8⟩ := CFSG.KC.Benes.andB_true hpp
  have hc0 : nthL [1] (hc r) 0 = [] := eqL_spec p3
  have hlen : ∀ {α : Type} (l : List α), lenL l = l.length := fun l => lenL_eq l
  refine ⟨f1, f2, f3, f4, f6, d1, d2, hL, d3, ⟨d4, hc0⟩, fun W hW => ?_, fun k hk => ?_, d5, ?_,
    ?_, fun k hk => ?_, d6, ?_, fun i hi => ?_, ?_, ?_, ?_, d7, ?_, ?_, ?_, d8⟩
  · have := CFSG.KS.Fi24ThreeO.allL_spec p1 W hW
    rw [← ptC_eq NW NT]
    exact (f5 _).1 (CFSG.KD.Fi24ThreeO.bit_of this)
  · have := CFSG.KS.Fi24ThreeO.allI_spec p2 k hk
    rw [Nat.zero_add, ← nthL_eq 0 _ k hk] at this
    obtain ⟨a, b⟩ := CFSG.KC.Benes.andB_true this
    refine ⟨Nat.blt_eq.mp a, ?_⟩
    rw [← ptC_eq NW NT]
    exact Nat.eq_of_beq_eq_true b
  · have e : ∀ (l : List Nat) (k : Nat), (List.rec (motive := fun _ => Nat → List (Nat × Nat))
        (fun _ => List.nil)
        (fun b _ ih k => (b, nthL 0 (lt r) (Nat.add (lenL (hc r)) k)) :: ih (Nat.succ k))
        l k).length = l.length := by
      intro l
      induction l with
      | nil => intro k; rfl
      | cons b l ih =>
        intro k
        change Nat.succ _ = _
        rw [ih]
        rfl
    have hc0len : (c0 r).length = Nat.succ (lenL (bp r)) := by
      unfold c0
      rw [List.length_cons, e, hlen]
    rw [hc0len]
    exact p6
  · intro u hu l hl
    have := CFSG.KS.Fi24ThreeO.allL_spec (CFSG.KS.Fi24ThreeO.allL_spec p7 u hu) l hl
    rw [← hlen]
    exact Nat.blt_eq.mp this
  · have := CFSG.KS.Fi24ThreeO.allI_spec p8 k hk
    rw [Nat.zero_add] at this
    have e := eqL_spec this
    rw [hlen] at e
    exact e
  · rw [← hlen, ← hlen]
    exact Nat.eq_of_beq_eq_true p5
  · have hy : pt (F r) i < 306936 := ((f6 _).2 ⟨i, hi, rfl⟩).1
    rcases covW_spec vn hcv hy with h | ⟨v, hv, h1⟩
    · exfalso
      change (ptsM ^^^ plF (m r) (F r)).testBit _ = true at h
      rw [Nat.testBit_xor, ptsM_bit hy, (f5 _).2 ⟨i, hi, rfl⟩] at h
      exact absurd h (by decide)
    · refine ⟨v, hv, ?_⟩
      by_contra hne
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
      change Nat.testBit 1 _ = true at h1
      rw [hk, Nat.testBit_succ, show (1 : Nat) / 2 = 0 by norm_num, Nat.zero_testBit] at h1
      exact absurd h1 Bool.false_ne_true
  · intro e he
    have hro' : allL (fun e => rowOK (m r) (nthP (cl r) 0).2 e.1 e.2) (List.tail (cl r)) = true :=
      hro
    have := CFSG.KS.Fi24ThreeO.allL_spec hro' e he
    have h := rowOK_spec this
    obtain ⟨D, hD⟩ := cBuild_prefix (m r) (cd r) (c0 r)
    have e0 : (nthP (cl r) 0).2 = nthL 0 (lt r) 0 := by
      unfold cl
      rw [hD]
      rfl
    rw [e0] at h
    exact h
  · obtain ⟨D, hD⟩ := cBuild_prefix (m r) (cd r) (c0 r)
    unfold cl
    rw [hD]
    rfl
  · exact k2OK_spec_ vn f2 f4 hxt hk2
  · exact (nmChk_spec f2 hL' hnm).2
  · exact c2Chk_spec_ f2 hL' hgw hc2
  · exact gtOK_spec vn hcj

theorem tb_all (r : Nat) (h : ∀ j < 8, tb r j = true) (hl : (lt r).length = 8) :
    ∀ j < (lt r).length, tb r j = true := fun j hj => h j (hl ▸ hj)

theorem tb0 : ∀ j < 8, tb 0 j = true := by
  intro j hj
  interval_cases j
  exacts [Ck.tbA0, Ck.tbA1, Ck.tbA2, Ck.tbA3, Ck.tbA4, Ck.tbA5, Ck.tbA6, Ck.tbA7]

theorem tb1 : ∀ j < 8, tb 1 j = true := by
  intro j hj
  interval_cases j
  exacts [Ck.tbB0, Ck.tbB1, Ck.tbB2, Ck.tbB3, Ck.tbB4, Ck.tbB5, Ck.tbB6, Ck.tbB7]

theorem tb2 : ∀ j < 8, tb 2 j = true := by
  intro j hj
  interval_cases j
  exacts [Ck.tbC0, Ck.tbC1, Ck.tbC2, Ck.tbC3, Ck.tbC4, Ck.tbC5, Ck.tbC6, Ck.tbC7]

theorem data1 : ∀ r < 3, (lt r).length = (hc r).length + (bw r).length ∧ (bw r).length = (bp r).length ∧
      (∀ W ∈ lw r, ∀ c ∈ W, c < 26) ∧ hc r ≠ [] ∧ bp r ≠ [] ∧ (bp r).length ≤ (gw r).length ∧
      (∀ W ∈ xt r, ∀ c ∈ W, c < 26) ∧ (∀ W ∈ gt r, ∀ c ∈ W, c < 26) := by
  decide +kernel

theorem lt_len8 : ∀ r < 3, (lt r).length = 8 := by decide +kernel

theorem gw_le64 : ∀ r < 3, (gw r).length ≤ 64 := by decide +kernel

theorem twin_facts : ∀ r < 3, TwinN r := by
  intro r hr
  interval_cases r
  · exact twinN_of Ck.fs0 (tb_all 0 tb0 (lt_len8 0 (by norm_num)))
      Ck.pp0 Ck.cv0 Ck.ro0 Ck.k20 Ck.nm0 Ck.c20 Ck.cj0 (data1 0 (by norm_num))
      (gw_le64 0 (by norm_num))
  · exact twinN_of Ck.fs1 (tb_all 1 tb1 (lt_len8 1 (by norm_num)))
      Ck.pp1 Ck.cv1 Ck.ro1 Ck.k21 Ck.nm1 Ck.c21 Ck.cj1 (data1 1 (by norm_num))
      (gw_le64 1 (by norm_num))
  · exact twinN_of Ck.fs2 (tb_all 2 tb2 (lt_len8 2 (by norm_num)))
      Ck.pp2 Ck.cv2 Ck.ro2 Ck.k22 Ck.nm2 Ck.c22 Ck.cj2 (data1 2 (by norm_num))
      (gw_le64 2 (by norm_num))

theorem ev_fix : ∀ l ∈ ev, LN NW l 0 = 0 ∧ LN NW l 305530 = 305530 := by
  intro l hl
  have := CFSG.KS.Fi24ThreeO.allL_spec Ck.evf l hl
  obtain ⟨a, b⟩ := CFSG.KC.Benes.andB_true this
  rw [← letN_eq, ← letN_eq]
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b⟩

end CFSG.KD.Fi24TwinK

end

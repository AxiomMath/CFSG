module

public import Certificates.Kernel.GH74.M12C4
public import Certificates.Kernel.GH74.Glue
public import Certificates.Kernel.GH74.Derived
public import Certificates.Kernel.Sporadic.OddCore.CentGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.M12C4

open Subgroup
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
open CFSG.GH74.Generic.S45.EvSpor CertificateChecks.KernelGH74
open scoped commutatorElement

theorem base : szOK 24 5 = true ∧ cK idK = true ∧ CFSG.KS.Prim.idK 24 5 (mask 5) = true ∧
    (∀ j < 4, cK (C4.GI j) = true ∧ cK (C4I j) = true ∧ iK (C4.GI j) (C4I j) = true ∧
      C4.G j = pidn 24 5) ∧
    (∀ j < 3, H3.GI j = C4.GI j ∧ H3I j = C4I j ∧ H3.G j = pidn 24 5) ∧
    (∀ j < 2, cK (KA.GI j) = true ∧ cK (KAI j) = true ∧ iK (KA.GI j) (KAI j) = true ∧
      KA.G j = pidn 24 5) ∧
    (∀ j < 3, cK (M12Y j) = true ∧ iK (M12Y j) (M12Y j) = true) ∧ cK (M12Y 3) = true ∧
    C4.cnt = 480 ∧ H3.cnt = 240 ∧ KA.cnt = 60 ∧
    penumHdK idK C4.cnt 3000 C4.T C4.PL = true ∧ penumHdK idK H3.cnt 3000 H3.T H3.PL = true ∧
    penumHdK idK KA.cnt 3000 KA.T KA.PL = true := by
  have h := base_ok
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := h
  refine ⟨a1, a2, a3, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, a8,
    Nat.eq_of_beq_eq_true a9, Nat.eq_of_beq_eq_true a10, Nat.eq_of_beq_eq_true a11, a12, a13, a14⟩
  · have := allN_spec a4 j hj
    simp only [bAnd_iff] at this
    exact ⟨this.1, this.2.1, this.2.2.1, Nat.eq_of_beq_eq_true this.2.2.2⟩
  · have := allN_spec a5 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2.1,
      Nat.eq_of_beq_eq_true this.2.2⟩
  · have := allN_spec a6 j hj
    simp only [bAnd_iff] at this
    exact ⟨this.1, this.2.1, this.2.2.1, Nat.eq_of_beq_eq_true this.2.2.2⟩
  · have := allN_spec a7 j hj
    simp only [bAnd_iff] at this
    exact this

theorem hidc : canonK 24 5 (mask 5) (24 * 5) (pidn 24 5) = true := base.2.1

theorem hid : idT 24 = tabT (unpack 24 5 (pidn 24 5)) := by
  rw [idT_tabT, idK_sound base.2.2.1]

theorem y_tab {j : Nat} {x : Table} (hx : natArr x = unpack 24 5 (M12Y j)) :
    x = tabT (unpack 24 5 (M12Y j)) := by
  rw [← hx, tabT_natArr]

theorem y_tabs : m12ZT = tabT (unpack 24 5 (M12Y 0)) ∧ m12AT = tabT (unpack 24 5 (M12Y 1)) ∧
    m12ST = tabT (unpack 24 5 (M12Y 2)) ∧ m12KaB = tabT (unpack 24 5 (M12Y 3)) := by
  have h := tabs_eq.2.2
  simp only [List.cons.injEq, and_true] at h
  exact ⟨y_tab h.1, y_tab h.2.1, y_tab h.2.2.1, y_tab h.2.2.2⟩

theorem yc {j : Nat} (hj : j < 4) : canonK 24 5 (mask 5) (24 * 5) (M12Y j) = true := by
  rcases Nat.lt_or_ge j 3 with h | h
  · exact (base.2.2.2.2.2.2.1 j h).1
  · obtain rfl : j = 3 := by omega
    exact base.2.2.2.2.2.2.2.1

theorem c4_tabs : TabsOK 24 5 4 C4.GI m12CGens.toArray :=
  tabsOK_of_map tabs_eq.1 fun j hj => (base.2.2.2.1 j hj).1

theorem ka_tabs : TabsOK 24 5 2 KA.GI m12KaGens.toArray :=
  tabsOK_of_map tabs_eq.2.1 fun j hj => (base.2.2.2.2.2.1 j hj).1

theorem h3_tabs : TabsOK 24 5 3 H3.GI (m12CGens.take 3).toArray :=
  tabsOK_of_map tabsH_eq fun j hj => by
    rw [(base.2.2.2.2.1 j hj).1]
    exact (base.2.2.2.1 j (by omega)).1

theorem c4_invs : ∀ j < 4, invEqK 24 5 (mask 5) (24 * 5) (C4.GI j) (C4I j) = true ∧
    canonK 24 5 (mask 5) (24 * 5) (C4I j) = true :=
  fun j hj => ⟨(base.2.2.2.1 j hj).2.2.1, (base.2.2.2.1 j hj).2.1⟩

theorem h3_invs : ∀ j < 3, invEqK 24 5 (mask 5) (24 * 5) (H3.GI j) (H3I j) = true ∧
    canonK 24 5 (mask 5) (24 * 5) (H3I j) = true := fun j hj => by
  rw [(base.2.2.2.2.1 j hj).1, (base.2.2.2.2.1 j hj).2.1]
  exact c4_invs j (by omega)

theorem ka_invs : ∀ j < 2, invEqK 24 5 (mask 5) (24 * 5) (KA.GI j) (KAI j) = true ∧
    canonK 24 5 (mask 5) (24 * 5) (KAI j) = true :=
  fun j hj => ⟨(base.2.2.2.2.2.1 j hj).2.2.1, (base.2.2.2.2.2.1 j hj).2.1⟩

theorem c4_pe : ∀ i < C4.cnt, penumPtK 24 5 (mask 5) (24 * 5) true C4.G C4.GI 4 C4.cnt
    C4.T C4.PL C4.POS C4.SRT C4.SRI i = true :=
  fun i hi => penumSl_spec c4E i (Nat.zero_le _) (by omega) hi
theorem c4_hs : ∀ i < C4.cnt, hsortPtK 24 5 (mask 5) C4.cnt C4.T C4.HS C4.HSI i = true :=
  fun i hi => slK_spec c4H i (Nat.zero_le _) (by omega) hi
theorem c4_cl : ∀ c < C4.cnt * (4 + 4), findPtK C4.cnt C4.T
    (prodQK 24 5 (mask 5) (4 + 4) C4.T (bothK 4 C4.GI C4I)) C4Cl c = true :=
  fun c hc => slK_spec c4Cl c (Nat.zero_le _) (by change c < Nat.mul C4.cnt 8; omega)
    (by change c < Nat.mul C4.cnt 8; omega)

theorem h3_pe : ∀ i < H3.cnt, penumPtK 24 5 (mask 5) (24 * 5) true H3.G H3.GI 3 H3.cnt
    H3.T H3.PL H3.POS H3.SRT H3.SRI i = true :=
  fun i hi => penumSl_spec h3E i (Nat.zero_le _) (by omega) hi
theorem h3_hs : ∀ i < H3.cnt, hsortPtK 24 5 (mask 5) H3.cnt H3.T H3.HS H3.HSI i = true :=
  fun i hi => slK_spec h3H i (Nat.zero_le _) (by omega) hi
theorem h3_cl : ∀ c < H3.cnt * (3 + 3), findPtK H3.cnt H3.T
    (prodQK 24 5 (mask 5) (3 + 3) H3.T (bothK 3 H3.GI H3I)) H3Cl c = true :=
  fun c hc => slK_spec h3Cl c (Nat.zero_le _) (by change c < Nat.mul H3.cnt 6; omega)
    (by change c < Nat.mul H3.cnt 6; omega)

theorem ka_pe : ∀ i < KA.cnt, penumPtK 24 5 (mask 5) (24 * 5) true KA.G KA.GI 2 KA.cnt
    KA.T KA.PL KA.POS KA.SRT KA.SRI i = true :=
  fun i hi => penumSl_spec kaE i (Nat.zero_le _) (by omega) hi
theorem ka_hs : ∀ i < KA.cnt, hsortPtK 24 5 (mask 5) KA.cnt KA.T KA.HS KA.HSI i = true :=
  fun i hi => slK_spec kaH i (Nat.zero_le _) (by omega) hi
theorem ka_cl : ∀ c < KA.cnt * (2 + 2), findPtK KA.cnt KA.T
    (prodQK 24 5 (mask 5) (2 + 2) KA.T (bothK 2 KA.GI KAI)) KACl c = true :=
  fun c hc => slK_spec kaCl c (Nat.zero_le _) (by change c < Nat.mul KA.cnt 4; omega)
    (by change c < Nat.mul KA.cnt 4; omega)

theorem c4_enum : enumOK 24 cap m12CGens 480 = true :=
  evEnum_of_rec base.1 (fun j hj => (base.2.2.2.1 j hj).2.2.2) c4_tabs c4_invs
    base.2.2.2.2.2.2.2.2.2.2.2.1 c4_pe c4_hs c4_cl base.2.2.2.2.2.2.2.2.1

theorem h3_enum : enumOK 24 cap (m12CGens.take 3) 240 = true :=
  evEnum_of_rec base.1 (fun j hj => (base.2.2.2.2.1 j hj).2.2) h3_tabs h3_invs
    base.2.2.2.2.2.2.2.2.2.2.2.2.1 h3_pe h3_hs h3_cl base.2.2.2.2.2.2.2.2.2.1

theorem ka_enum : enumOK 24 cap m12KaGens 60 = true :=
  evEnum_of_rec base.1 (fun j hj => (base.2.2.2.2.2.1 j hj).2.2.2) ka_tabs ka_invs
    base.2.2.2.2.2.2.2.2.2.2.2.2.2 ka_pe ka_hs ka_cl base.2.2.2.2.2.2.2.2.2.2.1

theorem c4_arr : m12C2A = (hRec 24 5 C4.cnt C4.T C4.PL).1 :=
  closArr_eq (cap := cap) base.1 (fun j hj => (base.2.2.2.1 j hj).2.2.2) c4_tabs
    base.2.2.2.2.2.2.2.2.2.2.2.1 c4_pe c4_hs

theorem h3_arr : closArr 24 cap (m12CGens.take 3) = (hRec 24 5 H3.cnt H3.T H3.PL).1 :=
  closArr_eq (cap := cap) base.1 (fun j hj => (base.2.2.2.2.1 j hj).2.2) h3_tabs
    base.2.2.2.2.2.2.2.2.2.2.2.2.1 h3_pe h3_hs

theorem ka_arr : m12Ka = (hRec 24 5 KA.cnt KA.T KA.PL).1 :=
  closArr_eq (cap := cap) base.1 (fun j hj => (base.2.2.2.2.2.1 j hj).2.2.2) ka_tabs
    base.2.2.2.2.2.2.2.2.2.2.2.2.2 ka_pe ka_hs

theorem facts : (∀ j < 3, Nat.beq (pc (M12Y j) (M12Y j)) idK = true ∧
      bIf(Nat.beq (M12Y j) idK, false, true) = true) ∧
    Nat.beq (pc (M12Y 2) (M12Y 0)) (pc (M12Y 0) (M12Y 2)) = true ∧
    Nat.beq (pc (M12Y 2) (M12Y 1)) (pc (M12Y 1) (M12Y 2)) = true ∧
    Nat.beq (pc (M12Y 2) (M12Y 3)) (pc (M12Y 3) (M12Y 2)) = true ∧
    r32 C4P 0 < C4.cnt ∧ C4.T (r32 C4P 0) = M12Y 1 ∧ r32 C4P 1 < C4.cnt ∧
    C4.T (r32 C4P 1) = M12Y 3 ∧ ∀ c < 15, r32 KAP c < KA.cnt ∧ KA.T (r32 KAP c) = kaQ c := by
  have h := facts_ok
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  refine ⟨fun j hj => ?_, a2, a3, a4, Nat.le_of_ble_eq_true a5, Nat.eq_of_beq_eq_true a6,
    Nat.le_of_ble_eq_true a7, Nat.eq_of_beq_eq_true a8, fun c hc => ?_⟩
  · have := allN_spec a1 j hj
    simp only [bAnd_iff] at this
    exact this
  · have := allN_spec a9 c hc
    simp only [bAnd_iff] at this
    exact ⟨Nat.le_of_ble_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

theorem reps_ok : m12RepsOK = true := by
  obtain ⟨yz, ya, ys, -⟩ := y_tabs
  have hn : (24 : Nat) < 2 ^ 32 := by norm_num
  have i0 := facts.1 0 (by norm_num)
  have i1 := facts.1 1 (by norm_num)
  have i2 := facts.1 2 (by norm_num)
  unfold m12RepsOK
  rw [yz, ya, ys, permOK_unpack (yc (j := 0) (by norm_num)) (base.2.2.2.2.2.2.1 0 (by norm_num)).2,
    permOK_unpack (yc (j := 1) (by norm_num)) (base.2.2.2.2.2.2.1 1 (by norm_num)).2,
    permOK_unpack (yc (j := 2) (by norm_num)) (base.2.2.2.2.2.2.1 2 (by norm_num)).2,
    involOK_unpack' hn hid hidc (yc (j := 0) (by norm_num)),
    involOK_unpack' hn hid hidc (yc (j := 1) (by norm_num)),
    involOK_unpack' hn hid hidc (yc (j := 2) (by norm_num))]
  change (true && bAnd(Nat.beq (pc (M12Y 0) (M12Y 0)) idK, bIf(Nat.beq (M12Y 0) idK, false, true))
    && true && bAnd(Nat.beq (pc (M12Y 1) (M12Y 1)) idK, bIf(Nat.beq (M12Y 1) idK, false, true))
    && true && bAnd(Nat.beq (pc (M12Y 2) (M12Y 2)) idK, bIf(Nat.beq (M12Y 2) idK, false, true)))
    = true
  rw [i0.1, i0.2, i1.1, i1.2, i2.1, i2.2]
  rfl

theorem c2A_ok : m12C2AEnumOK = true := by
  have hinv : invsOK 24 m12C2A = true := invsOK_of_enumOK (by norm_num) c4_enum
  unfold m12C2AEnumOK
  rw [c4_enum, hinv]
  rfl

theorem c4_mem {q : Nat} (hq : q < C4.cnt) {X : Nat} (hX : C4.T q = X) :
    memT 24 m12C2A (tabT (unpack 24 5 X)) = true := by
  rw [c4_arr, ← hX]
  exact memT_of hq (tblEq_self (penumPt_canon (c4_pe q hq)))

theorem ka_ok : m12KaEnumOK = true := by
  obtain ⟨-, ya, -, yb⟩ := y_tabs
  obtain ⟨-, -, -, -, p0, e0, p1, e1, -⟩ := facts
  unfold m12KaEnumOK
  rw [ka_enum, ya, yb, c4_mem p0 e0, c4_mem p1 e1]
  rfl

theorem outer_ok : m12OuterOK = true := by
  obtain ⟨yz, ya, ys, yb⟩ := y_tabs
  obtain ⟨-, a2, a3, a4, -⟩ := facts
  unfold m12OuterOK
  rw [yz, ya, ys, yb, CFSG.KS.MulH.commTT_unpack (yc (j := 2) (by norm_num)) (yc (j := 0) (by norm_num)),
    CFSG.KS.MulH.commTT_unpack (yc (j := 2) (by norm_num)) (yc (j := 1) (by norm_num)),
    CFSG.KS.MulH.commTT_unpack (yc (j := 2) (by norm_num)) (yc (j := 3) (by norm_num))]
  change (Nat.beq (pc (M12Y 2) (M12Y 0)) (pc (M12Y 0) (M12Y 2)) &&
    Nat.beq (pc (M12Y 2) (M12Y 1)) (pc (M12Y 1) (M12Y 2)) &&
    Nat.beq (pc (M12Y 2) (M12Y 3)) (pc (M12Y 3) (M12Y 2))) = true
  rw [a2, a3, a4]
  rfl

@[expose] def inner (g : Equiv.Perm (Fin 24)) : Prop := (g ⟨0, by norm_num⟩).val < 12

instance : DecidablePred inner := fun g => inferInstanceAs (Decidable (_ < 12))

theorem innerT_iff {T : Table} {g : Equiv.Perm (Fin 24)} (hT : Rep 24 T g) :
    innerT T = true ↔ inner g := by
  have h0 := hT 0 (by norm_num)
  rw [idx_of_lt _ (by norm_num)] at h0
  unfold innerT inner
  unfold ap at h0
  rw [h0, decide_eq_true_iff]
  rfl

theorem innerT_unpack {X : Nat} (hX : canonK 24 5 (mask 5) (24 * 5) X = true) :
    innerT (tabT (unpack 24 5 X)) = Nat.blt (pg 5 (mask 5) X 0) 12 := by
  unfold innerT
  have h := ap_tabT (unpack 24 5 X) (i := 0) (unpack_lt hX)
  unfold ap at h
  rw [h, CFSG.KC.Misc.PairCount.unpack_get (by norm_num : (0 : Nat) < 24)]
  cases e : Nat.blt (pg 5 (mask 5) X 0) 12
  · have : ¬ pg 5 (mask 5) X 0 < 12 := fun h' => by
      rw [Eq.mpr Nat.blt_eq h'] at e
      exact Bool.noConfusion e
    exact decide_eq_false this
  · exact decide_eq_true (Eq.mp Nat.blt_eq e)

theorem ka_mem {c : Nat} (hc : c < 15) : memT 24 m12Ka (tabT (unpack 24 5 (kaQ c))) = true := by
  obtain ⟨hp, he⟩ := facts.2.2.2.2.2.2.2.2 c hc
  rw [ka_arr, ← he]
  exact memT_of hp (tblEq_self (penumPt_canon (ka_pe _ hp)))

theorem h3c {j : Nat} (hj : j < 3) : canonK 24 5 (mask 5) (24 * 5) (H3.GI j) = true :=
  (h3_tabs.2 j hj).2

theorem h3_get {j : Nat} (hj : j < 3) :
    (m12CGens.take 3).toArray[j]! = tabT (unpack 24 5 (H3.GI j)) := (h3_tabs.2 j hj).1

theorem m12_derived : m12DerivedOK = true := by
  have hn : (24 : Nat) < 2 ^ 32 := by norm_num
  obtain ⟨hEC, hCc, -⟩ := enumOK_spec hn c4_enum
  obtain ⟨hEK, -, hKrep⟩ := enumOK_spec hn ka_enum
  obtain ⟨hEH, hHc, hHrep⟩ := enumOK_spec hn h3_enum
  set Csub := closure (tp 24 '' {x | x ∈ m12CGens.toArray}) with hCdef
  set Ksub := closure (tp 24 '' {x | x ∈ m12KaGens.toArray}) with hKdef
  set Hsub := closure (tp 24 '' {x | x ∈ (m12CGens.take 3).toArray}) with hHdef
  have hgen : ∀ j < 3, Rep 24 (tabT (unpack 24 5 (H3.GI j)))
      (tp 24 (tabT (unpack 24 5 (H3.GI j)))) ∧
      tp 24 (tabT (unpack 24 5 (H3.GI j))) ∈ tp 24 '' {x | x ∈ (m12CGens.take 3).toArray} := by
    intro j hj
    have hm : (m12CGens.take 3).toArray[j]! ∈ (m12CGens.take 3).toArray := by
      rw [getElem!_pos _ j (by rw [h3_tabs.1]; exact hj)]
      exact Array.getElem_mem _
    rw [h3_get hj] at hm
    exact ⟨hHrep _ (List.mem_toArray.1 hm), ⟨_, hm, rfl⟩⟩
  have hgenS : ∀ s ∈ tp 24 '' {x | x ∈ (m12CGens.take 3).toArray}, ∃ j < 3,
      s = tp 24 (tabT (unpack 24 5 (H3.GI j))) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj, rfl, -⟩ := TabsOK_list h3_tabs (List.mem_toArray.1 hx)
    exact ⟨j, hj, rfl⟩
  have hinvH : ∀ j < 3, Rep 24 (tabT (unpack 24 5 (H3I j)))
      (tp 24 (tabT (unpack 24 5 (H3.GI j))))⁻¹ := fun j hj => by
    have := rep_invT_of_rep hn (hgen j hj).1
    rwa [invT_unpack (lt_of_canonK (h3_invs j hj).2) (h3_invs j hj).1] at this
  have hkgen : ∀ k ∈ tp 24 '' {x | x ∈ m12KaGens.toArray},
      ∃ l < 2, Rep 24 (tabT (unpack 24 5 (M12Y (2 * l + 1)))) k := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ m12KaGens := List.mem_toArray.1 hx
    have hr := hKrep x hx'
    obtain ⟨-, ya, -, yb⟩ := y_tabs
    simp only [m12KaGens, List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl
    · exact ⟨0, by norm_num, by rw [← ya]; exact hr⟩
    · exact ⟨1, by norm_num, by rw [← yb]; exact hr⟩
  have hnorm : ∀ s ∈ tp 24 '' {x | x ∈ (m12CGens.take 3).toArray}, ∀ m ∈ Ksub,
      s * m * s⁻¹ ∈ Ksub := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := hgenS s hs
    refine conj_mem_closure fun k hk => ?_
    obtain ⟨l, hl, hrk⟩ := hkgen k hk
    have hc : 2 * j + l < 15 := by omega
    have hY : canonK 24 5 (mask 5) (24 * 5) (M12Y (2 * l + 1)) = true := yc (by omega)
    have e : kaQ (2 * j + l) = pc (pc (H3.GI j) (M12Y (2 * l + 1))) (H3I j) := by
      interval_cases j <;> interval_cases l <;> rfl
    have hrep : Rep 24 (tabT (unpack 24 5 (kaQ (2 * j + l))))
        (tp 24 (tabT (unpack 24 5 (H3.GI j))) * k * (tp 24 (tabT (unpack 24 5 (H3.GI j))))⁻¹) := by
      rw [e]
      unfold pc
      rw [← compT_unpack (CFSG.KC.BfsPin.canonK_pcomp (h3c hj) hY) (h3_invs j hj).2,
        ← compT_unpack (h3c hj) hY]
      exact Rep.compT (Rep.compT (hgen j hj).1 hrk) (hinvH j hj)
    exact (hEK.mem_iff hrep).1 (ka_mem hc)
  have hcomm : ∀ s ∈ tp 24 '' {x | x ∈ (m12CGens.take 3).toArray},
      ∀ t ∈ tp 24 '' {x | x ∈ (m12CGens.take 3).toArray}, ⁅s, t⁆ ∈ Ksub := by
    intro s hs t ht
    obtain ⟨i, hi, rfl⟩ := hgenS s hs
    obtain ⟨j, hj, rfl⟩ := hgenS t ht
    have hc : 6 + 3 * i + j < 15 := by omega
    have e : kaQ (6 + 3 * i + j) =
        pc (pc (H3.GI i) (H3.GI j)) (pc (H3I i) (H3I j)) := by
      interval_cases i <;> interval_cases j <;> rfl
    have hrep : Rep 24 (tabT (unpack 24 5 (kaQ (6 + 3 * i + j))))
        ⁅tp 24 (tabT (unpack 24 5 (H3.GI i))), tp 24 (tabT (unpack 24 5 (H3.GI j)))⁆ := by
      rw [e, commutatorElement_def, mul_assoc (_ * _)]
      unfold pc
      rw [← compT_unpack (CFSG.KC.BfsPin.canonK_pcomp (h3c hi) (h3c hj))
        (CFSG.KC.BfsPin.canonK_pcomp (h3_invs i hi).2 (h3_invs j hj).2),
        ← compT_unpack (h3c hi) (h3c hj), ← compT_unpack (h3_invs i hi).2 (h3_invs j hj).2]
      exact Rep.compT (Rep.compT (hgen i hi).1 (hgen j hj).1) (Rep.compT (hinvH i hi) (hinvH j hj))
    exact (hEK.mem_iff hrep).1 (ka_mem hc)
  have hHK := comm_mem_of_gens hnorm hcomm
  have hHC : Hsub ≤ Csub := by
    refine closure_mono ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    have hx' : x ∈ m12CGens.take 3 := List.mem_toArray.1 hx
    exact List.mem_toArray.2 (List.mem_of_mem_take hx')
  have hHin : ∀ h ∈ Hsub, inner h := by
    intro h hh
    obtain ⟨k, hk, hrk⟩ := hEH.2 h hh
    have hk' : k < H3.cnt := by rw [h3_arr, hRec_size] at hk; exact hk
    rw [h3_arr] at hrk
    have e : (hRec 24 5 H3.cnt H3.T H3.PL).1[k]! = tabT (unpack 24 5 (H3.T k)) := hRec_get hk'
    rw [e] at hrk
    refine (innerT_iff hrk).1 ?_
    rw [innerT_unpack (penumPt_canon (h3_pe k hk'))]
    exact allN_spec h3_inner k hk'
  have hcardI : Nat.card {x : Csub // inner x} = 240 := by
    have hsz : Nat.card Csub = m12C2A.size := by
      rw [hCc, c4_arr, hRec_size, base.2.2.2.2.2.2.2.2.1]
    rw [card_eq_countP_of_enums hEC hsz (p := innerT) (fun T g hT => innerT_iff hT),
      show closArr 24 cap m12CGens = (hRec 24 5 C4.cnt C4.T C4.PL).1 from c4_arr,
      countP_hRec (hi := 8) (q := fun i => Nat.blt (pg 5 (mask 5) (C4.T i) 0) 12)
        (by rw [base.2.2.2.2.2.2.2.2.1]; norm_num) (fun i hi => innerT_unpack (penumPt_canon (c4_pe i hi)))]
    exact Nat.eq_of_beq_eq_true c4_inner
  have hsurj : ∀ x ∈ Csub, inner x → x ∈ Hsub := by
    let f : Hsub → {x : Csub // inner x} := fun h => ⟨⟨h.1, hHC h.2⟩, hHin h.1 h.2⟩
    have hf : Function.Injective f := fun a b hab => by
      have := congrArg (fun z : {x : Csub // inner x} => (z.1 : Equiv.Perm (Fin 24))) hab
      exact Subtype.ext this
    have hb := hf.bijective_of_nat_card_le (by rw [hcardI, hHc])
    intro x hx hix
    obtain ⟨h, hh⟩ := hb.2 ⟨⟨x, hx⟩, hix⟩
    have := congrArg (fun z : {x : Csub // inner x} => (z.1 : Equiv.Perm (Fin 24))) hh
    simp only [f] at this
    rw [← this]
    exact h.2
  unfold m12DerivedOK innerDerivedOK
  rw [Array.all_eq_true]
  intro a ha
  obtain ⟨gx, hgxC, hrx⟩ := hEC.1 a ha
  rw [← getElem!_pos m12C2A a ha]
  cases hix : innerT m12C2A[a]!
  · rfl
  · simp only [Bool.not_true, Bool.false_or]
    rw [Array.all_eq_true]
    intro b hb
    obtain ⟨gy, hgyC, hry⟩ := hEC.1 b hb
    rw [← getElem!_pos m12C2A b hb]
    cases hiy : innerT m12C2A[b]!
    · rfl
    · simp only [Bool.not_true, Bool.false_or]
      have hxH := hsurj gx hgxC ((innerT_iff hrx).1 hix)
      have hyH := hsurj gy hgyC ((innerT_iff hry).1 hiy)
      have hrep : Rep 24 (compT 24 (compT 24 m12C2A[a]! m12C2A[b]!)
          (compT 24 (invT 24 m12C2A[a]!) (invT 24 m12C2A[b]!))) ⁅gx, gy⁆ := by
        rw [commutatorElement_def, mul_assoc (gx * gy)]
        exact Rep.compT (Rep.compT hrx hry)
          (Rep.compT (rep_invT_of_rep hn hrx) (rep_invT_of_rep hn hry))
      exact (hEK.mem_iff hrep).2 (hHK gx hxH gy hyH)

end CertificateChecks.KernelGH74.M12C4

end

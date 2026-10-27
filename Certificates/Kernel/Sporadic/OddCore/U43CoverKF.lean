module

public import Certificates.Kernel.Sporadic.OddCore.U43CoverK
public import Certificates.Kernel.Multipliers.U43BFacts
import CFSG.Certificates.Kernel.BfsPinSetSound
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.U43CoverK

open CFSG.EvenSporadicStandard.HSStd.U43 CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin

theorem base : szOK 820 10 = true ∧ cK (pidn 820 10) = true ∧
    CFSG.KS.Prim.idK 820 10 (mask 10) = true ∧
    allN 4 (fun j => bAnd(Nat.beq (U43KB.GI j) (gB j), bAnd(Nat.beq (U43KB.G j) (pidn 820 10),
      bAnd(cK (U43KB.GI j), bAnd(cK (U43KBI j), invEqK 820 10 (mask 10) (820 * 10) (U43KB.GI j)
        (U43KBI j)))))) = true ∧
    allN 5 (fun j => bAnd(Nat.beq (U43KC.GI j) (gC j), bAnd(Nat.beq (U43KC.G j) (pidn 820 10),
      bAnd(cK (U43KC.GI j), bAnd(cK (U43KCI j), invEqK 820 10 (mask 10) (820 * 10) (U43KC.GI j)
        (U43KCI j)))))) = true ∧
    Nat.beq U43KB.cnt 324 = true ∧ Nat.beq U43KC.cnt 324 = true ∧
    penumHdK (pidn 820 10) U43KB.cnt 400 U43KB.T U43KB.PL = true ∧
    penumHdK (pidn 820 10) U43KC.cnt 400 U43KC.T U43KC.PL = true := by
  simpa only [bAnd_iff] using base_ok

theorem hidc : canonK 820 10 (mask 10) (820 * 10) (pidn 820 10) = true := base.2.1

theorem hid : idT 820 = tabT (unpack 820 10 (pidn 820 10)) := by
  rw [idT_tabT, idK_sound base.2.2.1]

@[expose] noncomputable def tP (P : Nat) : Table := tabT (unpack 820 10 P)

theorem inK_facts {y k : Nat} (h : inK y k = true) :
    cK (U43KP k) = true ∧ cK (U43KI k) = true ∧
      invEqK 820 10 (mask 10) (820 * 10) (U43KP k) (U43KI k) = true ∧
      siftK 820 10 (mask 10) (820 * 10) (pidn 820 10) KernelU43B.C.LR KernelU43B.C.TRI
        KernelU43B.C.BP 3 0 (U43KP k) = true ∧
      Nat.beq (pc (U43KP k) (U43KP y)) (pc (U43KP y) (U43KP k)) = true := by
  simpa only [inK, bAnd_iff] using h

theorem inP_tab {P : Nat} (hc : cK P = true)
    (h : siftK 820 10 (mask 10) (820 * 10) (pidn 820 10) KernelU43B.C.LR KernelU43B.C.TRI
      KernelU43B.C.BP 3 0 P = true) : inP (natArr (tP P)) = true := by
  unfold inP CFSG.EvenSporadicStandard.M24Std.CU43.levels baseArr tP
  rw [natArr_tabT hc, KernelU43B.base_eq]
  exact siftK_sound KernelU43B.binds KernelU43B.perm KernelU43B.C.hl rfl (range_of_canonK hc) h

theorem mem_of {y k : Nat} (hy : cK (U43KP y) = true) (h : inK y k = true) :
    memCheck (tP (U43KP y)) (tP (U43KP k)) = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := inK_facts h
  unfold memCheck
  have hp := permOK_unpack h1 h3
  have hi := invOK_unpack h1 h2 h3
  unfold tP at hp hi ⊢
  have hin := inP_tab h1 h4
  unfold tP at hin
  rw [hp, invT_unpack (by norm_num) h3, hi, hin, commTT_unpack h1 hy]
  unfold pc at h5
  rw [h5]
  rfl

theorem gen_of {P I : Nat} (hP : cK P = true) (hI : cK I = true)
    (h : invEqK 820 10 (mask 10) (820 * 10) P I = true) :
    (permOK 820 (tP P) && invOK 820 (tP P) (invT 820 (tP P))) = true := by
  unfold tP
  rw [permOK_unpack hP h, invT_unpack (by norm_num) h, invOK_unpack hP hI h]
  rfl

theorem comm_tab {i j : Nat} (hi : inK 0 i = true ∨ inK 6 i = true)
    (hj : inK 0 j = true ∨ inK 6 j = true) :
    commTab (tP (U43KP i)) (tP (U43KP j)) = tP (cm i j) ∧ cK (cm i j) = true := by
  have fi : cK (U43KP i) = true ∧ cK (U43KI i) = true ∧
      invEqK 820 10 (mask 10) (820 * 10) (U43KP i) (U43KI i) = true := by
    rcases hi with h | h <;> exact ⟨(inK_facts h).1, (inK_facts h).2.1, (inK_facts h).2.2.1⟩
  have fj : cK (U43KP j) = true ∧ cK (U43KI j) = true ∧
      invEqK 820 10 (mask 10) (820 * 10) (U43KP j) (U43KI j) = true := by
    rcases hj with h | h <;> exact ⟨(inK_facts h).1, (inK_facts h).2.1, (inK_facts h).2.2.1⟩
  unfold commTab tP cm pc
  rw [invT_unpack (by norm_num) fi.2.2, invT_unpack (by norm_num) fj.2.2,
    compT_unpack fi.1 fj.1, compT_unpack fi.2.1 fj.2.1,
    compT_unpack (canonK_pcomp fi.1 fj.1) (canonK_pcomp fi.2.1 fj.2.1)]
  exact ⟨rfl, canonK_pcomp (canonK_pcomp fi.1 fj.1) (canonK_pcomp fi.2.1 fj.2.1)⟩

theorem cube_tab {i : Nat} (hi : inK 0 i = true ∨ inK 6 i = true) :
    cubeTab (tP (U43KP i)) = tP (cb i) := by
  have fi : cK (U43KP i) = true := by rcases hi with h | h <;> exact (inK_facts h).1
  unfold cubeTab tP cb pc
  rw [compT_unpack fi fi, compT_unpack fi (canonK_pcomp fi fi)]

theorem ins : cK (U43KP 0) = true ∧ cK (U43KP 6) = true ∧
    invEqK 820 10 (mask 10) (820 * 10) (U43KP 0) (U43KI 0) = true ∧
    invEqK 820 10 (mask 10) (820 * 10) (U43KP 6) (U43KI 6) = true ∧
    (∀ k < 5, inK 0 (k + 1) = true) ∧ ∀ k < 7, inK 6 (k + 7) = true := by
  have h := in_ok
  simp only [bAnd_iff] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun k hk => allN_spec h.2.2.2.2.1 k hk,
    fun k hk => allN_spec h.2.2.2.2.2 k hk⟩

theorem tabs_eq : yBTab = tP (U43KP 0) ∧ (kB1a.map UInt32.ofNat) = tP (U43KP 1) ∧
    (kB1b.map UInt32.ofNat) = tP (U43KP 2) ∧ (kB2p.map UInt32.ofNat) = tP (U43KP 3) ∧
    (kB3a.map UInt32.ofNat) = tP (U43KP 4) ∧ (kB3b.map UInt32.ofNat) = tP (U43KP 5) ∧
    yCTab = tP (U43KP 6) ∧ (kC1a.map UInt32.ofNat) = tP (U43KP 7) ∧
    (kC1b.map UInt32.ofNat) = tP (U43KP 8) ∧ (kC2p.map UInt32.ofNat) = tP (U43KP 9) ∧
    (kC3a.map UInt32.ofNat) = tP (U43KP 10) ∧ (kC3b.map UInt32.ofNat) = tP (U43KP 11) ∧
    (kC4a.map UInt32.ofNat) = tP (U43KP 12) ∧ (kC4b.map UInt32.ofNat) = tP (U43KP 13) := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩ := bind_ok
  unfold yBTab yCTab tP
  rw [← eq_unpack_of_bindListK b0, ← eq_unpack_of_bindListK b1, ← eq_unpack_of_bindListK b2,
    ← eq_unpack_of_bindListK b3, ← eq_unpack_of_bindListK b4, ← eq_unpack_of_bindListK b5,
    ← eq_unpack_of_bindListK b6, ← eq_unpack_of_bindListK b7, ← eq_unpack_of_bindListK b8,
    ← eq_unpack_of_bindListK b9, ← eq_unpack_of_bindListK b10, ← eq_unpack_of_bindListK b11,
    ← eq_unpack_of_bindListK b12, ← eq_unpack_of_bindListK b13]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem iB {k : Nat} (h1 : 1 ≤ k) (h5 : k ≤ 5) : inK 0 k = true := by
  have := ins.2.2.2.2.1 (k - 1) (by omega)
  rwa [Nat.sub_add_cancel h1] at this

theorem iC {k : Nat} (h1 : 7 ≤ k) (h5 : k ≤ 13) : inK 6 k = true := by
  have := ins.2.2.2.2.2 (k - 7) (by omega)
  rwa [Nat.sub_add_cancel h1] at this

theorem kB_eq : kTabs yBTab kBComm kBCube = #[tP (gB 0), tP (gB 1), tP (gB 2), tP (gB 3)] := by
  obtain ⟨t0, t1, t2, t3, t4, t5, -⟩ := tabs_eq
  unfold kTabs kBComm kBCube
  rw [t0, t1, t2, t3, t4, t5]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rw [(comm_tab (.inl (iB (k := 1) le_rfl (by norm_num)))
    (.inl (iB (k := 2) (by norm_num) (by norm_num)))).1,
    (comm_tab (.inl (iB (k := 4) (by norm_num) (by norm_num)))
      (.inl (iB (k := 5) (by norm_num) le_rfl))).1,
    cube_tab (.inl (iB (k := 3) (by norm_num) (by norm_num)))]
  rfl

theorem genB {j : Nat} (hj : j < 4) : U43KB.GI j = gB j ∧ U43KB.G j = pidn 820 10 ∧
    cK (U43KB.GI j) = true ∧ cK (U43KBI j) = true ∧
    invEqK 820 10 (mask 10) (820 * 10) (U43KB.GI j) (U43KBI j) = true := by
  have h := allN_spec base.2.2.2.1 j hj
  simp only [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem b_tabs : TabsOK 820 10 4 U43KB.GI (kTabs yBTab kBComm kBCube) := by
  rw [kB_eq]
  refine ⟨rfl, fun j hj => ⟨?_, (genB hj).2.2.1⟩⟩
  rw [(genB hj).1]
  interval_cases j <;> rfl

theorem kRepB : kRepCheck yBTab kBComm kBCube = true := by
  have hcnt : U43KB.cnt = 324 := Nat.eq_of_beq_eq_true base.2.2.2.2.2.1
  have pe : ∀ i < U43KB.cnt, penumPtK 820 10 (mask 10) (820 * 10) true U43KB.G U43KB.GI 4
      U43KB.cnt U43KB.T U43KB.PL U43KB.POS U43KB.SRT U43KB.SRI i = true :=
    fun i hi => penumSl_spec bE i (Nat.zero_le _) (by omega) hi
  have hs : ∀ i < U43KB.cnt, hsortPtK 820 10 (mask 10) U43KB.cnt U43KB.T U43KB.HS U43KB.HSI i =
      true := fun i hi => slK_spec bH i (Nat.zero_le _) (by omega) hi
  obtain ⟨e, ht, hd⟩ := mulH_sound base.1 (fun j hj => (genB hj).2.1) b_tabs base.2.2.2.2.2.2.2.1
    pe hs
  have hT : ∀ i < U43KB.cnt, canonK 820 10 (mask 10) (820 * 10) (U43KB.T i) = true :=
    fun i hi => penumPt_canon (pe i hi)
  have hcl : ∀ c < U43KB.cnt * (4 + 4), findPtK U43KB.cnt U43KB.T
      (prodQK 820 10 (mask 10) (4 + 4) U43KB.T (bothK 4 U43KB.GI U43KBI)) U43KBCl c = true :=
    fun c hc => slK_spec bCl c (Nat.zero_le _) (by change c < Nat.mul U43KB.cnt 8; omega)
      (by change c < Nat.mul U43KB.cnt 8; omega)
  have hinv : ∀ j < 4, invEqK 820 10 (mask 10) (820 * 10) (U43KB.GI j) (U43KBI j) = true ∧
      canonK 820 10 (mask 10) (820 * 10) (U43KBI j) = true :=
    fun j hj => ⟨(genB hj).2.2.2.2, (genB hj).2.2.2.1⟩
  have hgens : (kTabs yBTab kBComm kBCube).all
      (fun x => permOK 820 x && invOK 820 x (invT 820 x)) = true := by
    rw [Array.all_eq_true]
    intro j hj
    have hj' : j < 4 := by rw [b_tabs.1] at hj; exact hj
    obtain ⟨hg, hc⟩ := b_tabs.2 j hj'
    rw [← getElem!_pos _ j hj, hg]
    exact gen_of hc (genB hj').2.2.2.1 (genB hj').2.2.2.2
  obtain ⟨t0, t1, t2, t3, t4, t5, -⟩ := tabs_eq
  unfold kRepCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  have hk : kCap = 400 := rfl
  rw [hk, e]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, hgens⟩, ht⟩, closedOK_of hT (TabsOK_both b_tabs hinv) hcl⟩, hd⟩, ?_⟩
  · rw [t0]
    exact permOK_unpack ins.1 ins.2.2.1
  · unfold kBComm
    rw [t0, t1, t2, t4, t5]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [mem_of ins.1 (iB le_rfl (by norm_num)), mem_of ins.1 (iB (by norm_num) (by norm_num)),
      mem_of ins.1 (iB (by norm_num) (by norm_num)), mem_of ins.1 (iB (by norm_num) le_rfl)]
    rfl
  · unfold kBCube
    rw [t0, t3]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    exact mem_of ins.1 (iB (by norm_num) (by norm_num))
  · rw [hRec_size, hcnt]

theorem kC_eq : kTabs yCTab kCComm kCCube =
    #[tP (gC 0), tP (gC 1), tP (gC 2), tP (gC 3), tP (gC 4)] := by
  obtain ⟨-, -, -, -, -, -, t6, t7, t8, t9, t10, t11, t12, t13⟩ := tabs_eq
  unfold kTabs kCComm kCCube
  rw [t6, t7, t8, t9, t10, t11, t12, t13]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rw [
    (comm_tab (.inr (iC (k := 7) le_rfl (by norm_num)))
      (.inr (iC (k := 8) (by norm_num) (by norm_num)))).1,
    (comm_tab (.inr (iC (k := 10) (by norm_num) (by norm_num)))
      (.inr (iC (k := 11) (by norm_num) (by norm_num)))).1,
    (comm_tab (.inr (iC (k := 12) (by norm_num) (by norm_num)))
      (.inr (iC (k := 13) (by norm_num) le_rfl))).1,
    cube_tab (.inr (iC (k := 9) (by norm_num) (by norm_num)))]
  rfl

theorem genC {j : Nat} (hj : j < 5) : U43KC.GI j = gC j ∧ U43KC.G j = pidn 820 10 ∧
    cK (U43KC.GI j) = true ∧ cK (U43KCI j) = true ∧
    invEqK 820 10 (mask 10) (820 * 10) (U43KC.GI j) (U43KCI j) = true := by
  have h := allN_spec base.2.2.2.2.1 j hj
  simp only [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem c_tabs : TabsOK 820 10 5 U43KC.GI (kTabs yCTab kCComm kCCube) := by
  rw [kC_eq]
  refine ⟨rfl, fun j hj => ⟨?_, (genC hj).2.2.1⟩⟩
  rw [(genC hj).1]
  interval_cases j <;> rfl

theorem kRepC : kRepCheck yCTab kCComm kCCube = true := by
  have hcnt : U43KC.cnt = 324 := Nat.eq_of_beq_eq_true base.2.2.2.2.2.2.1
  have pe : ∀ i < U43KC.cnt, penumPtK 820 10 (mask 10) (820 * 10) true U43KC.G U43KC.GI 5
      U43KC.cnt U43KC.T U43KC.PL U43KC.POS U43KC.SRT U43KC.SRI i = true :=
    fun i hi => penumSl_spec cE i (Nat.zero_le _) (by omega) hi
  have hs : ∀ i < U43KC.cnt, hsortPtK 820 10 (mask 10) U43KC.cnt U43KC.T U43KC.HS U43KC.HSI i =
      true := fun i hi => slK_spec cH i (Nat.zero_le _) (by omega) hi
  obtain ⟨e, ht, hd⟩ := mulH_sound base.1 (fun j hj => (genC hj).2.1) c_tabs
    base.2.2.2.2.2.2.2.2 pe hs
  have hT : ∀ i < U43KC.cnt, canonK 820 10 (mask 10) (820 * 10) (U43KC.T i) = true :=
    fun i hi => penumPt_canon (pe i hi)
  have hcl : ∀ c < U43KC.cnt * (5 + 5), findPtK U43KC.cnt U43KC.T
      (prodQK 820 10 (mask 10) (5 + 5) U43KC.T (bothK 5 U43KC.GI U43KCI)) U43KCCl c = true :=
    fun c hc => slK_spec cCl c (Nat.zero_le _) (by change c < Nat.mul U43KC.cnt 10; omega)
      (by change c < Nat.mul U43KC.cnt 10; omega)
  have hinv : ∀ j < 5, invEqK 820 10 (mask 10) (820 * 10) (U43KC.GI j) (U43KCI j) = true ∧
      canonK 820 10 (mask 10) (820 * 10) (U43KCI j) = true :=
    fun j hj => ⟨(genC hj).2.2.2.2, (genC hj).2.2.2.1⟩
  have hgens : (kTabs yCTab kCComm kCCube).all
      (fun x => permOK 820 x && invOK 820 x (invT 820 x)) = true := by
    rw [Array.all_eq_true]
    intro j hj
    have hj' : j < 5 := by rw [c_tabs.1] at hj; exact hj
    obtain ⟨hg, hc⟩ := c_tabs.2 j hj'
    rw [← getElem!_pos _ j hj, hg]
    exact gen_of hc (genC hj').2.2.2.1 (genC hj').2.2.2.2
  obtain ⟨-, -, -, -, -, -, t6, t7, t8, t9, t10, t11, t12, t13⟩ := tabs_eq
  unfold kRepCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  have hk : kCap = 400 := rfl
  rw [hk, e]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, hgens⟩, ht⟩, closedOK_of hT (TabsOK_both c_tabs hinv) hcl⟩, hd⟩, ?_⟩
  · rw [t6]
    exact permOK_unpack ins.2.1 ins.2.2.2.1
  · unfold kCComm
    rw [t6, t7, t8, t10, t11, t12, t13]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [mem_of ins.2.1 (iC le_rfl (by norm_num)), mem_of ins.2.1 (iC (by norm_num) (by norm_num)),
      mem_of ins.2.1 (iC (by norm_num) (by norm_num)),
      mem_of ins.2.1 (iC (by norm_num) (by norm_num)),
      mem_of ins.2.1 (iC (by norm_num) (by norm_num)), mem_of ins.2.1 (iC (by norm_num) le_rfl)]
    rfl
  · unfold kCCube
    rw [t6, t9]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    exact mem_of ins.2.1 (iC (by norm_num) (by norm_num))
  · rw [hRec_size, hcnt]

theorem facts27272 : kCheck = true := by
  unfold kCheck
  rw [kRepB, kRepC]
  rfl

end CertificateChecks.KernelSpor.U43CoverK

end

module

public import Certificates.Kernel.Sporadic.OddCore.J2BetaA5
public import Certificates.Kernel.Sporadic.OddCore.J3BetaA5F
public import Certificates.Kernel.Sporadic.OddCore.J2CnF
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.RuInvHash

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2BetaA5

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.EvenSporadicStandard.HypOne
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CertificateChecks.KernelSpor.J3BetaA5 (natArr_get hkey_inj_of idxTH_of memTH_of treeImgN_eq)

local notation "⟪" x "⟫" => tabT (unpack 315 9 x)

theorem permOK_of_pK {x : Table} (h : pK x = true) :
    CFSG.Sporadic.SmallOddCore.permOK 5 x = true := by
  unfold CFSG.Sporadic.SmallOddCore.permOK CFSG.Monster.B.Co2.Native.isInvA
  rw [CFSG.KC.Misc.RuInv.P.invCand_eq_foldl, allLt_iff']
  intro i hi
  unfold pK invL5 at h
  rw [List.all_eq_true] at h
  have := h i (List.mem_range.2 hi)
  simpa only [natArr_get] using this

theorem tblEq5_eq (x y : Table) : tblEq 5 x y = eq5 x y := by
  unfold tblEq eq5
  rw [Bool.eq_iff_iff, CFSG.KS.TW.allIn_iff, List.all_eq_true]
  simp only [List.mem_range]

theorem base : szOK 315 9 = true ∧ S16J2.cK (pidn 315 9) = true ∧
    CFSG.KS.Prim.idK 315 9 (mask 9) = true ∧ S16J2.cK (J2BetaT.F 0) = true ∧
    S16J2.cK (J2BAI 2) = true ∧
    invEqK 315 9 (mask 9) (315 * 9) (J2BetaT.F 0) (J2BAI 2) = true ∧
    allN 2 (fun j => bAnd(S16J2.cK (J2BA.GI j), bAnd(S16J2.cK (J2BAI j),
      bAnd(invEqK 315 9 (mask 9) (315 * 9) (J2BA.GI j) (J2BAI j),
      bAnd(Nat.beq (J2BA.GI j) (J2BetaT.F (Nat.add j 5)), bAnd(Nat.beq (J2BA.G j) (pidn 315 9),
      Nat.beq (J2Cn.pc (J2BetaT.F 0) (J2BA.GI j)) (J2Cn.pc (J2BA.GI j) (J2BetaT.F 0)))))))) =
        true ∧
    Nat.beq (J2BetaT.F 6) (J2BetaT.F 7) = true ∧ Nat.beq (J2BetaT.F 0) (J2BetaT.F 8) = true ∧
    Nat.beq J2BA.cnt 60 = true ∧ penumHdK (pidn 315 9) J2BA.cnt 100 J2BA.T J2BA.PL = true := by
  simpa only [bAnd_iff] using base_ok

theorem hcnt : J2BA.cnt = 60 := Nat.eq_of_beq_eq_true base.2.2.2.2.2.2.2.2.2.1

theorem hidc : canonK 315 9 (mask 9) (315 * 9) (pidn 315 9) = true := base.2.1

theorem hid : idT 315 = ⟪pidn 315 9⟫ := by
  rw [idT_tabT, idK_sound base.2.2.1]

theorem gen {j : ℕ} (hj : j < 2) : S16J2.cK (J2BA.GI j) = true ∧ S16J2.cK (J2BAI j) = true ∧
    invEqK 315 9 (mask 9) (315 * 9) (J2BA.GI j) (J2BAI j) = true ∧
    J2BA.GI j = J2BetaT.F (j + 5) ∧ J2BA.G j = pidn 315 9 ∧
    pcomp 315 9 (mask 9) (J2BetaT.F 0) (J2BA.GI j) =
      pcomp 315 9 (mask 9) (J2BA.GI j) (J2BetaT.F 0) := by
  have h := allN_spec base.2.2.2.2.2.2.1 j hj
  simp only [bAnd_iff] at h
  exact ⟨h.1, h.2.1, h.2.2.1, Nat.eq_of_beq_eq_true h.2.2.2.1,
    Nat.eq_of_beq_eq_true h.2.2.2.2.1, Nat.eq_of_beq_eq_true h.2.2.2.2.2⟩

theorem beta_tab {k : ℕ} (hk : k < 13) : j2BetaTbl k = ⟪J2BetaT.F k⟫ := by
  have h : natArr (j2BetaTbl k) = unpack 315 9 (J2BetaT.F k) := by
    have h := CFSG.KC.Misc.HexFlat.hexT_sound J2BetaT.all (by norm_num) k hk
    rw [← J2BetaT.eq] at h
    exact h
  rw [← tabT_natArr (j2BetaTbl k), h]

@[expose] noncomputable def gensK : Array Table := #[⟪J2BA.GI 0⟫, ⟪J2BA.GI 1⟫]

theorem gens_eq : #[j2BetaTbl 5, j2BetaTbl 6] = gensK := by
  rw [beta_tab (by norm_num), beta_tab (by norm_num), ← (gen (j := 0) (by norm_num)).2.2.2.1,
    ← (gen (j := 1) (by norm_num)).2.2.2.1]
  rfl

theorem s_tabs : TabsOK 315 9 2 J2BA.GI gensK := by
  refine ⟨rfl, fun j hj => ⟨?_, (gen hj).1⟩⟩
  interval_cases j <;> (rw [getElem!_pos _ _ (by simp [gensK])]; simp [gensK])

theorem s_pe : ∀ i < J2BA.cnt, penumPtK 315 9 (mask 9) (315 * 9) true J2BA.G J2BA.GI 2
    J2BA.cnt J2BA.T J2BA.PL J2BA.POS J2BA.SRT J2BA.SRI i = true :=
  fun i hi => penumSl_spec sE i (Nat.zero_le _) (by omega) hi

theorem s_hs : ∀ i < J2BA.cnt,
    hsortPtK 315 9 (mask 9) J2BA.cnt J2BA.T J2BA.HS J2BA.HSI i = true :=
  fun i hi => slK_spec sH i (Nat.zero_le _) (by omega) hi

theorem s_cl : ∀ c < J2BA.cnt * 4, findPtK J2BA.cnt J2BA.T
    (prodQK 315 9 (mask 9) 4 J2BA.T (bothK 2 J2BA.GI J2BAI)) J2BACl c = true :=
  fun c hc => slK_spec sCl c (Nat.zero_le _) (by change c < Nat.mul J2BA.cnt 4; omega)
    (by change c < Nat.mul J2BA.cnt 4; omega)

theorem mul_eq : mulClosureH 315 gensK 100 = hRec 315 9 J2BA.cnt J2BA.T J2BA.PL ∧
    mulTreeOK 315 gensK (hRec 315 9 J2BA.cnt J2BA.T J2BA.PL).1
      (hRec 315 9 J2BA.cnt J2BA.T J2BA.PL).2.1 (hRec 315 9 J2BA.cnt J2BA.T J2BA.PL).2.2 =
        true ∧
    hkeysDistinct 315 (hRec 315 9 J2BA.cnt J2BA.T J2BA.PL).1.toList = true :=
  mulH_sound base.1 (fun j hj => (gen hj).2.2.2.2.1) s_tabs base.2.2.2.2.2.2.2.2.2.2 s_pe s_hs

theorem hT {i : ℕ} (hi : i < 60) : canonK 315 9 (mask 9) (315 * 9) (J2BA.T i) = true :=
  penumPt_canon (s_pe i (by rw [hcnt]; exact hi))

@[expose] noncomputable def LK : Array Table := (hRec 315 9 60 J2BA.T J2BA.PL).1

theorem LK_size : LK.size = 60 := hRec_size _ _ _ _ _

theorem LK_get {i : ℕ} (hi : i < 60) : LK[i]! = ⟪J2BA.T i⟫ := hRec_get hi

theorem mul_eq' : mulClosureH 315 gensK 100 = hRec 315 9 60 J2BA.T J2BA.PL := by
  rw [← hcnt]
  exact mul_eq.1

theorem LK_inj : ∀ a < LK.size, ∀ b < LK.size, hkey 315 LK[a]! = hkey 315 LK[b]! → a = b := by
  have h := mul_eq.2.2
  rw [hcnt] at h
  exact hkey_inj_of h

theorem prod_entry {k l : ℕ} (hk : k < 60) (hl : l < 4) :
    r32 J2BACl (k * 4 + l) < 60 ∧
      compT 315 LK[k]! (gensK ++ gensK.map (invT 315))[l]! = LK[r32 J2BACl (k * 4 + l)]! := by
  have hb := TabsOK_both s_tabs (fun j hj => ⟨(gen hj).2.2.1, (gen hj).2.1⟩)
  obtain ⟨hgj, hcj⟩ := hb.2 l hl
  have hc : k * 4 + l < J2BA.cnt * 4 := by rw [hcnt]; omega
  obtain ⟨hq, he⟩ := findPt_spec (s_cl _ hc)
  unfold prodQK at he
  obtain ⟨e1, e2⟩ := div_mod_pair (i := k) hl
  change r32 J2BACl (k * 4 + l) < J2BA.cnt at hq
  rw [show Nat.div (k * 4 + l) 4 = k from e1, show Nat.mod (k * 4 + l) 4 = l from e2] at he
  rw [hcnt] at hq
  refine ⟨hq, ?_⟩
  rw [LK_get hk, hgj, compT_unpack (hT hk) hcj, ← he, LK_get hq]

theorem himg : treeImgN 5 piA5J2 (hRec 315 9 60 J2BA.T J2BA.PL).2.1
    (hRec 315 9 60 J2BA.T J2BA.PL).2.2 LK.size = imgK := by
  rw [treeImgN_eq, LK_size]
  rfl

theorem cay : imgK.size = 60 ∧ imgK.toList.all pK = true ∧ eq5 imgK[0]! (idT 5) = true ∧
    (∀ k < 60, ∀ l < 2, Nat.blt (r32 J2BACl (4 * k + l)) 60 = true ∧
      eq5 imgK[r32 J2BACl (4 * k + l)]! (compT 5 imgK[k]! piA5J2[l]!) = true) ∧
    (∀ k < 60, (eq5 imgK[k]! (idT 5) == Nat.beq (J2BA.T k) (pidn 315 9)) = true) ∧
    piA5J2.toList.all pK = true := by
  have hc := cay_ok
  unfold cayK at hc
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩ := hc
  refine ⟨c1, List.all_eq_true.2 c2, c3, fun k hk l hl => c4 k hk l hl, fun k hk => ?_,
    List.all_eq_true.2 c6⟩
  rw [beq_iff_eq]
  exact c5 k hk

theorem facts24604a : j2A5OK = true := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := cay
  unfold j2A5OK a5HomCheck
  dsimp only
  rw [gens_eq, mul_eq', beta_tab (k := 0) (by norm_num)]
  rw [show (hRec 315 9 60 J2BA.T J2BA.PL).1 = LK from rfl, himg]
  simp only [Bool.and_eq_true]
  have c0 := base.2.2.2.1
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, rfl⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← Array.all_toList]
    simp only [gensK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact permOK_unpack (gen (j := 0) (by norm_num)).1 (gen (j := 0) (by norm_num)).2.2.1
    · rw [invT_unpack (by norm_num) (gen (j := 0) (by norm_num)).2.2.1]
      exact invOK_unpack (gen (j := 0) (by norm_num)).1 (gen (j := 0) (by norm_num)).2.1
        (gen (j := 0) (by norm_num)).2.2.1
    · exact permOK_unpack (gen (j := 1) (by norm_num)).1 (gen (j := 1) (by norm_num)).2.2.1
    · rw [invT_unpack (by norm_num) (gen (j := 1) (by norm_num)).2.2.1]
      exact invOK_unpack (gen (j := 1) (by norm_num)).1 (gen (j := 1) (by norm_num)).2.1
        (gen (j := 1) (by norm_num)).2.2.1
  · exact permOK_unpack c0 base.2.2.2.2.2.1
  · rw [← Array.all_toList, List.all_eq_true]
    exact fun x hx => permOK_of_pK (List.all_eq_true.1 c6 x hx)
  · rw [← Array.all_toList]
    simp only [gensK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [commTT_unpack c0 (gen (j := 0) (by norm_num)).1, (gen (j := 0) (by norm_num)).2.2.2.2.2]
      exact Nat.beq_refl _
    · rw [commTT_unpack c0 (gen (j := 1) (by norm_num)).1, (gen (j := 1) (by norm_num)).2.2.2.2.2]
      exact Nat.beq_refl _
  · have h := mul_eq.2.1
    rw [hcnt] at h
    exact h
  · have h := mul_eq.2.2
    rw [hcnt] at h
    exact h
  · unfold closedOKH
    rw [Array.all_eq_true]
    intro i hi
    rw [Array.all_eq_true]
    intro l hl
    have hi' : i < 60 := by rw [← LK_size]; exact hi
    have hl' : l < 4 := by simpa [s_tabs.1] using hl
    obtain ⟨hq, he⟩ := prod_entry hi' hl'
    rw [← getElem!_pos LK i hi, ← getElem!_pos _ l hl, he]
    exact memTH_of LK_inj (by rw [LK_size]; exact hq) (by rw [LK_get hq]; exact tblEq_self (hT hq))
  · rw [LK_size]
    rfl
  · rw [c1, LK_size]
    rfl
  · rw [← Array.all_toList, List.all_eq_true]
    exact fun x hx => permOK_of_pK (List.all_eq_true.1 c2 x hx)
  · rw [tblEq5_eq]
    exact c3
  · rw [LK_size, List.all_eq_true]
    intro k hk
    rw [List.all_eq_true]
    intro l hl
    have hk' := List.mem_range.1 hk
    have hl' := List.mem_range.1 hl
    obtain ⟨hq, he⟩ := prod_entry hk' (l := l) (by omega)
    have hg : (gensK ++ gensK.map (invT 315))[l]! = gensK[l]! := by
      rw [getElem!_pos _ l (by simp [s_tabs.1]; omega), getElem!_pos _ l (by rw [s_tabs.1]; omega),
        Array.getElem_append_left]
    rw [hg] at he
    rw [he, idxTH_of LK_inj (by rw [LK_size]; exact hq) (by rw [LK_get hq]; exact tblEq_self (hT hq)),
      tblEq5_eq, Nat.mul_comm k 4]
    obtain ⟨d1, d2⟩ := c4 k hk' l hl'
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Nat.le_of_ble_eq_true d1, d2⟩
  · rw [LK_size, List.all_eq_true]
    intro k hk
    have hk' := List.mem_range.1 hk
    rw [tblEq5_eq, LK_get hk', hid, tblEq_unpack (hT hk') hidc]
    exact c5 k hk'

theorem facts24604b : j2A5MemOK = true := by
  have g0 := gen (j := 0) (by norm_num)
  have g1 := gen (j := 1) (by norm_num)
  have c5 : canonK 315 9 (mask 9) (315 * 9) (J2BetaT.F 5) = true := by rw [← g0.2.2.2.1]; exact g0.1
  have c6 : canonK 315 9 (mask 9) (315 * 9) (J2BetaT.F 6) = true := by rw [← g1.2.2.2.1]; exact g1.1
  have hs := sift_ok
  simp only [bAnd_iff] at hs
  unfold j2A5MemOK
  rw [beta_tab (k := 5) (by norm_num), beta_tab (k := 6) (by norm_num),
    beta_tab (k := 7) (by norm_num), beta_tab (k := 0) (by norm_num),
    beta_tab (k := 8) (by norm_num), J2Cn.sift_eq c5, J2Cn.sift_eq c6]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨hs.1, hs.2⟩, ?_⟩, ?_⟩
  · rw [← Nat.eq_of_beq_eq_true base.2.2.2.2.2.2.2.1]
    exact tblEq_self c6
  · rw [← Nat.eq_of_beq_eq_true base.2.2.2.2.2.2.2.2.1]
    exact tblEq_self base.2.2.2.1

end CertificateChecks.KernelSpor.J2BetaA5

end

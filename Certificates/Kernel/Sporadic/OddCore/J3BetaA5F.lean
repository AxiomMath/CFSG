module

public import Certificates.Kernel.Sporadic.OddCore.J3BetaA5Img
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import Certificates.Kernel.SporSch.J3K426.Sift
public import CFSG.Certificates.Kernel.Spor.ClassOneH
public import CFSG.Certificates.Kernel.Spor.JoinSound
public import CFSG.Certificates.Kernel.Spor.MulHFSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3BetaA5

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.EvenSporadicStandard.HypOne
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.KS.Join CertificateChecks.KernelSporSch

theorem treeImgN_eq (k : ℕ) (pg : Array Table) (par lab : Array ℕ) (m : ℕ) :
    treeImgN k pg par lab m = (List.range' 1 (m - 1)).foldl
      (fun r j => r.push (compT k r[par[j]!]! pg[lab[j]!]!)) #[idT k] := by
  unfold treeImgN
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.div_one,
    Nat.add_sub_cancel, List.forIn_pure_yield_eq_foldl, bind_pure]
  rfl

theorem natArr_get (x : Table) (i : ℕ) : (natArr x)[i]! = (x[i]!).toNat := by
  unfold natArr
  by_cases h : i < x.size
  · rw [getElem!_pos _ i (by simpa using h), getElem!_pos x i h, Array.getElem_map]
  · rw [getElem!_neg _ i (by simpa using h), getElem!_neg x i h]
    rfl

theorem permOK_of_pK {x : Table} (h : pK x = true) :
    CFSG.Sporadic.SmallOddCore.permOK 5 x = true := by
  unfold CFSG.Sporadic.SmallOddCore.permOK CFSG.Monster.B.Co2.Native.isInvA
  rw [CFSG.KC.Misc.RuInv.P.invCand_eq_foldl, allLt_iff']
  intro i hi
  unfold pK invL5 at h
  rw [List.all_eq_true] at h
  have := h i (List.mem_range.2 hi)
  simpa only [natArr_get] using this

theorem hkey_inj_of {n : ℕ} {L : Array Table} (hk : hkeysDistinct n L.toList = true) :
    ∀ a < L.size, ∀ b < L.size, hkey n L[a]! = hkey n L[b]! → a = b := by
  have hsorted := (CFSG.Sporadic.Schreier.pairwise_of_strictlyIncreasing hk).imp
    (fun hab => Nat.ne_of_lt hab)
  have hkeys : (L.toList.map fun T => (hkey n T).toNat).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.1 hsorted
  intro a ha b hb e
  have e' : (L.toList.map fun T => (hkey n T).toNat)[a]'(by simpa using ha) =
      (L.toList.map fun T => (hkey n T).toNat)[b]'(by simpa using hb) := by
    simp only [List.getElem_map, Array.getElem_toList]
    rw [← getElem!_pos L a ha, ← getElem!_pos L b hb, e]
  exact (List.Nodup.getElem_inj_iff hkeys).1 e'

theorem idxTH_of {n : ℕ} {L : Array Table}
    (hd : ∀ a < L.size, ∀ b < L.size, hkey n L[a]! = hkey n L[b]! → a = b) {j : ℕ}
    (hj : j < L.size) (hs : tblEq n L[j]! L[j]! = true) :
    idxTH n L (hashIndex n L) L[j]! = j := by
  have hs' : tblEq n L[j] L[j] = true := by rwa [getElem!_pos L j hj] at hs
  unfold idxTH
  rw [CFSG.KS.ClassOneH.hashIndex_get hd hj]
  simp [hj, hs']

theorem memTH_of {n : ℕ} {L : Array Table}
    (hd : ∀ a < L.size, ∀ b < L.size, hkey n L[a]! = hkey n L[b]! → a = b) {j : ℕ}
    (hj : j < L.size) (hs : tblEq n L[j]! L[j]! = true) :
    memTH n L (hashIndex n L) L[j]! = true := by
  have hs' : tblEq n L[j] L[j] = true := by rwa [getElem!_pos L j hj] at hs
  unfold memTH
  rw [CFSG.KS.ClassOneH.hashIndex_get hd hj]
  simp [hj, hs']

theorem base : szOK 6156 13 = true ∧ cK (pidn 6156 13) = true ∧
    CFSG.KS.Prim.idK 6156 13 (mask 13) = true ∧ cK (J3BetaP 0) = true ∧ cK (J3BetaI 2) = true ∧
    invEqK 6156 13 (mask 13) (6156 * 13) (J3BetaP 0) (J3BetaI 2) = true ∧
    allN 2 (fun j => bAnd(cK (J3BA.GI j), bAnd(cK (J3BetaI j),
      bAnd(invEqK 6156 13 (mask 13) (6156 * 13) (J3BA.GI j) (J3BetaI j),
      bAnd(Nat.beq (J3BA.GI j) (J3BetaP (Nat.add j 5)), bAnd(Nat.beq (J3BA.G j) (pidn 6156 13),
      Nat.beq (pc (J3BetaP 0) (J3BA.GI j)) (pc (J3BA.GI j) (J3BetaP 0)))))))) = true ∧
    Nat.beq (J3BetaP 6) (J3BetaP 7) = true ∧ Nat.beq (J3BetaP 0) (J3BetaP 8) = true ∧
    Nat.beq J3BA.cnt 60 = true ∧ penumHdK (pidn 6156 13) J3BA.cnt 100 J3BA.T J3BA.PL = true := by
  simpa only [bAnd_iff] using base_ok

theorem hcnt : J3BA.cnt = 60 := Nat.eq_of_beq_eq_true base.2.2.2.2.2.2.2.2.2.1

theorem hidc : canonK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13) = true := base.2.1

theorem hid : idT 6156 = tabT (unpack 6156 13 (pidn 6156 13)) := by
  rw [idT_tabT, idK_sound base.2.2.1]

theorem gen {j : ℕ} (hj : j < 2) : cK (J3BA.GI j) = true ∧ cK (J3BetaI j) = true ∧
    invEqK 6156 13 (mask 13) (6156 * 13) (J3BA.GI j) (J3BetaI j) = true ∧
    J3BA.GI j = J3BetaP (j + 5) ∧ J3BA.G j = pidn 6156 13 ∧
    pcomp 6156 13 (mask 13) (J3BetaP 0) (J3BA.GI j) =
      pcomp 6156 13 (mask 13) (J3BA.GI j) (J3BetaP 0) := by
  have h := allN_spec base.2.2.2.2.2.2.1 j hj
  simp only [bAnd_iff] at h
  exact ⟨h.1, h.2.1, h.2.2.1, Nat.eq_of_beq_eq_true h.2.2.2.1,
    Nat.eq_of_beq_eq_true h.2.2.2.2.1, Nat.eq_of_beq_eq_true h.2.2.2.2.2⟩

theorem beta_tab {k : ℕ} (hk : k < 13) : j3BetaTbl k = tabT (unpack 6156 13 (J3BetaP k)) := by
  have h := hexT_join_sound (d := 4) (n₀ := 513) (w := 13) (c := 12) (N := 13) J3BetaT.all
    beta_join (by norm_num) k hk
  rw [← J3BetaT.eq] at h
  rw [← tabT_natArr (j3BetaTbl k)]
  exact congrArg tabT h

@[expose] noncomputable def gensK : Array Table :=
  #[tabT (unpack 6156 13 (J3BA.GI 0)), tabT (unpack 6156 13 (J3BA.GI 1))]

theorem gens_eq : #[j3BetaTbl 5, j3BetaTbl 6] = gensK := by
  rw [beta_tab (by norm_num), beta_tab (by norm_num), ← (gen (j := 0) (by norm_num)).2.2.2.1,
    ← (gen (j := 1) (by norm_num)).2.2.2.1]
  rfl

theorem s_tabs : TabsOK 6156 13 2 J3BA.GI gensK := by
  refine ⟨rfl, fun j hj => ⟨?_, (gen hj).1⟩⟩
  interval_cases j <;> (rw [getElem!_pos _ _ (by simp [gensK])]; simp [gensK])

theorem s_pe : ∀ i < J3BA.cnt, penumPtK 6156 13 (mask 13) (6156 * 13) true J3BA.G J3BA.GI 2
    J3BA.cnt J3BA.T J3BA.PL J3BA.POS J3BA.SRT J3BA.SRI i = true :=
  fun i hi => penumSl_spec sE i (Nat.zero_le _) (by omega) hi

theorem s_hs : ∀ i < J3BA.cnt,
    hsortPtK 6156 13 (mask 13) J3BA.cnt J3BA.T J3BA.HS J3BA.HSI i = true := fun i hi => by
  rw [← hsortPtKF_eq 6156 13 J3BA.cnt J3BA.T J3BA.HS J3BA.HSI i]
  exact slK_spec sHF i (Nat.zero_le _) (by omega) hi

theorem s_cl : ∀ c < J3BA.cnt * 4, findPtK J3BA.cnt J3BA.T
    (prodQK 6156 13 (mask 13) 4 J3BA.T (bothK 2 J3BA.GI J3BetaI)) J3BACl c = true :=
  fun c hc => slK_spec sCl c (Nat.zero_le _) (by change c < Nat.mul J3BA.cnt 4; omega)
    (by change c < Nat.mul J3BA.cnt 4; omega)

theorem mul_eq : mulClosureH 6156 gensK 100 = hRec 6156 13 J3BA.cnt J3BA.T J3BA.PL ∧
    mulTreeOK 6156 gensK (hRec 6156 13 J3BA.cnt J3BA.T J3BA.PL).1
      (hRec 6156 13 J3BA.cnt J3BA.T J3BA.PL).2.1 (hRec 6156 13 J3BA.cnt J3BA.T J3BA.PL).2.2 =
        true ∧
    hkeysDistinct 6156 (hRec 6156 13 J3BA.cnt J3BA.T J3BA.PL).1.toList = true :=
  mulH_sound base.1 (fun j hj => (gen hj).2.2.2.2.1) s_tabs base.2.2.2.2.2.2.2.2.2.2 s_pe s_hs

theorem hT {i : ℕ} (hi : i < 60) : canonK 6156 13 (mask 13) (6156 * 13) (J3BA.T i) = true :=
  penumPt_canon (s_pe i (by rw [hcnt]; exact hi))

theorem tblEq5_eq (x y : Table) : tblEq 5 x y = eq5 x y := by
  unfold tblEq eq5
  rw [Bool.eq_iff_iff, CFSG.KS.TW.allIn_iff, List.all_eq_true]
  simp only [List.mem_range]

@[expose] noncomputable def LK : Array Table := (hRec 6156 13 60 J3BA.T J3BA.PL).1

theorem LK_size : LK.size = 60 := hRec_size _ _ _ _ _

theorem LK_get {i : ℕ} (hi : i < 60) : LK[i]! = tabT (unpack 6156 13 (J3BA.T i)) := hRec_get hi

theorem mul_eq' : mulClosureH 6156 gensK 100 = hRec 6156 13 60 J3BA.T J3BA.PL := by
  rw [← hcnt]
  exact mul_eq.1

theorem LK_inj : ∀ a < LK.size, ∀ b < LK.size, hkey 6156 LK[a]! = hkey 6156 LK[b]! → a = b := by
  have h := mul_eq.2.2
  rw [hcnt] at h
  exact hkey_inj_of h

theorem gensK_get {l : ℕ} (hl : l < 2) : gensK[l]! = tabT (unpack 6156 13 (J3BA.GI l)) :=
  (s_tabs.2 l hl).1

theorem prod_entry {k l : ℕ} (hk : k < 60) (hl : l < 4) :
    r32 J3BACl (k * 4 + l) < 60 ∧
      compT 6156 LK[k]! (gensK ++ gensK.map (invT 6156))[l]! = LK[r32 J3BACl (k * 4 + l)]! := by
  have hb := TabsOK_both s_tabs (fun j hj => ⟨(gen hj).2.2.1, (gen hj).2.1⟩)
  obtain ⟨hgj, hcj⟩ := hb.2 l hl
  have hc : k * 4 + l < J3BA.cnt * 4 := by rw [hcnt]; omega
  obtain ⟨hq, he⟩ := findPt_spec (s_cl _ hc)
  unfold prodQK at he
  obtain ⟨e1, e2⟩ := div_mod_pair (i := k) hl
  change r32 J3BACl (k * 4 + l) < J3BA.cnt at hq
  rw [show Nat.div (k * 4 + l) 4 = k from e1, show Nat.mod (k * 4 + l) 4 = l from e2] at he
  rw [hcnt] at hq
  refine ⟨hq, ?_⟩
  rw [LK_get hk, hgj, compT_unpack (hT hk) hcj, ← he, LK_get hq]

theorem himg : treeImgN 5 piA5J3 (hRec 6156 13 60 J3BA.T J3BA.PL).2.1
    (hRec 6156 13 60 J3BA.T J3BA.PL).2.2 LK.size = imgK := by
  rw [treeImgN_eq, LK_size]
  rfl

theorem cay : imgK.size = 60 ∧ imgK.toList.all pK = true ∧ eq5 imgK[0]! (idT 5) = true ∧
    (∀ k < 60, ∀ l < 2, Nat.blt (r32 J3BACl (4 * k + l)) 60 = true ∧
      eq5 imgK[r32 J3BACl (4 * k + l)]! (compT 5 imgK[k]! piA5J3[l]!) = true) ∧
    (∀ k < 60, (eq5 imgK[k]! (idT 5) == Nat.beq (J3BA.T k) (pidn 6156 13)) = true) ∧
    piA5J3.toList.all pK = true := by
  have hc := cay_ok
  unfold cayK at hc
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩ := hc
  refine ⟨c1, List.all_eq_true.2 c2, c3, fun k hk l hl => c4 k hk l hl, fun k hk => ?_,
    List.all_eq_true.2 c6⟩
  rw [beq_iff_eq]
  exact c5 k hk

theorem facts24605a : j3A5OK = true := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := cay
  unfold j3A5OK a5HomCheck
  dsimp only
  rw [gens_eq, mul_eq', beta_tab (k := 0) (by norm_num)]
  rw [show (hRec 6156 13 60 J3BA.T J3BA.PL).1 = LK from rfl, himg]
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
    have hg : (gensK ++ gensK.map (invT 6156))[l]! = gensK[l]! := by
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

theorem facts24605b : j3A5MemOK = true := by
  have g0 := gen (j := 0) (by norm_num)
  have g1 := gen (j := 1) (by norm_num)
  unfold j3A5MemOK
  rw [beta_tab (k := 5) (by norm_num), beta_tab (k := 6) (by norm_num),
    beta_tab (k := 7) (by norm_num), beta_tab (k := 0) (by norm_num),
    beta_tab (k := 8) (by norm_num)]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · unfold CFSG.Sporadic.SmallOddCore.j3Sift
    rw [natArr_tabT (by rw [← g0.2.2.2.1]; exact g0.1)]
    exact J3KT.sift_of a_word
  · unfold CFSG.Sporadic.SmallOddCore.j3Sift
    rw [natArr_tabT (by rw [← g1.2.2.2.1]; exact g1.1)]
    exact J3KT.sift_of b_word
  · rw [← Nat.eq_of_beq_eq_true base.2.2.2.2.2.2.2.1]
    exact tblEq_self (by rw [← g1.2.2.2.1]; exact g1.1)
  · rw [← Nat.eq_of_beq_eq_true base.2.2.2.2.2.2.2.2.1]
    exact tblEq_self base.2.2.2.1

end CertificateChecks.KernelSpor.J3BetaA5

end

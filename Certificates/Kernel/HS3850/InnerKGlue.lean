module

public import Certificates.Kernel.HS3850.InnerKSmall
public import Certificates.Kernel.HS3850.InnerKS0
public import Certificates.Kernel.HS3850.InnerKS1
public import Certificates.Kernel.HS3850.InnerKS2
public import Certificates.Kernel.HS3850.InnerKS3
public import Certificates.Kernel.HS3850.InnerKS4
public import Certificates.Kernel.HS3850.InnerKS5
public import Certificates.Kernel.HS3850.InnerKS6
public import Certificates.Kernel.HS3850.InnerKS7
public import Certificates.Kernel.HS3850.Facts25371
public import Certificates.Kernel.HS3850.FusFacts
public import Certificates.Kernel.HS3850.Kit
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.Certificates.Kernel.L34KSnd.Tab
public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN
open CFSG.KD.LQT.HN hiding Cn cIdn
open CFSG.KD.LQT.C4126 CFSG.KC.PkPow CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert
open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.KD.LQT.HO (Cn cIdn)
open CFSG.KD.HS3850 (comp_pc' cn_pc beq_pc' idTab_idn countP_nfix c1Enum_eq cnt_A canonA cperm
  sift_true_of_word cent_parts)

#kqb_all CertificateChecks.KernelHS3850.IK CertificateChecks.KernelHS3850.ckI 240

theorem itab_eq {k : Nat} (hk : k < 14) : itab k = unpack 3850 12 (IT.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound IT.all (by norm_num) k hk
  rw [← IT.eq] at h
  exact h

theorem inner_tab {k : Nat} (hk : k < 14) : innerTbl k = CFSG.KS.MulH.tabT (unpack 3850 12 (IT.F k)) := by
  rw [← itab_eq hk]
  exact (CFSG.KS.MulH.tabT_natArr (innerTbl k)).symm

theorem itPerm {k : Nat} (hk : k < 14) : Cn (IT.F k) ∧
    invEqK 3850 12 (mask 12) (3850 * 12) (IT.F k) (pinvS 3850 12 (mask 12) (IT.F k)) = true :=
  Bool.and_eq_true_iff.1 (allN_spec IK.perm k hk)

theorem cnI {k : Nat} (hk : k < 14) : Cn (IT.F k) := (itPerm hk).1

theorem giParts : Cn GI1 ∧ pc (IT.F 0) GI1 = idn ∧ pc GI1 (IT.F 0) = idn := by
  have h := IK.gi
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem tGi_eq : tGi = unpack 3850 12 GI1 := by
  unfold tGi tG
  rw [itab_eq (k := 0) (by norm_num)]
  exact CFSG.KC.L34KSnd.invTab_eq_of_pcomp (cnI (k := 0) (by norm_num)) giParts.1 giParts.2.1

theorem codeTab_c0 (g gi y : Tab) : codeTab g gi y 0 = g := rfl

theorem codeTab_c1 (g gi y : Tab) : codeTab g gi y 1 = gi := rfl

theorem codeTab_c2 (g gi y : Tab) (c : Nat) : codeTab g gi y (c + 2) = y := rfl

theorem nIf_c0 (a b y : Nat) : nIf(Nat.beq 0 (nat_lit 0), a, nIf(Nat.beq 0 (nat_lit 1), b, y)) = a :=
  rfl

theorem nIf_c1 (a b y : Nat) : nIf(Nat.beq 1 (nat_lit 0), a, nIf(Nat.beq 1 (nat_lit 1), b, y)) = b :=
  rfl

theorem nIf_c2 (a b y c : Nat) :
    nIf(Nat.beq (c + 2) (nat_lit 0), a, nIf(Nat.beq (c + 2) (nat_lit 1), b, y)) = y := rfl

theorem code_eq {Y : Nat} (hY : Cn Y) (c : Nat) :
    codeTab tG tGi (unpack 3850 12 Y) c = unpack 3850 12 (kCode Y c) ∧ Cn (kCode Y c) := by
  rcases c with _ | _ | c
  · have e : kCode Y 0 = IT.F 0 := by
      unfold kCode
      exact nIf_c0 (IT.F 0) GI1 Y
    rw [e, codeTab_c0]
    exact ⟨itab_eq (k := 0) (by norm_num), cnI (k := 0) (by norm_num)⟩
  · have e : kCode Y 1 = GI1 := by
      unfold kCode
      exact nIf_c1 (IT.F 0) GI1 Y
    rw [e, codeTab_c1]
    exact ⟨tGi_eq, giParts.1⟩
  · have e : kCode Y (c + 2) = Y := by
      unfold kCode
      exact nIf_c2 (IT.F 0) GI1 Y c
    rw [e, codeTab_c2]
    exact ⟨rfl, hY⟩

theorem wT_eq {Y : Nat} (hY : Cn Y) :
    ∀ w : List Nat, wT (unpack 3850 12 Y) w = unpack 3850 12 (kW Y w) ∧ Cn (kW Y w)
  | [] => ⟨idTab_idn, cIdn⟩
  | c :: w => by
    obtain ⟨h1, h2⟩ := wT_eq hY w
    obtain ⟨c1, c2⟩ := code_eq hY c
    have e : wT (unpack 3850 12 Y) (c :: w) =
        comp 3850 (codeTab tG tGi (unpack 3850 12 Y) c) (wT (unpack 3850 12 Y) w) := rfl
    rw [e, h1, c1, comp_pc' c2 h2]
    exact ⟨rfl, cn_pc c2 h2⟩

theorem fixN_eq (p : Nat) : fixN (unpack 3850 12 p) = nfix 3850 12 p := countP_nfix 3850 12 p

theorem isInv_eq {p : Nat} (hp : Cn p) : isInv (unpack 3850 12 p) = Nat.beq (pc p p) idn := by
  unfold isInv
  rw [comp_pc' hp hp, idTab_idn, beq_pc' (cn_pc hp hp) cIdn]

theorem comp_eq {p q : Nat} (hp : Cn p) (hq : Cn q) {r s : Nat} (hr : Cn r) (hs : Cn s) :
    (comp 3850 (unpack 3850 12 p) (unpack 3850 12 q) == comp 3850 (unpack 3850 12 r)
      (unpack 3850 12 s)) = Nat.beq (pc p q) (pc r s) := by
  rw [comp_pc' hp hq, comp_pc' hr hs, beq_pc' (cn_pc hp hq) (cn_pc hr hs)]

theorem pow5_eq {p : Nat} (hp : Cn p) : pow5 (unpack 3850 12 p) = unpack 3850 12 (p5K p) ∧
    Cn (p5K p) := by
  unfold pow5 p5K
  dsimp only
  rw [comp_pc' hp hp, comp_pc' (cn_pc hp hp) (cn_pc hp hp), comp_pc' (cn_pc (cn_pc hp hp) (cn_pc hp hp)) hp]
  exact ⟨rfl, cn_pc (cn_pc (cn_pc hp hp) (cn_pc hp hp)) hp⟩

theorem hPow_eq : ∀ k, hPow k = unpack 3850 12 (hpK k) ∧ Cn (hpK k)
  | 0 => ⟨idTab_idn, cIdn⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := hPow_eq k
    have c2 := cnI (k := 2) (by norm_num)
    have e : hPow (k + 1) = comp 3850 tH (hPow k) := rfl
    rw [e, h1]
    unfold tH
    rw [itab_eq (k := 2) (by norm_num), comp_pc' c2 h2]
    exact ⟨rfl, cn_pc c2 h2⟩

theorem bool_beq (a b : Bool) : (a == b) = Bool.beq a b := by cases a <;> cases b <;> rfl

theorem patOK_eq {Y : Nat} (hY : Cn Y) : patOK (unpack 3850 12 Y) = patK Y := by
  unfold patOK patK
  apply Bool.eq_iff_iff.2
  rw [List.all_eq_true, List.all_eq_true]
  refine forall_congr' fun p => forall_congr' fun _ => ?_
  obtain ⟨h1, h2⟩ := wT_eq hY p.1
  rw [h1, idTab_idn, beq_pc' h2 cIdn, bool_beq]

theorem c1Tabs_eq : c1Tabs = Array.ofFn (n := A.cnt) fun i => unpack 3850 12 (A.T i.val) := by
  rw [c1Tabs_def, c1Enum_eq]
  rfl

theorem c1_get {i : Nat} (hi : i < A.cnt) : c1Tabs[i]! = unpack 3850 12 (A.T i) := by
  rw [c1Tabs_eq, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem c1_size : c1Tabs.size = 7680 := by rw [c1Tabs_eq, Array.size_ofFn, cnt_A]

theorem inC1_of {t : Tab} {i : Nat} (hi : i < 7680) (h : c1Tabs[i]! = t) : inC1 t = true := by
  unfold inC1
  rw [Array.contains_iff]
  rw [← h, getElem!_pos _ i (by rw [c1_size]; exact hi)]
  exact Array.getElem_mem _

theorem memParts {j : Nat} (hj : j < 11) : MI j < 7680 ∧ A.T (MI j) = memT j := by
  have h := allN_spec IK.mem j hj
  rw [Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem inC1_mem {j k : Nat} (hj : j < 11) (hk : k < 14)
    (e : [0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13].getD j 0 = k) : inC1 (itab k) = true := by
  obtain ⟨h1, h2⟩ := memParts hj
  refine inC1_of h1 ?_
  rw [c1_get (by rw [cnt_A]; exact h1), h2, memT, e, itab_eq hk]

theorem siftParts : IT.F 9 = wfoldR ls8 SW9 ∧ IT.F 10 = wfoldR ls8 SW10 ∧ IT.F 11 = wfoldR ls8 SW11 := by
  have h := IK.sift
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem permI {k : Nat} (hk : k < 14) : CFSG.Sporadic.SmallOddCore.permOK 3850 (innerTbl k) = true := by
  rw [inner_tab hk]
  exact CFSG.KS.MulH.permOK_unpack (itPerm hk).1 (itPerm hk).2

theorem memOK_true :
    memOK = true := by
  obtain ⟨s9, s10, s11⟩ := siftParts
  have m : ∀ j (hj : j < 11) k (hk : k < 14), [0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13].getD j 0 = k →
      inC1 (itab k) = true := fun j hj k hk e => inC1_mem hj hk e
  have e1 : inC1 tG = true := m 0 (by norm_num) 0 (by norm_num) rfl
  have e2 : inC1 tA = true := m 1 (by norm_num) 1 (by norm_num) rfl
  have e3 : inC1 tH = true := m 2 (by norm_num) 2 (by norm_num) rfl
  have e4 : ((List.range 4).all fun i => inC1 (tY i)) = true := by
    rw [List.all_eq_true]
    intro i hi
    have hi4 := List.mem_range.1 hi
    interval_cases i
    · exact m 3 (by norm_num) 3 (by norm_num) rfl
    · exact m 4 (by norm_num) 4 (by norm_num) rfl
    · exact m 5 (by norm_num) 5 (by norm_num) rfl
    · exact m 6 (by norm_num) 6 (by norm_num) rfl
  have e5 : ((List.range 2).all fun i => inC1 (tCP i)) = true := by
    rw [List.all_eq_true]
    intro i hi
    have hi2 := List.mem_range.1 hi
    interval_cases i
    · exact m 7 (by norm_num) 7 (by norm_num) rfl
    · exact m 8 (by norm_num) 8 (by norm_num) rfl
  have e6 : inC1 (tCS 2) = true := m 9 (by norm_num) 12 (by norm_num) rfl
  have e7 : inC1 (tCS 3) = true := m 10 (by norm_num) 13 (by norm_num) rfl
  have f9 : hsSift (innerTbl 9) = true :=
    sift_true_of_word (by decide) (itab_eq (k := 9) (by norm_num)) s9
  have f10 : hsSift (innerTbl 10) = true :=
    sift_true_of_word (by decide) (itab_eq (k := 10) (by norm_num)) s10
  have f11 : hsSift (innerTbl 11) = true :=
    sift_true_of_word (by decide) (itab_eq (k := 11) (by norm_num)) s11
  have g1 : (tGi.size == 3850) = true := by
    rw [tGi_eq]
    simp [unpack]
  have g2 : (comp 3850 tGi tG == idTab 3850) = true := by
    unfold tG
    rw [tGi_eq, itab_eq (k := 0) (by norm_num), comp_pc' giParts.1 (cnI (k := 0) (by norm_num)),
      giParts.2.2, idTab_idn, beq_pc' cIdn cIdn, Nat.beq_refl]
  unfold memOK
  rw [e1, e2, e3, e4, e5, e6, e7, permI (k := 9) (by norm_num), f9, permI (k := 10) (by norm_num),
    f10, permI (k := 11) (by norm_num), f11, cperm (k := 5) (by norm_num), g1, g2]
  rfl

theorem ptI_of {i : Nat} (hi : i < 7680) : ptI i = true := by
  have hs : i / 32 < 240 := by omega
  have h := CFSG.KS.Raw.Orb.allN_iff.1 (IK.all (i / 32) hs) (i % 32) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.mul (i / 32) 32) (i % 32) = i := by
    change i / 32 * 32 + i % 32 = i
    omega
  rw [CFSG.KS.PEnum.strictB_app', e] at h
  have hb : Nat.blt i 7680 = true := Nat.blt_eq.mpr hi
  rw [hb] at h
  exact h

theorem ptI_parts {i : Nat} (hi : i < 7680) :
    (bIf(bAnd(Nat.beq (p5K (A.T i)) idn, (Nat.beq (A.T i) idn).not),
        bAnd(Nat.blt (OW i) (nat_lit 7680),
          Nat.beq (pc (A.T (OW i)) (A.T i)) (pc (IT.F 0) (A.T (OW i)))), true)) = true ∧
      (bIf(patK (A.T i),
        bAnd(Nat.blt (FW i / 4) (nat_lit 20),
          Nat.beq (pc (hpK (FW i / 4)) (A.T i)) (pc (IT.F (3 + FW i % 4)) (hpK (FW i / 4)))),
        true)) = true := by
  have h := ptI_of hi
  unfold ptI at h
  rw [CFSG.KS.PEnum.strictB_app'] at h
  exact (bAnd_iff _ _).1 h

theorem cnA {i : Nat} (hi : i < 7680) : Cn (A.T i) := canonA (by rw [cnt_A]; exact hi)

theorem orderOK_true : orderOK = true := by
  have hh := IK.ord
  simp only [Bool.and_eq_true] at hh
  obtain ⟨⟨⟨o1, o2⟩, o3⟩, -⟩ := hh
  have c0 := cnI (k := 0) (by norm_num)
  have c2 := cnI (k := 2) (by norm_num)
  have tG_eq : tG = unpack 3850 12 (IT.F 0) := itab_eq (k := 0) (by norm_num)
  have tH_eq : tH = unpack 3850 12 (IT.F 2) := itab_eq (k := 2) (by norm_num)
  unfold orderOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [tG_eq, (pow5_eq c0).1, idTab_idn, beq_pc' (pow5_eq c0).2 cIdn]
    exact o1
  · rw [tG_eq, idTab_idn, bne, beq_pc' c0 cIdn]
    exact o2
  · rw [tG_eq, tH_eq, comp_eq c2 c0 c0 c2]
    exact o3
  · rw [Array.all_eq_true]
    intro i hi
    have hi' : i < 7680 := by rw [c1_size] at hi; exact hi
    have ca := cnA hi'
    rw [← getElem!_pos c1Tabs i hi, c1_get (by rw [cnt_A]; exact hi'), (pow5_eq ca).1, idTab_idn,
      beq_pc' (pow5_eq ca).2 cIdn, bne, beq_pc' ca cIdn]
    obtain ⟨h1, -⟩ := ptI_parts hi'
    cases hp : Nat.beq (p5K (A.T i)) idn <;> cases hn : Nat.beq (A.T i) idn
    · rfl
    · rfl
    · rw [hp, hn] at h1
      change bAnd(Nat.blt (OW i) 7680,
        Nat.beq (pc (A.T (OW i)) (A.T i)) (pc (IT.F 0) (A.T (OW i)))) = true at h1
      obtain ⟨w1, w2⟩ := (bAnd_iff _ _).1 h1
      have hw : OW i < 7680 := Nat.blt_eq.mp w1
      simp only [Bool.not_true, Bool.true_and, Bool.not_false, Bool.false_or, Array.any_eq_true]
      refine ⟨OW i, by rw [c1_size]; exact hw, ?_⟩
      rw [← getElem!_pos c1Tabs (OW i) (by rw [c1_size]; exact hw),
        c1_get (by rw [cnt_A]; exact hw), tG_eq, comp_eq (cnA hw) ca c0 (cnA hw)]
      exact w2
    · rfl

theorem filterOK_true : filterOK = true := by
  have hh := IK.ord
  simp only [Bool.and_eq_true] at hh
  have tA_eq : tA = unpack 3850 12 (IT.F 1) := itab_eq (k := 1) (by norm_num)
  unfold filterOK
  rw [Bool.and_eq_true]
  refine ⟨by rw [tA_eq, patOK_eq (cnI (k := 1) (by norm_num))]; exact hh.2, ?_⟩
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < 7680 := by rw [c1_size] at hi; exact hi
  have ca := cnA hi'
  rw [← getElem!_pos c1Tabs i hi, c1_get (by rw [cnt_A]; exact hi'), patOK_eq ca]
  obtain ⟨-, h2⟩ := ptI_parts hi'
  cases hp : patK (A.T i)
  · rfl
  · rw [hp] at h2
    change bAnd(Nat.blt (FW i / 4) 20,
      Nat.beq (pc (hpK (FW i / 4)) (A.T i)) (pc (IT.F (3 + FW i % 4)) (hpK (FW i / 4)))) = true at h2
    obtain ⟨w1, w2⟩ := (bAnd_iff _ _).1 h2
    have hk : FW i / 4 < 20 := Nat.blt_eq.mp w1
    have hj : FW i % 4 < 4 := Nat.mod_lt _ (by norm_num)
    simp only [Bool.not_true, Bool.false_or]
    unfold hitOK
    rw [Array.any_eq_true]
    have hk' : FW i / 4 < hPows.size := by simp [hPows]; exact hk
    refine ⟨FW i / 4, hk', ?_⟩
    have e : hPows[FW i / 4]'hk' = hPow (FW i / 4) := by simp [hPows]
    rw [e, List.any_eq_true]
    refine ⟨FW i % 4, List.mem_range.2 hj, ?_⟩
    obtain ⟨hp1, hp2⟩ := hPow_eq (FW i / 4)
    have cy := cnI (k := 3 + FW i % 4) (by omega)
    unfold tY
    rw [hp1, itab_eq (k := 3 + FW i % 4) (by omega), comp_eq hp2 ca cy hp2]
    exact w2

theorem eHead : EE.cnt = 16 ∧ penumHdK idn EE.cnt 16 EE.T EE.PL = true ∧
    ∀ j < 4, EE.G j = kW (IT.F 1) (eWc.getD j []) ∧ EE.GI j = EE.G j := by
  have h := IK.eHead
  simp only [Bool.and_eq_true] at h
  refine ⟨Nat.eq_of_beq_eq_true h.1.1, h.1.2, fun j hj => ?_⟩
  have h3 := allN_spec h.2 j hj
  rw [Bool.and_eq_true] at h3
  exact ⟨Nat.eq_of_beq_eq_true h3.1, Nat.eq_of_beq_eq_true h3.2⟩

theorem gensE : GensOK 3850 12 4 EE.G (eGens tA) := by
  have tA_eq : tA = unpack 3850 12 (IT.F 1) := itab_eq (k := 1) (by norm_num)
  refine ⟨by simp [eGens], fun j hj => ?_⟩
  have e : (eGens tA)[j]! = wT tA (eWc.getD j []) := by
    unfold eGens
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  obtain ⟨w1, w2⟩ := wT_eq (cnI (k := 1) (by norm_num)) (eWc.getD j [])
  rw [e, tA_eq, w1, (eHead.2.2 j hj).1]
  exact ⟨rfl, w2⟩

theorem ptE : ∀ i < EE.cnt, penumPtK 3850 12 (mask 12) (3850 * 12) false EE.G EE.GI 4 EE.cnt EE.T
    EE.PL EE.POS EE.SRT EE.SRI i = true := by
  intro i hi
  exact penumSl_spec IK.eRec i (Nat.zero_le _) (by rw [eHead.1] at hi; omega) hi

theorem encE : eEnum = penumRec 3850 12 EE.cnt EE.T EE.PL ∧
    enumOK 3850 (eGens tA) (penumRec 3850 12 EE.cnt EE.T EE.PL) = true :=
  penumK_left_sound (by decide) gensE eHead.2.1 ptE

theorem cnE {x : Nat} (hx : x < 16) : Cn (EE.T x) := penumPt_canon (ptE x (by rw [eHead.1]; exact hx))

theorem eTabs : eEnum.tabs = Array.ofFn (n := EE.cnt) fun i => unpack 3850 12 (EE.T i.val) := by
  rw [encE.1]
  rfl

theorem eTabs_get {x : Nat} (hx : x < 16) : eEnum.tabs[x]! = unpack 3850 12 (EE.T x) := by
  rw [eTabs, getElem!_pos _ x (by simp [eHead.1]; exact hx), Array.getElem_ofFn]

theorem eSize : eEnum.tabs.size = 16 := by rw [eTabs, Array.size_ofFn, eHead.1]

theorem eAll {f : Tab → Bool} (h : ∀ x < 16, f (unpack 3850 12 (EE.T x)) = true) :
    eEnum.tabs.all f = true := by
  rw [Array.all_eq_true]
  intro x hx
  have hx' : x < 16 := by rw [eSize] at hx; exact hx
  rw [← getElem!_pos eEnum.tabs x hx, eTabs_get hx']
  exact h x hx'

theorem eAny {f : Tab → Bool} {x : Nat} (hx : x < 16) (h : f (unpack 3850 12 (EE.T x)) = true) :
    eEnum.tabs.any f = true := by
  rw [Array.any_eq_true]
  refine ⟨x, by rw [eSize]; exact hx, ?_⟩
  rw [← getElem!_pos eEnum.tabs x (by rw [eSize]; exact hx), eTabs_get hx]
  exact h

theorem eOK_true : eOK = true := by
  have h := IK.e
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨x, hx, hx5⟩ := List.any_eq_true.1 h3
  have hx' := List.mem_range.1 hx
  unfold eOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨by rw [encE.1]; exact encE.2, eSize⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact eAll fun a ha => eAll fun b hb => by
      rw [comp_eq (cnE ha) (cnE hb) (cnE hb) (cnE ha)]
      exact allN_spec (allN_spec h1 a ha) b hb
  · exact eAll fun a ha => by rw [isInv_eq (cnE ha)]; exact allN_spec h2 a ha
  · have e : eEnum.tabs[x]! = tT1 := by
      rw [eTabs_get hx', Nat.eq_of_beq_eq_true hx5, tT1, (cent_parts (k := 5) (by norm_num)).1]
    rw [Array.contains_iff, ← e, getElem!_pos eEnum.tabs x (by rw [eSize]; exact hx')]
    exact Array.getElem_mem _
  · exact eAll fun a ha => by
      have h5 := allN_spec h4 a ha
      rw [idTab_idn, beq_pc' (cnE ha) cIdn, fixN_eq, Bool.or_eq_true, beq_iff_eq]
      rw [Bool.or_eq_true] at h5
      rcases h5 with e | e
      · exact Or.inl e
      · exact Or.inr (Nat.eq_of_beq_eq_true e)

theorem presOK_true : presOK = true := by
  have h := IK.pres
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  unfold presOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hi' := allN_spec h1 i hi
    simp only [Bool.and_eq_true] at hi'
    obtain ⟨⟨a1, a2⟩, a3⟩ := hi'
    have cy := cnI (k := 3 + i) (by omega)
    have ty : tY i = unpack 3850 12 (IT.F (3 + i)) := by
      unfold tY
      rw [Nat.add_comm]
      exact itab_eq (by omega)
    have tc : tCP i = unpack 3850 12 (IT.F (7 + i)) := by
      unfold tCP
      rw [Nat.add_comm]
      exact itab_eq (by omega)
    refine ⟨⟨by rw [ty, isInv_eq cy]; exact a1, by rw [ty, fixN_eq]; exact Nat.eq_of_beq_eq_true a2⟩,
      fun j hj => ?_⟩
    have a4 := allN_spec a3 j hj
    rw [Bool.and_eq_true] at a4
    have hp : PW (4 * i + j) < 16 := Nat.blt_eq.mp a4.1
    obtain ⟨w1, w2⟩ := wT_eq cy (eWc.getD j [])
    refine eAny hp ?_
    have cc := cnI (k := 7 + i) (by omega)
    rw [ty, tc, w1, comp_eq cc w2 (cnE hp) cc]
    exact a4.2
  · have hi' := allN_spec h2 i hi
    rw [Bool.and_eq_true] at hi'
    have cy := cnI (k := 5 + i) (by omega)
    have ty : tY (i + 2) = unpack 3850 12 (IT.F (5 + i)) := by
      have e : 3 + (i + 2) = 5 + i := by omega
      unfold tY
      rw [e]
      exact itab_eq (by omega)
    exact ⟨by rw [ty, isInv_eq cy]; exact hi'.1, by rw [ty, fixN_eq]; exact Nat.eq_of_beq_eq_true hi'.2⟩

theorem tY2_eq {i : Nat} (hi : i < 2) : tY (i + 2) = unpack 3850 12 (IT.F (5 + i)) := by
  have e : 3 + (i + 2) = 5 + i := by omega
  unfold tY
  rw [e]
  exact itab_eq (by omega)

theorem classOK_true : CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert.classOK = true := by
  have h := IK.cls
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a12⟩ := h
  have c1 := cnI (k := 1) (by norm_num)
  have c9 := cnI (k := 9) (by norm_num)
  have tA_eq : tA = unpack 3850 12 (IT.F 1) := itab_eq (k := 1) (by norm_num)
  have tU_eq : tU = unpack 3850 12 (IT.F 9) := itab_eq (k := 9) (by norm_num)
  obtain ⟨b1, b2⟩ := wT_eq c1 wbc
  have tB_eq : tB = unpack 3850 12 (kW (IT.F 1) wbc) := by unfold tB; rw [tA_eq]; exact b1
  unfold CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert.classOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cperm (by norm_num), ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [(cent_parts (k := 12) (by norm_num)).1, fixN_eq]; exact Nat.eq_of_beq_eq_true a1
  · rw [tT1, (cent_parts (k := 5) (by norm_num)).1, fixN_eq]; exact Nat.eq_of_beq_eq_true a2
  · rw [tA_eq, fixN_eq]; exact Nat.eq_of_beq_eq_true a3
  · rw [tA_eq, isInv_eq c1]; exact a4
  · rw [tB_eq, isInv_eq b2]; exact a5
  · rw [tB_eq, fixN_eq]; exact Nat.eq_of_beq_eq_true a6
  · rw [tU_eq, isInv_eq c9]; exact a7
  · rw [tU_eq, fixN_eq]; exact Nat.eq_of_beq_eq_true a8
  · rw [tU_eq, tB_eq]
    exact eq_of_beq ((comp_eq c9 b2 b2 c9).trans a9)
  · rw [tU_eq, tB_eq, comp_pc' c9 b2, fixN_eq]; exact Nat.eq_of_beq_eq_true a10
  · intro i hi
    have h12 := allN_spec a12 i hi
    rw [Bool.and_eq_true] at h12
    obtain ⟨w1, w2⟩ := wT_eq (cnI (k := 5 + i) (by omega)) wbc
    rw [tY2_eq hi, w1, isInv_eq w2, fixN_eq]
    exact ⟨h12.1, Nat.eq_of_beq_eq_true h12.2⟩

theorem e8_eq {Y : Nat} (hY : Cn Y) (e : Nat) :
    wT (unpack 3850 12 Y) (yWc.getD e []) = unpack 3850 12 (e8K Y e) ∧ Cn (e8K Y e) :=
  wT_eq hY (yWc.getD e [])

theorem stabOK_true : stabOK = true := by
  have h := IK.stab
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨s1, s2⟩, s3⟩, s4⟩, s5⟩ := h
  have c1 := cnI (k := 1) (by norm_num)
  have tA_eq : tA = unpack 3850 12 (IT.F 1) := itab_eq (k := 1) (by norm_num)
  have c5 := (cent_parts (k := 5) (by norm_num))
  have tE8_eq : ∀ e, tE8 e = unpack 3850 12 (e8K (IT.F 1) e) := fun e => by
    unfold tE8
    rw [tA_eq]
    exact (e8_eq c1 e).1
  unfold stabOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨fun e he => ?_, ?_⟩, ?_⟩, fun j hj e he => ?_⟩, fun i hi e he => ?_⟩
  · rw [tE8_eq, tE8_eq, tT1, c5.1, comp_pc' (e8_eq c1 e).2 c5.2,
      beq_pc' (cn_pc (e8_eq c1 e).2 c5.2) (e8_eq c1 _).2]
    exact allN_spec s1 e he
  · rw [tE8_eq, idTab_idn, beq_pc' (e8_eq c1 0).2 cIdn]; exact s2
  · rw [tE8_eq, tA_eq, beq_pc' (e8_eq c1 1).2 c1]; exact s3
  · have cg := cnI (k := 10 + j) (by omega)
    have tg : tGS j = unpack 3850 12 (IT.F (10 + j)) := by
      unfold tGS
      exact itab_eq (by omega)
    rw [tg, tE8_eq, tE8_eq, comp_eq cg (e8_eq c1 e).2 (e8_eq c1 _).2 cg]
    exact allN_spec (allN_spec s4 j hj) e he
  · have cs := cnI (k := 12 + i) (by omega)
    have cy := cnI (k := 5 + i) (by omega)
    have tc : tCS (i + 2) = unpack 3850 12 (IT.F (12 + i)) := by
      have e2 : 10 + (i + 2) = 12 + i := by omega
      unfold tCS
      rw [e2]
      exact itab_eq (by omega)
    have te : tE8Y (i + 2) e = unpack 3850 12 (e8K (IT.F (5 + i)) e) := by
      unfold tE8Y
      rw [tY2_eq hi]
      exact (e8_eq cy e).1
    rw [tc, te, tE8_eq, comp_eq cs (e8_eq cy e).2 (e8_eq c1 _).2 cs]
    exact allN_spec (allN_spec s5 i hi) e he

theorem innerK :
    innerOK = true := by
  unfold innerOK
  rw [memOK_true, orderOK_true, filterOK_true, eOK_true, presOK_true, classOK_true, stabOK_true]
  rfl

end CertificateChecks.KernelHS3850

end

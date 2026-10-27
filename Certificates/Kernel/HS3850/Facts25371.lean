module

public import Certificates.Kernel.HS3850.F25371T
public import Certificates.Kernel.HS3850.F25371Q
public import Certificates.Kernel.HS3850.FoursFacts
public import CFSG.Certificates.Kernel.L34KSnd.Tab
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Misc.RuInvHash
public import CFSG.Certificates.Kernel.Spor.ClassOneH

public section

set_option maxRecDepth 400000

#kqb_all CFSG.KD.HS3850.EFq CFSG.KD.HS3850.ckFq 30
#kqb_all CFSG.KD.HS3850.ET0 CFSG.KD.HS3850.ckT0 16

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KC.PkPow
open CFSG.KD.LQT.C4126 CFSG.KS.MulH CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.HSStd
open CFSG.KD.LQT.HO (Cn cIdn foldr_unp)

theorem pg_lt {P i : Nat} (hP : Cn P) (hi : i < 3850) : img P i < 3850 :=
  CFSG.KC.L34KSnd.canon_lt hP hi

theorem get_unp {P i : Nat} (_hP : Cn P) (hi : i < 3850) : (unpack 3850 12 P)[i]! = img P i :=
  CFSG.KD.LQT.HO.unpack_getD hi

theorem allBelow_congr {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) :
    allBelow n f = allBelow n g := by
  rw [Bool.eq_iff_iff, CFSG.KS.BfsReplay.allBelow_iff, CFSG.KS.BfsReplay.allBelow_iff]
  exact forall_congr' fun i => imp_congr_right fun hi => by rw [h i hi]

theorem img_pc' {P Q i : Nat} (hP : Cn P) (hi : i < 3850) : img (pc P Q) i = img P (img Q i) :=
  CFSG.KC.L34KSnd.pg_pcomp' hP hi

theorem pts_beq {P Q : Nat} (hP : Cn P) (hQ : Cn Q) :
    allBelow 3850 (fun i => img P i == img Q i) = Nat.beq P Q := by
  rw [Bool.eq_iff_iff, CFSG.KS.BfsReplay.allBelow_iff, Nat.beq_eq]
  constructor
  · intro h
    exact CFSG.KC.L34KSnd.eq_of_pg hP hQ fun i hi => beq_iff_eq.1 (h i hi)
  · intro e i _
    rw [e]
    exact beq_self_eq_true _

theorem img_idn {i : Nat} (hi : i < 3850) : img idn i = i := CFSG.KC.L34KSnd.pg_pidn' (by decide) hi

theorem commPt_eq {X G : Nat} (hX : Cn X) (hG : Cn G) :
    commPt 3850 (unpack 3850 12 X) (unpack 3850 12 G) = cmK X G := by
  unfold commPt cmK
  rw [← pts_beq (cn_pc hX hG) (cn_pc hG hX)]
  apply allBelow_congr
  intro i hi'
  rw [get_unp hG hi', get_unp hX (pg_lt hG hi'), get_unp hX hi', get_unp hG (pg_lt hX hi'),
    img_pc' hX hi', img_pc' hG hi']

theorem sqPt_eq {X : Nat} (hX : Cn X) : sqPt 3850 (unpack 3850 12 X) = sqK X := by
  unfold sqPt sqK
  rw [← pts_beq (cn_pc hX hX) cIdn]
  apply allBelow_congr
  intro i hi'
  rw [get_unp hX hi', get_unp hX (pg_lt hX hi'), img_pc' hX hi', img_idn hi']

theorem commPt2_eq {W X G : Nat} (hW : Cn W) (hX : Cn X) (hG : Cn G) :
    commPt2 3850 (unpack 3850 12 W) (unpack 3850 12 X) (unpack 3850 12 G) = cmK (pc W X) G := by
  unfold commPt2 cmK
  have hWX := cn_pc hW hX
  rw [← pts_beq (cn_pc hWX hG) (cn_pc hG hWX)]
  apply allBelow_congr
  intro i hi'
  rw [get_unp hG hi', get_unp hX (pg_lt hG hi'), get_unp hW (pg_lt hX (pg_lt hG hi')),
    get_unp hX hi', get_unp hW (pg_lt hX hi'), get_unp hG (pg_lt hW (pg_lt hX hi')),
    img_pc' hWX hi', img_pc' hW (pg_lt hG hi'), img_pc' hG hi', img_pc' hW hi']

theorem sqPt2_eq {W X : Nat} (hW : Cn W) (hX : Cn X) :
    sqPt2 3850 (unpack 3850 12 W) (unpack 3850 12 X) = sqK (pc W X) := by
  unfold sqPt2 sqK
  have hWX := cn_pc hW hX
  rw [← pts_beq (cn_pc hWX hWX) cIdn]
  apply allBelow_congr
  intro i hi'
  rw [get_unp hX hi', get_unp hW (pg_lt hX hi'), get_unp hX (pg_lt hW (pg_lt hX hi')),
    get_unp hW (pg_lt hX (pg_lt hW (pg_lt hX hi'))), img_pc' hWX hi', img_pc' hW hi',
    img_pc' hW (pg_lt hW (pg_lt hX hi')), img_idn hi']

theorem facts_eq {k : Nat} (hk : k < 2) : natArr (factsTbl k) = unpack 3850 12 (FT.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound FT.all (by norm_num) k hk
  rw [← FT.eq] at h
  exact h

theorem facts_tab {k : Nat} (hk : k < 2) : factsTbl k = tabT (unpack 3850 12 (FT.F k)) := by
  rw [← facts_eq hk, tabT_natArr]

theorem ok_parts : Cn (FT.F 0) ∧ Cn (pinvS 3850 12 (mask 12) (FT.F 0)) ∧
    invEqK 3850 12 (mask 12) (3850 * 12) (FT.F 0) (pinvS 3850 12 (mask 12) (FT.F 0)) = true ∧
    allN 4 (fun b => Nat.beq (img (FT.F 0) b) b) = true ∧ (Nat.beq (img (FT.F 0) 5) 5).not = true ∧
    pc (FT.F 0) (HC.F 0) = wfoldR CFSG.KD.LQT.HN.ls8 wZU ∧ cmK (FT.F 0) (HC.F 5) = true ∧
    Cn (FT.F 1) ∧ Cn hInvK ∧ pc (FT.F 1) hInvK = idn ∧ FT.F 1 = wfoldR CFSG.KD.LQT.HN.ls8 wH ∧
    pc oddAK (pc oddAK (pc oddAK (pc oddAK (pc oddAK idn)))) = idn ∧
    pc oddBK (pc oddBK (pc oddBK idn)) = idn ∧
    pc (pc hInvK (pc oddBK (pc oddAK (pc oddBK (pc oddAK idn))))) (FT.F 1) = HC.F 5 ∧
    ET0.cnt = 512 ∧ penumHdK idn ET0.cnt 512 ET0.T ET0.PL = true ∧
    ET0.G 0 = wfoldR lc1 [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0] ∧
    ET0.G 1 = wfoldR lc1 [1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0] ∧
    ET0.G 2 = wfoldR lc1 [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0] ∧ ET0.T t1Pos = HC.F 5 ∧
    commRelK qPerf (qPerf 0) [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1]
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0] = true ∧
    commRelK qPerf (qPerf 1) [0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0]
      [0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1] = true ∧
    wfoldR qPerf [0, 0, 0, 0, 0, 0] = HC.F 5 ∧
    foldN 7680 (fun x c => nIf(t0Idx.elem x, Nat.succ c, c)) 0 = 2 := by
  have h := ok25371
  rw [CFSG.KS.PEnum.strictB_app'] at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := h
  exact ⟨h1, h2, h3, h4, h5, Nat.eq_of_beq_eq_true h6, h7, h8, h9, Nat.eq_of_beq_eq_true h10,
    Nat.eq_of_beq_eq_true h11, Nat.eq_of_beq_eq_true h12, Nat.eq_of_beq_eq_true h13,
    Nat.eq_of_beq_eq_true h14, Nat.eq_of_beq_eq_true h15, h16, Nat.eq_of_beq_eq_true h17,
    Nat.eq_of_beq_eq_true h18, Nat.eq_of_beq_eq_true h19, Nat.eq_of_beq_eq_true h20, h21, h22,
    Nat.eq_of_beq_eq_true h23, Nat.eq_of_beq_eq_true h24⟩

theorem all_two {gs : Array Tab} {a b : Tab} (h : gs = #[a, b]) (p : Tab → Bool) :
    gs.all p = (p a && p b) := by
  subst h
  rw [Bool.eq_iff_iff, Array.all_eq_true, Bool.and_eq_true]
  constructor
  · intro hp
    exact ⟨hp 0 (by simp), hp 1 (by simp)⟩
  · rintro ⟨h0, h1⟩ i hi
    have hi' : i < 2 := by simpa using hi
    interval_cases i
    · exact h0
    · exact h1

theorem all_three {gs : Array Tab} {a b c : Tab} (h : gs = #[a, b, c]) (p : Tab → Bool) :
    gs.all p = (p a && (p b && p c)) := by
  subst h
  rw [Bool.eq_iff_iff, Array.all_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  constructor
  · intro hp
    exact ⟨hp 0 (by simp), hp 1 (by simp), hp 2 (by simp)⟩
  · rintro ⟨h0, h1, h2⟩ i hi
    have hi' : i < 3 := by simpa using hi
    interval_cases i
    · exact h0
    · exact h1
    · exact h2

theorem sqAt_eq {W G0 G1 X : Nat} {gs : Array Tab} (hW : Cn W) (h0 : Cn G0) (h1 : Cn G1)
    (hX : Cn X) (hgs : gs = #[unpack 3850 12 G0, unpack 3850 12 G1]) :
    ((!(gs.all (commPt 3850 (unpack 3850 12 X))) || sqPt 3850 (unpack 3850 12 X)) &&
      (!(gs.all (commPt2 3850 (unpack 3850 12 W) (unpack 3850 12 X))) ||
        sqPt2 3850 (unpack 3850 12 W) (unpack 3850 12 X))) = sqAt W G0 G1 X := by
  rw [all_two hgs, all_two hgs, commPt_eq hX h0, commPt_eq hX h1, sqPt_eq hX,
    commPt2_eq hW hX h0, commPt2_eq hW hX h1, sqPt2_eq hW hX]
  unfold sqAt
  rw [CFSG.KS.PEnum.strictB_app']
  cases cmK X G0 <;> cases cmK X G1 <;> cases sqK X <;> cases cmK (pc W X) G0 <;>
    cases cmK (pc W X) G1 <;> cases sqK (pc W X) <;> rfl

theorem c1Tabs_eq : hsC1Tabs = CFSG.QuasithinUnique.Id2519.HSAut.gensA0 := by
  unfold hsC1Tabs CFSG.QuasithinUnique.Id2519.HSAut.gensA0
  apply Array.ext (by simp)
  intro i h1 _
  have hi : i < 2 := by simpa using h1
  interval_cases i <;> simp

theorem c1Enum_eq : hsC1Enum = penumRec 3850 12 CFSG.KD.LQT.HN.A.cnt CFSG.KD.LQT.HN.A.T
    CFSG.KD.LQT.HN.A.PL := by
  unfold hsC1Enum
  rw [c1Tabs_eq]
  exact CFSG.KD.LQT.HN.enum_eq.1

theorem cnt_A : CFSG.KD.LQT.HN.A.cnt = 7680 := CFSG.KD.LQT.HN.a_parts.2.2.2

theorem canonA {i : Nat} (hi : i < CFSG.KD.LQT.HN.A.cnt) : Cn (CFSG.KD.LQT.HN.A.T i) :=
  penumPt_canon (CFSG.KD.LQT.HN.pt i hi).1

theorem lc1_parts {j : Nat} (hj : j < 2) : hsC1Tabs[j]! = unpack 3850 12 (lc1 j) ∧ Cn (lc1 j) := by
  have e : hsC1Tabs[j]! = natArr (hsCentTbl (j + 6)) := by
    unfold hsC1Tabs
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  rw [e, Nat.add_comm]
  exact cent_parts (by omega)

theorem c1Tabs_two : hsC1Tabs = #[unpack 3850 12 (lc1 0), unpack 3850 12 (lc1 1)] := by
  apply Array.ext (by simp [hsC1Tabs])
  intro i h1 _
  have hi : i < 2 := by simpa [hsC1Tabs] using h1
  rw [← getElem!_pos hsC1Tabs i h1, (lc1_parts hi).1]
  interval_cases i <;> rfl

theorem oddA_eq : oddA = unpack 3850 12 oddAK ∧ Cn oddAK := c2Word (by decide)

theorem oddB_eq : oddB = unpack 3850 12 oddBK ∧ Cn oddBK := c2Word (by decide)

theorem oc_cn : Cn oc0K ∧ Cn oc1K := by
  obtain ⟨-, -, -, -, -, -, -, c1, ci, -⟩ := ok_parts
  exact ⟨cn_pc (cn_pc ci oddA_eq.2) c1, cn_pc (cn_pc ci oddB_eq.2) c1⟩

theorem et0G_eq {j : Nat} (hj : j < 3) : ET0.G j = wfoldR lc1 (hsT0Words.getD j []) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e0, e1, e2, -⟩ := ok_parts
  interval_cases j
  · exact e0
  · exact e1
  · exact e2

theorem t0Words_lt {j : Nat} : ∀ l ∈ hsT0Words.getD j [], l < 2 := by
  rcases j with _ | _ | _ | j <;> simp [hsT0Words]

theorem c1Word {ls : List Nat} (hls : ∀ l ∈ ls, l < 2) :
    wordTabS 3850 hsC1Tabs ls = unpack 3850 12 (wfoldR lc1 ls) ∧ Cn (wfoldR lc1 ls) :=
  wordTabS_unp ls fun l hl => lc1_parts (hls l hl)

theorem et0G_cn {j : Nat} (hj : j < 3) : Cn (ET0.G j) := by
  rw [et0G_eq hj]
  exact (c1Word t0Words_lt).2

theorem cmAt_of {X G p : Nat} (hX : Cn X) (hG : Cn G) (hp : p < 3850) (h : cmK X G = true) :
    cmAt X G p = true := by
  unfold cmK at h
  have e : img (pc X G) p = img (pc G X) p := by rw [Nat.eq_of_beq_eq_true h]
  rw [img_pc' hX hp, img_pc' hG hp] at e
  unfold cmAt
  rw [e]
  exact Nat.beq_refl _

theorem tpts_of {f : Nat → Bool} (h : ∀ p < 3850, f p = true) : tpts f = true := by
  unfold tpts
  rw [h (nat_lit 517) (by decide), h (nat_lit 1001) (by decide), h (nat_lit 1597) (by decide),
    h (nat_lit 2003) (by decide), h (nat_lit 2689) (by decide), h (nat_lit 3011) (by decide)]

theorem cmQ_eq {X G : Nat} (hX : Cn X) (hG : Cn G) : cmQ X G = cmK X G := by
  unfold cmQ
  cases h : cmK X G
  · cases tpts (cmAt X G) <;> rfl
  · rw [tpts_of fun p hp => cmAt_of hX hG hp h]

theorem cmAt2_of {W X G p : Nat} (hW : Cn W) (hX : Cn X) (hG : Cn G) (hp : p < 3850)
    (h : cmK (pc W X) G = true) : cmAt2 W X G p = true := by
  unfold cmK at h
  have e : img (pc (pc W X) G) p = img (pc G (pc W X)) p := by rw [Nat.eq_of_beq_eq_true h]
  rw [img_pc' (cn_pc hW hX) hp, img_pc' hW (pg_lt hG hp), img_pc' hG hp, img_pc' hW hp] at e
  unfold cmAt2
  rw [e]
  exact Nat.beq_refl _

theorem cmP2_of {W X G : Nat} (hW : Cn W) (hX : Cn X) (hG : Cn G)
    (h : cmK (pc W X) G = true) : cmP2 W X G = true := by
  unfold cmP2
  exact tpts_of fun p hp => cmAt2_of hW hX hG hp h

theorem sqAtQ_eq {W G0 G1 X : Nat} (hW : Cn W) (hX : Cn X) (h0 : Cn G0) (h1 : Cn G1) :
    sqAtQ W G0 G1 X = sqAt W G0 G1 X := by
  have k0 := cmP2_of hW hX h0
  have k1 := cmP2_of hW hX h1
  unfold sqAtQ sqAt
  rw [CFSG.KS.PEnum.strictB_app', CFSG.KS.PEnum.strictB_app', cmQ_eq hX h0, cmQ_eq hX h1]
  revert k0 k1
  cases cmK (pc W X) G0 <;> cases cmK (pc W X) G1 <;> cases cmP2 W X G0 <;>
    cases cmP2 W X G1 <;> cases cmK X G0 <;> cases cmK X G1 <;> cases sqK X <;>
    cases sqK (pc W X) <;> decide

theorem ptFQ_eq {i : Nat} (hi : i < 7680) :
    ptFQ (FT.F 0) (lc1 0) (lc1 1) oc0K oc1K (ET0.G 0) (ET0.G 1) (ET0.G 2) i = ptF i := by
  have hx := canonA (i := i) (by rw [cnt_A]; exact hi)
  unfold ptFQ ptF
  rw [CFSG.KS.PEnum.strictB_app', CFSG.KS.PEnum.strictB_app',
    sqAtQ_eq ok_parts.1 hx (lc1_parts (j := 0) (by norm_num)).2 (lc1_parts (j := 1) (by norm_num)).2,
    sqAtQ_eq ok_parts.1 hx oc_cn.1 oc_cn.2, cmQ_eq hx (et0G_cn (j := 0) (by norm_num)),
    cmQ_eq hx (et0G_cn (j := 1) (by norm_num)), cmQ_eq hx (et0G_cn (j := 2) (by norm_num))]

theorem ptF_of {i : Nat} (hi : i < 7680) : ptF i = true := by
  have hs : i / 256 < 30 := by omega
  have hq := EFq.all (i / 256) hs
  unfold ckFq at hq
  simp only [CFSG.KS.PEnum.strictB_app'] at hq
  have hc := CFSG.KS.Raw.Orb.allN_iff.1 hq (i / 32 % 8) (Nat.mod_lt _ (by omega))
  have e8 : Nat.add (Nat.mul (i / 256) 8) (i / 32 % 8) = i / 32 := by
    change i / 256 * 8 + i / 32 % 8 = i / 32
    omega
  rw [e8] at hc
  unfold ckFB at hc
  have h := CFSG.KS.Raw.Orb.allN_iff.1 hc (i % 32) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.mul (i / 32) 32) (i % 32) = i := by
    change i / 32 * 32 + i % 32 = i
    omega
  rw [CFSG.KS.PEnum.strictB_app', e] at h
  have hb : Nat.blt i 7680 = true := Nat.blt_eq.mpr hi
  rw [hb] at h
  rw [← ptFQ_eq hi]
  exact h

theorem ptF_parts {i : Nat} (hi : i < 7680) :
    sqAt (FT.F 0) (lc1 0) (lc1 1) (CFSG.KD.LQT.HN.A.T i) = true ∧
      sqAt (FT.F 0) oc0K oc1K (CFSG.KD.LQT.HN.A.T i) = true ∧
      (cmK (CFSG.KD.LQT.HN.A.T i) (ET0.G 0) && (cmK (CFSG.KD.LQT.HN.A.T i) (ET0.G 1) &&
        cmK (CFSG.KD.LQT.HN.A.T i) (ET0.G 2))) = t0Idx.elem i := by
  have h := ptF_of hi
  unfold ptF at h
  rw [CFSG.KS.PEnum.strictB_app'] at h
  obtain ⟨h1, h2, h3⟩ := (by simpa only [bAnd_iff] using h :
    sqAt (FT.F 0) (lc1 0) (lc1 1) (CFSG.KD.LQT.HN.A.T i) = true ∧
      sqAt (FT.F 0) oc0K oc1K (CFSG.KD.LQT.HN.A.T i) = true ∧ _)
  refine ⟨h1, h2, ?_⟩
  have key : ∀ a b : Bool, Bool.beq a b = true → a = b := by decide
  have h3' := key _ _ h3
  rw [← h3']
  cases cmK (CFSG.KD.LQT.HN.A.T i) (ET0.G 0) <;> cases cmK (CFSG.KD.LQT.HN.A.T i) (ET0.G 1) <;>
    cases cmK (CFSG.KD.LQT.HN.A.T i) (ET0.G 2) <;> rfl

theorem sqCheck_of {gs : Array Tab} {G0 G1 : Nat} (h0 : Cn G0) (h1 : Cn G1)
    (hgs : gs = #[unpack 3850 12 G0, unpack 3850 12 G1])
    (hs : ∀ i < 7680, sqAt (FT.F 0) G0 G1 (CFSG.KD.LQT.HN.A.T i) = true) :
    sqCheck 3850 hsC1Enum.tabs (natArr (factsTbl 0)) gs = true := by
  rw [c1Enum_eq, facts_eq (k := 0) (by norm_num)]
  unfold sqCheck penumRec
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < CFSG.KD.LQT.HN.A.cnt := by simpa using hi
  simp only [Array.getElem_ofFn]
  rw [sqAt_eq ok_parts.1 h0 h1 (canonA hi') hgs]
  exact hs i (cnt_A ▸ hi')

theorem u1OK_true : u1OK = true := by
  unfold u1OK
  exact sqCheck_of (lc1_parts (j := 0) (by norm_num)).2 (lc1_parts (j := 1) (by norm_num)).2
    c1Tabs_two fun i hi => (ptF_parts hi).1

theorem hInv_eq : hInvTab = unpack 3850 12 hInvK := by
  obtain ⟨-, -, -, -, -, -, -, c1, ci, e, -⟩ := ok_parts
  unfold hInvTab
  rw [facts_eq (k := 1) (by norm_num)]
  exact CFSG.KC.L34KSnd.invTab_eq_of_pcomp c1 ci e

theorem oddConj_eq : oddConj = #[unpack 3850 12 oc0K, unpack 3850 12 oc1K] := by
  obtain ⟨-, -, -, -, -, -, -, c1, ci, -⟩ := ok_parts
  obtain ⟨ha, ca⟩ := oddA_eq
  obtain ⟨hb, cb⟩ := oddB_eq
  unfold oddConj oc0K oc1K
  rw [hInv_eq, ha, hb, facts_eq (k := 1) (by norm_num), comp_pc' ci ca, comp_pc' (cn_pc ci ca) c1,
    comp_pc' ci cb, comp_pc' (cn_pc ci cb) c1]

theorem u2bOK_true : u2bOK = true := by
  obtain ⟨-, -, -, -, -, -, -, c1, ci, -, -, e5, e3, eab, -⟩ := ok_parts
  obtain ⟨ha, ca⟩ := oddA_eq
  obtain ⟨hb, cb⟩ := oddB_eq
  have w5 := wordTabS_unp (gs := #[oddA]) (L := fun _ => oddAK) (List.replicate 5 0)
    (fun l hl => by
      rw [List.eq_of_mem_replicate hl]
      exact ⟨by rw [ha]; rfl, ca⟩)
  have w3 := wordTabS_unp (gs := #[oddB]) (L := fun _ => oddBK) (List.replicate 3 0)
    (fun l hl => by
      rw [List.eq_of_mem_replicate hl]
      exact ⟨by rw [hb]; rfl, cb⟩)
  have wab := wordTabS_unp (gs := #[oddA, oddB]) (L := fun l => nIf(Nat.beq l 0, oddAK, oddBK))
    [1, 0, 1, 0] (fun l hl => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · exact ⟨by rw [hb]; rfl, cb⟩
      · exact ⟨by rw [ha]; rfl, ca⟩
      · exact ⟨by rw [hb]; rfl, cb⟩
      · exact ⟨by rw [ha]; rfl, ca⟩)
  have v5 : wfoldR (fun _ => oddAK) (List.replicate 5 0) =
      pc oddAK (pc oddAK (pc oddAK (pc oddAK (pc oddAK idn)))) := by
    simp only [List.replicate, CFSG.KD.LQT.HO.wfoldR_cons']
    rfl
  have v3 : wfoldR (fun _ => oddBK) (List.replicate 3 0) = pc oddBK (pc oddBK (pc oddBK idn)) := by
    simp only [List.replicate, CFSG.KD.LQT.HO.wfoldR_cons']
    rfl
  have vab : wfoldR (fun l => nIf(Nat.beq l 0, oddAK, oddBK)) [1, 0, 1, 0] =
      pc oddBK (pc oddAK (pc oddBK (pc oddAK idn))) := by
    simp only [CFSG.KD.LQT.HO.wfoldR_cons']
    rfl
  unfold u2bOK
  rw [w5.1, w3.1, wab.1, idTab_idn, beq_pc' w5.2 cIdn, beq_pc' w3.2 cIdn, v5, v3, e5, e3, hInv_eq, facts_eq (k := 1) (by norm_num), comp_pc' ci wab.2,
    comp_pc' (cn_pc ci wab.2) c1, (cent_parts (k := 5) (by norm_num)).1,
    beq_pc' (cn_pc (cn_pc ci wab.2) c1) (cent_parts (k := 5) (by norm_num)).2, vab, eab,
    Nat.beq_refl]
  rw [sqCheck_of oc_cn.1 oc_cn.2 oddConj_eq fun i hi => (ptF_parts hi).2.1]
  rfl

theorem t0Gens_get {j : Nat} (hj : j < 3) :
    hsT0Gens[j]! = wordTabS 3850 hsC1Tabs (hsT0Words.getD j []) := by
  unfold hsT0Gens
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem gensT0 : GensOK 3850 12 3 ET0.G hsT0Gens := by
  refine ⟨by simp [hsT0Gens], fun j hj => ?_⟩
  obtain ⟨h1, h2⟩ := c1Word (t0Words_lt (j := j))
  rw [t0Gens_get hj, h1, et0G_eq hj]
  exact ⟨rfl, h2⟩

theorem ptT0 : ∀ i < ET0.cnt, penumPtK 3850 12 (mask 12) (3850 * 12) false ET0.G ET0.GI 3 ET0.cnt
    ET0.T ET0.PL ET0.POS ET0.SRT ET0.SRI i = true := by
  intro i hi
  have hi' : i < 512 := ok_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ▸ hi
  have hs : i / 32 < 16 := by omega
  exact penumSl_spec (ET0.all (i / 32) hs) i (by change i / 32 * 32 ≤ i; omega)
    (by change i < i / 32 * 32 + 32; omega) hi

theorem encT0 : hsT0Enum = penumRec 3850 12 ET0.cnt ET0.T ET0.PL ∧
    enumOK 3850 hsT0Gens (penumRec 3850 12 ET0.cnt ET0.T ET0.PL) = true :=
  penumK_left_sound (by decide) gensT0 ok_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ptT0

theorem t0Gens_three : hsT0Gens = #[unpack 3850 12 (ET0.G 0), unpack 3850 12 (ET0.G 1),
    unpack 3850 12 (ET0.G 2)] := by
  apply Array.ext (by simp [hsT0Gens])
  intro i h1 _
  have hi : i < 3 := by simpa [hsT0Gens] using h1
  rw [← getElem!_pos hsT0Gens i h1, (gensT0.2 i hi).1]
  interval_cases i <;> rfl

theorem t0OK_true : t0OK = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hcnt, -, -, -, -, ht1, -, -, -, h2⟩ := ok_parts
  unfold t0OK
  rw [encT0.1, encT0.2]
  have hs : (penumRec 3850 12 ET0.cnt ET0.T ET0.PL).tabs.size = 512 := by simp [penumRec, hcnt]
  have hc : (penumRec 3850 12 ET0.cnt ET0.T ET0.PL).tabs.contains (natArr (hsCentTbl 5)) = true := by
    rw [Array.contains_iff_mem, (cent_parts (k := 5) (by norm_num)).1, ← ht1]
    have hq : t1Pos < (penumRec 3850 12 ET0.cnt ET0.T ET0.PL).tabs.size := by
      rw [hs]
      decide
    have e : (penumRec 3850 12 ET0.cnt ET0.T ET0.PL).tabs[t1Pos] = unpack 3850 12 (ET0.T t1Pos) := by
      simp [penumRec]
    rw [← e]
    exact Array.getElem_mem hq
  have hf : ((hsC1Enum.tabs.toList.filter fun x => hsT0Gens.all (commPt 3850 x))).length = 2 := by
    rw [c1Enum_eq]
    have e := CFSG.KS.PEnum.filter_ofFn CFSG.KD.LQT.HN.A.cnt
      (fun i => unpack 3850 12 (CFSG.KD.LQT.HN.A.T i)) (fun x => hsT0Gens.all (commPt 3850 x))
    have hcg : ((List.range CFSG.KD.LQT.HN.A.cnt).filter fun i =>
        hsT0Gens.all (commPt 3850 (unpack 3850 12 (CFSG.KD.LQT.HN.A.T i)))) =
        (List.range CFSG.KD.LQT.HN.A.cnt).filter fun i => t0Idx.elem i := by
      apply List.filter_congr
      intro i hi
      have hi' := List.mem_range.1 hi
      have cA := canonA hi'
      rw [all_three t0Gens_three, commPt_eq cA (gensT0.2 0 (by norm_num)).2,
        commPt_eq cA (gensT0.2 1 (by norm_num)).2, commPt_eq cA (gensT0.2 2 (by norm_num)).2]
      exact (ptF_parts (cnt_A ▸ hi')).2.2
    unfold penumRec
    dsimp only
    rw [← Array.toList_filter, e, List.toList_toArray, List.length_map, hcg,
      ← CFSG.KC.Misc.RuInv.P.foldN_count, cnt_A]
    exact h2
  rw [hs, hc, hf]
  rfl

section Sift


open CFSG.KD.LQT.HN (hd gen_eq sift_iff rep_word rep_pc) in
theorem sift_false_of_fix {T : Table} {Z ZI : Nat} (hz : natArr T = unpack 3850 12 Z)
    (hinv : invEqK 3850 12 (mask 12) (3850 * 12) Z ZI = true)
    (hfix : allN 4 (fun b => Nat.beq (img Z b) b) = true) (hmove : (Nat.beq (img Z 5) 5).not = true) :
    hsSift T = false := by
  cases hs : hsSift T
  · rfl
  · exfalso
    have hr := (CFSG.Monster.B.Co2.rep_permOfArr (invEqK_sound hinv).2).1
    have hr' : CFSG.Monster.B.Co2.Rep 3850 (natArr T)
        (CFSG.Monster.B.Co2.permOfArr 3850 (unpack 3850 12 Z)) := by
      rw [hz]
      exact hr
    have hm := (sift_iff hr').1 hs
    have h1 : CFSG.Monster.B.Co2.permOfArr 3850 (unpack 3850 12 Z) = 1 := by
      refine Orb.fix_one hd CertificateChecks.KernelSporSch.PHSCheck.card_le ⟨gen_eq ▸ hm, fun t htl hb => ?_⟩
      have htl' : t < 4 := htl
      have hbt : CFSG.Sporadic.Schreier.PairHS.baseArr[t]! = t := by interval_cases t <;> rfl
      apply Fin.ext
      rw [← hr.apply hb, CFSG.KS.Raw.Orb.unpack_get hb]
      have := Nat.eq_of_beq_eq_true (allN_spec hfix t htl')
      change pg 12 (mask 12) Z CFSG.Sporadic.Schreier.PairHS.baseArr[t]! =
        CFSG.Sporadic.Schreier.PairHS.baseArr[t]!
      rw [hbt]
      exact this
    have h5 := hr.apply (i := 5) (by norm_num)
    rw [h1, CFSG.KS.Raw.Orb.unpack_get (by norm_num)] at h5
    have h55 : img Z 5 = 5 := h5
    rw [h55, Nat.beq_refl] at hmove
    exact absurd hmove (by decide)

open CFSG.KD.LQT.HN (sift_iff rep_word) in
theorem sift_true_of_word {T : Table} {X : Nat} {w : List Nat} (hw : ∀ l ∈ w, l < 16)
    (hz : natArr T = unpack 3850 12 X) (e : X = wfoldR CFSG.KD.LQT.HN.ls8 w) : hsSift T = true := by
  obtain ⟨g, hg, hrep⟩ := rep_word w hw
  rw [← e, ← hz] at hrep
  exact (sift_iff hrep).2 hg

theorem tablesOK_true : tablesOK = true := by
  obtain ⟨c0, ci0, i0, hfix, hmove, ezu, cm, c1, ci1, e1, eh, -⟩ := ok_parts
  have cu := (cent_parts (k := 0) (by norm_num)).2
  have c5 := (cent_parts (k := 5) (by norm_num)).2
  have iH : invEqK 3850 12 (mask 12) (3850 * 12) (FT.F 1) hInvK = true := by
    obtain ⟨-, -, hinv⟩ := CFSG.KC.L34KSnd.injK_of_pcomp c1 ci1 e1
    have hpk := CFSG.KS.PinvS.permOK_pinvS c1 (CFSG.KC.L34KSnd.injK_of_pcomp c1 ci1 e1).1
    exact hpk
  unfold tablesOK outerCommOK
  have s0 : hsSift (factsTbl 0) = false :=
    sift_false_of_fix (facts_eq (k := 0) (by norm_num)) i0 hfix hmove
  have szu : hsSift (compT 3850 (factsTbl 0) hsOuterTbl) = true := by
    refine sift_true_of_word (X := pc (FT.F 0) (HC.F 0)) (by decide) ?_ ezu
    rw [facts_tab (k := 0) (by norm_num), hsOuterTbl, cent_tab (k := 0) (by norm_num),
      compT_pc c0 cu, natArr_tabT (cn_pc c0 cu)]
  have s1 : hsSift (factsTbl 1) = true := sift_true_of_word (by decide)
    (facts_eq (k := 1) (by norm_num)) eh
  rw [s0, szu, s1, hsOuterTbl, cperm (k := 0) (by norm_num), cperm (k := 5) (by norm_num),
    facts_eq (k := 1) (by norm_num), CFSG.KC.L34KSnd.invTab_eq_of_pcomp c1 ci1 e1,
    CFSG.KC.L34KSnd.comp_inv_of_pcomp c1 ci1 e1, facts_tab (k := 0) (by norm_num),
    facts_tab (k := 1) (by norm_num), permOK_unpack c0 i0, permOK_unpack c1 iH,
    cent_tab (k := 5) (by norm_num), commTT_unpack c0 c5]
  have hcm : Nat.beq (pcomp 3850 12 (mask 12) (FT.F 0) (HC.F 5))
      (pcomp 3850 12 (mask 12) (HC.F 5) (FT.F 0)) = true := cm
  rw [hcm]
  simp [CFSG.KS.PEnum.unpack_size]

end Sift

theorem perfGens_get {j : Nat} (hj : j < 2) :
    hsPerfGens[j]! = unpack 3850 12 (qPerf j) ∧ Cn (qPerf j) := by
  have e : hsPerfGens[j]! = wordTabS 3850 hsC1Tabs (hsPerfWords.getD j []) := by
    unfold hsPerfGens
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  rw [e]
  interval_cases j
  · exact c1Word (by decide)
  · exact c1Word (by decide)

theorem perfWord {ls : List Nat} (hls : ∀ l ∈ ls, l < 2) :
    wordTabS 3850 hsPerfGens ls = unpack 3850 12 (wfoldR qPerf ls) ∧ Cn (wfoldR qPerf ls) :=
  wordTabS_unp ls fun l hl => perfGens_get (hls l hl)

theorem commRel_of {q : Nat} {X Y : List Nat} (hq : Cn q) (hX : ∀ l ∈ X, l < 2)
    (hY : ∀ l ∈ Y, l < 2) (h : commRelK qPerf q X Y = true) :
    commRel hsPerfGens (unpack 3850 12 q) X Y = true := by
  obtain ⟨wx, cx⟩ := perfWord hX
  obtain ⟨wy, cy⟩ := perfWord hY
  unfold commRel
  rw [wx, wy, comp_pc' hq cy, comp_pc' (cn_pc hq cy) cx, comp_pc' cx cy,
    beq_pc' (cn_pc (cn_pc hq cy) cx) (cn_pc cx cy)]
  exact h

theorem perfOK_true : perfOK = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, r0, r1, p6, -⟩ := ok_parts
  unfold perfOK
  have ha : allBelow 2 (fun i => commRel hsPerfGens hsPerfGens[i]! (hsPerfComm.getD i ([], [])).1
      (hsPerfComm.getD i ([], [])).2) = true := by
    rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro i hi
    rw [(perfGens_get hi).1]
    interval_cases i
    · exact commRel_of (perfGens_get (j := 0) (by norm_num)).2 (by decide) (by decide) r0
    · exact commRel_of (perfGens_get (j := 1) (by norm_num)).2 (by decide) (by decide) r1
  obtain ⟨w6, c6⟩ := perfWord (ls := List.replicate 6 0) (by decide)
  rw [ha, w6, (cent_parts (k := 5) (by norm_num)).1,
    beq_pc' c6 (cent_parts (k := 5) (by norm_num)).2]
  have e : wfoldR qPerf (List.replicate 6 0) = wfoldR qPerf [0, 0, 0, 0, 0, 0] := rfl
  rw [e, p6, Nat.beq_refl]
  rfl

theorem factsData_true :
    factsData = true := by
  unfold factsData
  rw [tablesOK_true, u1OK_true, u2bOK_true, t0OK_true, perfOK_true]
  rfl

end CFSG.KD.HS3850

end


module

public import Certificates.Kernel.KGC31M23.CosFacts
public import Certificates.Kernel.KGC31M23.Small
public import Certificates.Kernel.KGC31M23.Glue
public import Certificates.Kernel.KGC31M23.Inv0
public import Certificates.Kernel.KGC31M23.Inv1
public import CFSG.Certificates.Kernel.KGC31PPow
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Quasithin.Vol2.KGFactC31M23Data
public import Certificates.Kernel.J4Count.FixCE

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M23

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3 CFSG.KC.BfsPin
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M23
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M23OC CFSG.KS.SporSch.MOC
open CFSG.Monster.B.Mathieu

#kc_forall_chunks invAll (fun k => invBlk k = true) 8 CertificateChecks.KernelKGC31M23.invBlk 1

theorem invOne_all : ∀ j < D.c, invOne j = true := by
  intro j hj
  have hN := Nat.eq_of_beq_eq_true kC
  have hk : j / 500 < 8 := by omega
  apply List.all_eq_true.1 (invAll (j / 500) hk) j
  rw [List.mem_range'_1]
  omega

theorem inv_facts {j : Nat} (hj : j < D.c) :
    PP 23 5 (D.ST j) ∧ porbOne 23 5 5 X5 C5 (D.ST j) = true ∧
      porbOne 23 5 7 X7 C7 (D.ST j) = true ∧ pactOne 23 5 11 X11 (D.ST j) = true ∧
      pactOne 23 5 23 X23 (D.ST j) = true := by
  have h := invOne_all j hj
  simp only [invOne, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨PP_of_permOK hsz h1, h2, h3, h4, h5⟩

theorem hI : ∀ t ∈ invs, ∃ u, PP 23 5 u ∧ t = tabP 23 5 u := by
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  exact ⟨_, (inv_facts hj).1, rfl⟩

theorem ppcAll {c : Nat} {bs : List Nat} (hc : PP 23 5 c) (hb : ∀ b ∈ bs, PP 23 5 b) :
    ∀ b ∈ cAll c bs, PP 23 5 b := by
  intro b hbb
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hbb
  exact PP_pcj hc hc.pinv (hb b' hb')

theorem conjAll_eq {c : Nat} {bs : List Nat} (hc : PP 23 5 c) (hb : ∀ b ∈ bs, PP 23 5 b) :
    conjAll (tabP 23 5 c) (bs.map (tabP 23 5)) = (cAll c bs).map (tabP 23 5) := by
  rw [conjAll, cAll, invT_tabP hc, List.map_map, List.map_map]
  exact List.map_congr_left fun b hbb => conjTab_tabP hc hc.pinv (hb b hbb)

theorem cA (wd : List Int) (ws : List (List Int)) :
    conjAll (wordT 23 gensT wd) (ws.map (wordT 23 gensT)) =
      (cAll (pw wd) (ws.map pw)).map (tabP 23 5) := by
  rw [wordT_eq, mapW]
  exact conjAll_eq (ppw' wd) (ppL ws)

theorem cands5_eq : cands5 = C5.map (List.map (tabP 23 5)) := by
  simp only [cands5, C5, candT, cnd, CFSG.Quasithin.KGC31.M23.tT, tP,
    CFSG.Quasithin.KGC31.M23.wT, wP, cA, List.map_cons, List.map_nil]

theorem cands7_eq : cands7 = C7.map (List.map (tabP 23 5)) := by
  simp only [cands7, C7, candT, cnd, CFSG.Quasithin.KGC31.M23.eT, eP,
    CFSG.Quasithin.KGC31.M23.wT, wP, CFSG.Quasithin.KGC31.M23.sT, sP, cA, List.map_cons,
    List.map_nil]

theorem ppC5 : ∀ c ∈ C5, ∀ b ∈ c, PP 23 5 b := by
  simp only [C5, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_const,
    and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact ppcAll (ppw' _) (ppL _)

theorem ppC7 : ∀ c ∈ C7, ∀ b ∈ c, PP 23 5 b := by
  simp only [C7, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_const,
    and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact ppcAll (ppw' _) (ppL _)

theorem kOrdP : pord 23 5 5 X5 = true ∧ pord 23 5 7 X7 = true ∧ pord 23 5 11 X11 = true ∧
    pord 23 5 23 X23 = true := by
  have h := kOrd
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  exact ⟨a, b, c, d⟩

theorem ord5 : ordTest 23 5 x5T = true := by rw [x5T, wordT_eq, ordTest_tabP (ppw' w5)]; exact kOrdP.1
theorem ord7 : ordTest 23 7 x7T = true := by
  rw [x7T, wordT_eq, ordTest_tabP (ppw' w7)]; exact kOrdP.2.1
theorem ord11 : ordTest 23 11 x11T = true := by
  rw [x11T, wordT_eq, ordTest_tabP (ppw' w11)]; exact kOrdP.2.2.1
theorem ord23 : ordTest 23 23 x23T = true := by
  rw [x23T, wordT_eq, ordTest_tabP (ppw' w23)]; exact kOrdP.2.2.2

theorem orb5 : orbCheck 23 5 invs (powTabs 23 x5T 5) cands5 = true := by
  rw [x5T, wordT_eq, cands5_eq, orbCheck_powTabs hsz (ppw' w5) (by norm_num) kOrdP.1 ppC5 hI,
    orbCheck, List.all_cons, List.all_nil, Bool.and_true, invOK_tabP (ppw' w5), Bool.true_and,
    List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [orbOne_tabP hsz (ppw' w5) (inv_facts hj).1 ppC5]
  exact (inv_facts hj).2.1

theorem orb7 : orbCheck 23 7 invs (powTabs 23 x7T 7) cands7 = true := by
  rw [x7T, wordT_eq, cands7_eq, orbCheck_powTabs hsz (ppw' w7) (by norm_num) kOrdP.2.1 ppC7 hI,
    orbCheck, List.all_cons, List.all_nil, Bool.and_true, invOK_tabP (ppw' w7), Bool.true_and,
    List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [orbOne_tabP hsz (ppw' w7) (inv_facts hj).1 ppC7]
  exact (inv_facts hj).2.2.1

theorem act11 : actCheck 23 11 invs (powTabs 23 x11T 11) = true := by
  rw [x11T, wordT_eq, actCheck_powTabs (ppw' w11) (by norm_num) kOrdP.2.2.1 hI, actCheck,
    List.all_cons, List.all_nil, Bool.and_true, invOK_tabP (ppw' w11), Bool.true_and,
    List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [actOne_tabP (ppw' w11) (inv_facts hj).1]
  exact (inv_facts hj).2.2.2.1

theorem act23 : actCheck 23 23 invs (powTabs 23 x23T 23) = true := by
  rw [x23T, wordT_eq, actCheck_powTabs (ppw' w23) (by norm_num) kOrdP.2.2.2 hI, actCheck,
    List.all_cons, List.all_nil, Bool.and_true, invOK_tabP (ppw' w23), Bool.true_and,
    List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [actOne_tabP (ppw' w23) (inv_facts hj).1]
  exact (inv_facts hj).2.2.2.2

theorem candInv : ((List.range 8).all fun k => invOK 23 (candT k) (invT 23 (candT k))) = true := by
  rw [List.all_eq_true]
  intro k _
  rw [candT, wordT_eq]
  exact invOK_tabP (ppw' _)

theorem kCosP : pcosetOK 23 5 B0 (wW.map pw) (wCosetW.map pw) = true ∧
    pcosetOK 23 5 B0 (tW.map pw) (tCosetW.map pw) = true ∧
    pcosetOK 23 5 B0 (eW.map pw) (eCosetW.map pw) = true := by
  have h := kCos
  unfold wP tP eP at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨a, b⟩, c⟩ := h
  exact ⟨a, b, c⟩

theorem cosOK (ws rs : List (List Int)) :
    cosetOK 23 b0T (ws.map (wordT 23 gensT)) (rs.map (wordT 23 gensT)) =
      pcosetOK 23 5 B0 (ws.map pw) (rs.map pw) := by
  rw [b0T, wordT_eq, mapW, mapW]
  exact cosetOK_tabP hsz (ppw' _) (ppL ws) (ppL rs)

theorem cosW : cosetOK 23 b0T wT wCosetT = true := (cosOK wW wCosetW).trans kCosP.1
theorem cosT : cosetOK 23 b0T tT tCosetT = true := (cosOK tW tCosetW).trans kCosP.2.1
theorem cosE : cosetOK 23 b0T eT eCosetT = true := (cosOK eW eCosetW).trans kCosP.2.2

theorem tab_img (w : List Int) : imageList (tab (wordG gensG w)) = (unpack 23 5 (pw w)).toList := by
  rw [tab_eq]
  refine imageList_of_rep (ppw' w).1 ?_
  rw [← wordT_eq]
  exact Rep.wordT hn23 w fun l _ => hrep l

theorem toTable_tab (w : List Int) : toTable (tab (wordG gensG w)) = tabP 23 5 (pw w) :=
  CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img (tab_img w)

theorem gens_img {ws : List (List Int)} {S : Nat → Nat} {m : Nat} (hl : ws.length = m)
    (h : (List.range m).all (fun j => Nat.beq (S j) (pw (ws.getD j []))) = true) :
    ∀ j < (ws.map fun w => tab (wordG gensG w)).length,
      imageList ((ws.map fun w => tab (wordG gensG w)).getD j 1) = (unpack 23 5 (S j)).toList := by
  intro j hj
  have hj' : j < ws.length := by simpa using hj
  rw [List.getD_eq_getElem _ _ hj, List.getElem_map, tab_img, ← List.getD_eq_getElem _ [] hj',
    Nat.eq_of_beq_eq_true (List.all_eq_true.1 h j (List.mem_range.2 (hl ▸ hj')))]

theorem kGensP : (List.range 2).all (fun j => Nat.beq (CW.S j) (pw (wGenW.getD j []))) = true ∧
    (List.range 2).all (fun j => Nat.beq (CT.S j) (pw (tGenW.getD j []))) = true ∧
    (List.range 2).all (fun j => Nat.beq (CE.S j) (pw (eGenW.getD j []))) = true := by
  have h := kGens
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨a, b⟩, c⟩ := h
  exact ⟨a, b, c⟩

theorem chainW : ChainK 23 5 wGen wChainW (#v[0, 1, 2, 3, 5] : Vector (Fin 23) 5)
    CW.S CW.SI CW.LR CW.TR CW.TRI 9 CW.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.1, by decide, CW.head, CW.hl,
    by norm_num, CW.hs⟩

theorem chainT : ChainK 23 5 tGen tChainW (#v[1, 2, 3] : Vector (Fin 23) 3)
    CT.S CT.SI CT.LR CT.TR CT.TRI 4 CT.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.2.1, by decide, CT.head, CT.hl,
    by norm_num, CT.hs⟩

theorem chainE : ChainK 23 5 eGen eChainW (#v[0, 1, 2] : Vector (Fin 23) 3)
    CE.S CE.SI CE.LR CE.TR CE.TRI 8 CE.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.2.2, by decide, CE.head, CE.hl,
    by norm_num, CE.hs⟩

theorem kOrdCP : ordK CW.LR 5 = 40320 ∧ ordK CT.LR 3 = 960 ∧ ordK CE.LR 3 = 1344 := by
  have h := kOrdC
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨a, b⟩, c⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c⟩

theorem chW : wChain.check = true ∧ wChain.orderCertificate = 40320 := by
  obtain ⟨a, b⟩ := chainK_check (by decide) (by decide) chainW
  exact ⟨a, b.trans kOrdCP.1⟩

theorem chT : tChain.check = true ∧ tChain.orderCertificate = 960 := by
  obtain ⟨a, b⟩ := chainK_check (by decide) (by decide) chainT
  exact ⟨a, b.trans kOrdCP.2.1⟩

theorem chE : eChain.check = true ∧ eChain.orderCertificate = 1344 := by
  obtain ⟨a, b⟩ := chainK_check (by decide) (by decide) chainE
  exact ⟨a, b.trans kOrdCP.2.2⟩

theorem mzW (ws : List (List Int)) (gs : List (List Int)) (ms : List (List Nat)) :
    ((gs.map fun w => tab (wordG gensG w)).zip ms).all
        (fun p => masksOK 23 (ws.map (wordT 23 gensT)) (toTable p.1) p.2) =
      ((gs.map pw).zip ms).all (fun p => pmasksOK 23 5 (ws.map pw) p.1 p.2) := by
  rw [mapW, List.zip_map_left, List.zip_map_left, List.all_map, List.all_map]
  refine all_congr' fun p _ => ?_
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
  rw [toTable_tab, masksOK_tabP hsz (ppL ws) (ppw' _)]

theorem kMasksP : ((wGenW.map pw).zip wMasks).all (fun p => pmasksOK 23 5 (wW.map pw) p.1 p.2) =
      true ∧
    ((tGenW.map pw).zip tMasks).all (fun p => pmasksOK 23 5 (tW.map pw) p.1 p.2) = true ∧
    ((eGenW.map pw).zip eMasks).all (fun p => pmasksOK 23 5 (eW.map pw) p.1 p.2) = true := by
  have h := kMasks
  unfold wP tP eP at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨a, b⟩, c⟩ := h
  exact ⟨a, b, c⟩

theorem mW : (wGen.zip wMasks).all (fun p => masksOK 23 wT (toTable p.1) p.2) = true :=
  (mzW wW wGenW wMasks).trans kMasksP.1
theorem mT : (tGen.zip tMasks).all (fun p => masksOK 23 tT (toTable p.1) p.2) = true :=
  (mzW tW tGenW tMasks).trans kMasksP.2.1
theorem mE : (eGen.zip eMasks).all (fun p => masksOK 23 eT (toTable p.1) p.2) = true :=
  (mzW eW eGenW eMasks).trans kMasksP.2.2

theorem fixPts_tabP {X : Nat} (hX : PP 23 5 X) {pts : List Nat} (hp : ∀ i ∈ pts, i < 23) :
    fixesAll (tabP 23 5 X) pts = pfix pts X := by
  rw [fixesAll, pfix]
  exact all_congr' fun i hi => by rw [ap_tabP' hX (hp i hi), beq_nat]

theorem fixG : (tGen.all fun g => fixesAll (toTable g) triT) = true := by
  rw [tGen, List.all_map]
  have h := kFixG
  rw [List.all_map] at h
  rw [← h]
  refine all_congr' fun w _ => ?_
  simp only [Function.comp_apply]
  rw [toTable_tab, fix_tabP (ppw' w)]

theorem fixSet_tabP {bs : List Nat} (hb : ∀ b ∈ bs, PP 23 5 b) (pts : List Nat) :
    fixSetIs 23 (bs.map (tabP 23 5)) pts = pfixSet bs pts := by
  rw [fixSetIs, pfixSet]
  refine all_congr' fun i hi => ?_
  have e : ((bs.map (tabP 23 5)).all fun b => ap b i == i) =
      bs.all fun b => Nat.beq (pg 5 (mask 5) b i) i := by
    rw [List.all_map]
    exact all_congr' fun b hbb => by
      simp only [Function.comp_apply]
      rw [ap_tabP' (hb b hbb) (List.mem_range.1 hi), beq_nat]
  rw [e]

theorem kFixSetP : pfixSet (wW.map pw) hexH = true ∧ pfixSet (tW.map pw) triT = true := by
  have h := kFixSet
  unfold wP tP at h
  simp only [Bool.and_eq_true] at h
  exact h

theorem fsW : fixSetIs 23 wT hexH = true := by
  rw [CFSG.Quasithin.KGC31.M23.wT, mapW, fixSet_tabP (ppL wW)]
  exact kFixSetP.1

theorem fsT : fixSetIs 23 tT triT = true := by
  rw [CFSG.Quasithin.KGC31.M23.tT, mapW, fixSet_tabP (ppL tW)]
  exact kFixSetP.2

theorem ppTRW : ∀ L ∈ trPL 23 5 CW.LR CW.TR 5, ∀ t ∈ L, PP 23 5 t := fun L hL t ht =>
  PP_of_permOK hsz (List.all_eq_true.1 (List.all_eq_true.1 kTRW L hL) t ht)

theorem hexL : levelTables wChain = (trPL 23 5 CW.LR CW.TR 5).map (List.map (tabP 23 5)) :=
  levelTables_eq chainW (by decide) (by decide)

theorem hexP : ∀ i ∈ hexH, i < 23 := by decide

theorem hexE : countProducts 23 (fun g => fixesAll g hexH)
    ((trPL 23 5 CW.LR CW.TR 5).map (List.map (tabP 23 5))) (tabP 23 5 (pidn 23 5)) =
      pcountProducts 23 5 (pfix hexH) (trPL 23 5 CW.LR CW.TR 5) (pidn 23 5) :=
  countProducts_tabP (f := fun g => fixesAll g hexH) (fk := pfix hexH)
    (fun X hX => fixPts_tabP hX hexP) _ ppTRW _ (PP.id hsz)

theorem hex : countProducts 23 (fun g => fixesAll g hexH) (levelTables wChain) (idT 23) = 16 := by
  have e := hexE
  rw [← hexL, ← idT_tabP hsz, Nat.eq_of_beq_eq_true kHex] at e
  exact e

theorem sIn : (sT.length == sInW.length &&
    (sT.zip sInW).all fun p => tblEq 23 p.1 (maskProd 23 wT p.2)) = true := by
  have h := kSIn
  unfold sP wP at h
  rw [CFSG.Quasithin.KGC31.M23.sT, CFSG.Quasithin.KGC31.M23.wT, mapW, mapW, List.zip_map_left,
    List.all_map]
  rw [Bool.and_eq_true]
  refine ⟨by decide, ?_⟩
  rw [← h]
  refine all_congr' fun p hp => ?_
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
  have hp1 : PP 23 5 p.1 := ppL sW _ (List.of_mem_zip hp).1
  rw [maskProd_tabP hsz _ (ppL wW), tblEq_tabP hp1 (PP_pmask hsz _ (ppL wW) _)]

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M23 in
open Certificates in
theorem cert7210 : ordTest 23 5 x5T = true ∧ ordTest 23 7 x7T = true ∧ ordTest 23 11 x11T = true ∧
    ordTest 23 23 x23T = true ∧
    orbCheck 23 5 invs (powTabs 23 x5T 5) cands5 = true ∧
    orbCheck 23 7 invs (powTabs 23 x7T 7) cands7 = true ∧
    actCheck 23 11 invs (powTabs 23 x11T 11) = true ∧
    actCheck 23 23 invs (powTabs 23 x23T 23) = true ∧
    ((List.range 8).all fun k => invOK 23 (candT k) (invT 23 (candT k))) = true ∧
    ebasisOK 23 wT = true ∧ ebasisOK 23 tT = true ∧ ebasisOK 23 eT = true ∧
    ebasisOK 23 sT = true ∧
    cbT.countP (commAll 23 wT) = 16 ∧ cbT.countP (commAll 23 tT) = 16 ∧
    cbT.countP (commAll 23 eT) = 8 ∧ cbT.countP (commAll 23 sT) = 16 ∧
    cosetOK 23 b0T wT wCosetT = true ∧ cosetOK 23 b0T tT tCosetT = true ∧
    cosetOK 23 b0T eT eCosetT = true ∧
    cosetCount 23 cbT wCosetT (normAll 23 wT) = 40320 ∧
    cosetCount 23 cbT tCosetT (fun g => normAll 23 tT g && fixesAll g triT) = 960 ∧
    cosetCount 23 cbT eCosetT (normAll 23 eT) = 1344 ∧
    wChain.check = true ∧ wChain.orderCertificate = 40320 ∧
    tChain.check = true ∧ tChain.orderCertificate = 960 ∧
    eChain.check = true ∧ eChain.orderCertificate = 1344 ∧
    (wGen.zip wMasks).all (fun p => masksOK 23 wT (toTable p.1) p.2) = true ∧
    (tGen.zip tMasks).all (fun p => masksOK 23 tT (toTable p.1) p.2) = true ∧
    (eGen.zip eMasks).all (fun p => masksOK 23 eT (toTable p.1) p.2) = true ∧
    (tGen.all fun g => fixesAll (toTable g) triT) = true ∧
    fixSetIs 23 wT hexH = true ∧ fixSetIs 23 tT triT = true ∧
    countProducts 23 (fun g => fixesAll g hexH) (levelTables wChain) (idT 23) = 16 ∧
    (sT.length == sInW.length && (sT.zip sInW).all fun p => tblEq 23 p.1 (maskProd 23 wT p.2)) =
      true :=
  ⟨ord5, ord7, ord11, ord23, orb5, orb7, act11, act23, candInv, eb.1, eb.2.1, eb.2.2.1, eb.2.2.2,
    cnt.1, cnt.2.1, cnt.2.2.1, cnt.2.2.2, cosW, cosT, cosE, cos_w, cos_t, cos_e, chW.1, chW.2,
    chT.1, chT.2, chE.1, chE.2, mW, mT, mE, fixG, fsW, fsT, hex, sIn⟩

end CertificateChecks.KernelKGC31M23

end

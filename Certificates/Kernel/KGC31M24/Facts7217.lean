module

public import Certificates.Kernel.KGC31M24.Facts7216
public import Certificates.Kernel.KGC31M24.Checks7217
public import Certificates.Kernel.KGC31M24.Cnt
public import Certificates.Kernel.KGC31M24.CosK
public import CFSG.Certificates.Kernel.KGC31PBSound
public import CFSG.Certificates.Kernel.KGC31PNormSound
public import CFSG.Quasithin.Vol2.KGFactC31M24Data
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3 CFSG.KC.BfsPin
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M24 CFSG.Sporadic.Mathieu
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M24OC
open CFSG.KS.SporSch.MOC CFSG.Monster.B.Mathieu CFSG.Certificates

theorem tab_img (w : List Int) : imageList (tab (wordG gensG w)) = (unpack 24 5 (pw w)).toList := by
  rw [tab_eq]
  exact imgW w

theorem toTable_tab (w : List Int) : toTable (tab (wordG gensG w)) = tabP 24 5 (pw w) :=
  CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img (tab_img w)

theorem cj_img (g y : List Int) :
    imageList (tab (wordG gensG g * wordG gensG y * (wordG gensG g)⁻¹)) =
      (unpack 24 5 (wcj g y)).toList := by
  rw [tab_eq]
  have hp := ppw' g
  exact mulK_rep hsz (mulK_rep hsz (imgW g) (imgW y))
    (invK_rep (imgW g) (CFSG.KS.PinvS.permOK_pinvS hp.1 hp.2))

theorem gens_img {ws : List (List Int)} {S : Nat → Nat} {m : Nat} (hl : ws.length = m)
    (h : (List.range m).all (fun j => Nat.beq (S j) (pw (ws.getD j []))) = true) :
    ∀ j < (ws.map fun w => tab (wordG gensG w)).length,
      imageList ((ws.map fun w => tab (wordG gensG w)).getD j 1) = (unpack 24 5 (S j)).toList := by
  intro j hj
  have hj' : j < ws.length := by simpa using hj
  rw [List.getD_eq_getElem _ _ hj, List.getElem_map, tab_img, ← List.getD_eq_getElem _ [] hj',
    Nat.eq_of_beq_eq_true (List.all_eq_true.1 h j (List.mem_range.2 (hl ▸ hj')))]

theorem cgens_img {ws : List (List Int)} {y : List Int} {S : Nat → Nat} {m : Nat}
    (hl : ws.length = m)
    (h : (List.range m).all (fun j => Nat.beq (S j) (wcj (ws.getD j []) y)) = true) :
    ∀ j < (ws.map fun w => tab (wordG gensG w * wordG gensG y * (wordG gensG w)⁻¹)).length,
      imageList ((ws.map fun w => tab (wordG gensG w * wordG gensG y * (wordG gensG w)⁻¹)).getD j 1) =
        (unpack 24 5 (S j)).toList := by
  intro j hj
  have hj' : j < ws.length := by simpa using hj
  rw [List.getD_eq_getElem _ _ hj, List.getElem_map, cj_img, ← List.getD_eq_getElem _ [] hj',
    Nat.eq_of_beq_eq_true (List.all_eq_true.1 h j (List.mem_range.2 (hl ▸ hj')))]

theorem kGensP : ((List.range 2).all (fun j => Nat.beq (CMO.S j) (pw (moGenW.getD j []))) = true ∧
    (List.range 2).all (fun j => Nat.beq (CNS.S j) (pw (nsGenW.getD j []))) = true ∧
    (List.range 3).all (fun j => Nat.beq (CLS.S j) (wcj (njW.getD j []) y5W)) = true ∧
    (List.range 2).all (fun j => Nat.beq (CNQ.S j) (pw (nqGenW.getD j []))) = true ∧
    (List.range 3).all (fun j => Nat.beq (CLQ.S j) (wcj (mjW.getD j []) y7W)) = true ∧
    (List.range 2).all (fun j => Nat.beq (CNT.S j) (pw (ntGenW.getD j []))) = true ∧
    (List.range 2).all (fun j => Nat.beq (CKQ.S j) (pw (kqGenW.getD j []))) = true) := by
  have h := kGens
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩ := h
  exact ⟨a, b, c, d, e, f, g⟩

theorem chainMO : ChainK 24 5 moGen moChainW (#v[0, 1, 2, 3, 4] : Vector (Fin 24) 5)
    CMO.S CMO.SI CMO.LR CMO.TR CMO.TRI 8 CMO.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.1, by decide, CMO.head,
    CMO.hl, by norm_num, CMO.hs⟩

theorem chainNS : ChainK 24 5 nsGen nsChainW (#v[0, 1, 2, 3, 4, 5] : Vector (Fin 24) 6)
    CNS.S CNS.SI CNS.LR CNS.TR CNS.TRI 9 CNS.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.2.1, by decide, CNS.head,
    CNS.hl, by norm_num, CNS.hs⟩

theorem chainLS : ChainK 24 5 lsGen lsChainW (#v[0, 1, 2, 3, 4] : Vector (Fin 24) 5)
    CLS.S CLS.SI CLS.LR CLS.TR CLS.TRI 10 CLS.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, cgens_img rfl kGensP.2.2.1, by decide, CLS.head,
    CLS.hl, by norm_num, CLS.hs⟩

theorem chainNQ : ChainK 24 5 nqGen nqChainW (#v[0, 1, 2, 3, 4] : Vector (Fin 24) 5)
    CNQ.S CNQ.SI CNQ.LR CNQ.TR CNQ.TRI 7 CNQ.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.2.2.2.1, by decide, CNQ.head,
    CNQ.hl, by norm_num, CNQ.hs⟩

theorem chainLQ : ChainK 24 5 lqGen lqChainW (#v[0, 1, 2, 3, 4] : Vector (Fin 24) 5)
    CLQ.S CLQ.SI CLQ.LR CLQ.TR CLQ.TRI 7 CLQ.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, cgens_img rfl kGensP.2.2.2.2.1, by decide, CLQ.head,
    CLQ.hl, by norm_num, CLQ.hs⟩

theorem chainNT : ChainK 24 5 ntGen ntChainW (#v[0, 1, 2, 3, 4] : Vector (Fin 24) 5)
    CNT.S CNT.SI CNT.LR CNT.TR CNT.TRI 6 CNT.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.2.2.2.2.2.1, by decide, CNT.head,
    CNT.hl, by norm_num, CNT.hs⟩

theorem chainKQ : ChainK 24 5 kqGen kqChainW (#v[0, 1, 2, 3, 4] : Vector (Fin 24) 5)
    CKQ.S CKQ.SI CKQ.LR CKQ.TR CKQ.TRI 9 CKQ.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.2.2.2.2.2.2, by decide, CKQ.head,
    CKQ.hl, by norm_num, CKQ.hs⟩

theorem kOrdP : ordK CMO.LR 5 = 322560 ∧ ordK CNS.LR 6 = 138240 ∧ ordK CLS.LR 5 = 69120 ∧
    ordK CNQ.LR 5 = 21504 ∧ ordK CLQ.LR 5 = 10752 ∧ ordK CNT.LR 5 = 64512 ∧
    ordK CKQ.LR 5 = 21504 := by
  have h := kOrd
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c,
    Nat.eq_of_beq_eq_true d, Nat.eq_of_beq_eq_true e, Nat.eq_of_beq_eq_true f,
    Nat.eq_of_beq_eq_true g⟩

theorem g4 : (moChain.check && (moChain.orderCertificate == 322560) && nsChain.check &&
      (nsChain.orderCertificate == 138240) && lsChain.check &&
      (lsChain.orderCertificate == 69120) && qChain.check && (qChain.orderCertificate == 128) &&
      nqChain.check && (nqChain.orderCertificate == 21504) && lqChain.check &&
      (lqChain.orderCertificate == 10752) && ntChain.check && (ntChain.orderCertificate == 64512) &&
      kqChain.check && (kqChain.orderCertificate == 21504)) = true := by
  obtain ⟨mo1, mo2⟩ := chainK_check (by decide) (by decide) chainMO
  obtain ⟨ns1, ns2⟩ := chainK_check (by decide) (by decide) chainNS
  obtain ⟨ls1, ls2⟩ := chainK_check (by decide) (by decide) chainLS
  obtain ⟨q1, q2⟩ := chainK_check (by decide) (by decide) chainQ
  obtain ⟨nq1, nq2⟩ := chainK_check (by decide) (by decide) chainNQ
  obtain ⟨lq1, lq2⟩ := chainK_check (by decide) (by decide) chainLQ
  obtain ⟨nt1, nt2⟩ := chainK_check (by decide) (by decide) chainNT
  obtain ⟨kq1, kq2⟩ := chainK_check (by decide) (by decide) chainKQ
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := kOrdP
  have oq := Nat.eq_of_beq_eq_true kQN
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨mo1, mo2.trans o1⟩, ns1⟩, ns2.trans o2⟩, ls1⟩, ls2.trans o3⟩, q1⟩,
    q2.trans oq⟩, nq1⟩, nq2.trans o4⟩, lq1⟩, lq2.trans o5⟩, nt1⟩, nt2.trans o6⟩, kq1⟩,
    kq2.trans o7⟩

theorem countP_congr' {α : Type} : ∀ {l : List α} {f g : α → Bool}, (∀ a ∈ l, f a = g a) →
    l.countP f = l.countP g
  | [], _, _, _ => rfl
  | a :: l, f, g, H => by
    rw [List.countP_cons, List.countP_cons, H a List.mem_cons_self,
      countP_congr' fun b hb => H b (List.mem_cons_of_mem _ hb)]

theorem ppTR {LR TR : Nat → Nat} {k : Nat}
    (h : (trPL 24 5 LR TR k).all (fun L => L.all fun t =>
      permOK 24 5 (mask 5) (24 * 5) t (pinv 24 5 t)) = true) :
    ∀ L ∈ trPL 24 5 LR TR k, ∀ t ∈ L, PP 24 5 t := fun L hL t ht =>
  PP_of_permOK hsz (List.all_eq_true.1 (List.all_eq_true.1 h L hL) t ht)

theorem kTRP : (∀ L ∈ trPL 24 5 M24C2.LR M24C2.TR 4, ∀ t ∈ L, PP 24 5 t) ∧
    (∀ L ∈ trPL 24 5 M24C1.LR M24C1.TR 3, ∀ t ∈ L, PP 24 5 t) ∧
    (∀ L ∈ trPL 24 5 CLQ.LR CLQ.TR 5, ∀ t ∈ L, PP 24 5 t) ∧
    (∀ L ∈ trPL 24 5 CLS.LR CLS.TR 5, ∀ t ∈ L, PP 24 5 t) := by
  have h := kTR
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  exact ⟨ppTR a, ppTR b, ppTR c, ppTR d⟩

theorem ppcb0 : ∀ c ∈ cb0P, PP 24 5 c :=
  PP_pfilterProducts hsz _ kTRP.1 _ [] (PP.id hsz) (fun _ h => absurd h List.not_mem_nil)

theorem ppcb1 : ∀ c ∈ cb1P, PP 24 5 c :=
  PP_pfilterProducts hsz _ kTRP.2.1 _ [] (PP.id hsz) (fun _ h => absurd h List.not_mem_nil)

theorem allTables_eq {Q : RawSchreierDatum 24} {Ls : List (List Nat)}
    (hL : levelTables Q = Ls.map (List.map (tabP 24 5))) (hP : ∀ L ∈ Ls, ∀ t ∈ L, PP 24 5 t) :
    allTables Q = (pfilterProducts 24 5 (fun _ => true) Ls (pidn 24 5) []).map (tabP 24 5) := by
  rw [allTables, hL, idT_tabP hsz]
  have := filterProducts_tabP (f := allTrue) (fk := fun _ => true) (fun _ _ => rfl) Ls hP
    (pidn 24 5) [] (PP.id hsz)
  rwa [List.map_nil] at this

theorem cb0T_eq : cb0T = cb0P.map (tabP 24 5) := by
  have hL : levelTables m24CentQ2 = (trPL 24 5 M24C2.LR M24C2.TR 4).map (List.map (tabP 24 5)) :=
    levelTables_eq chainC2 (by decide) (by decide)
  exact allTables_eq hL kTRP.1

theorem cb1T_eq : cb1T = cb1P.map (tabP 24 5) := by
  have hL : levelTables m24CentQ1 = (trPL 24 5 M24C1.LR M24C1.TR 3).map (List.map (tabP 24 5)) :=
    levelTables_eq chainC1 (by decide) (by decide)
  exact allTables_eq hL kTRP.2.1

theorem cntW {cP : List Nat} (hc : ∀ c ∈ cP, PP 24 5 c) (ws : List (List Int)) :
    (cP.map (tabP 24 5)).countP (commAll 24 (ws.map (wordT 24 gensT))) =
      cP.countP (pcommAll 24 5 (ws.map pw)) := by
  rw [mapW, List.countP_map]
  exact countP_congr' fun c hcc => commAll_tabP (ppL ws) (hc c hcc)

theorem cntW' {cP : List Nat} (hc : ∀ c ∈ cP, PP 24 5 c) (ws : List (List Int)) {bs : List Nat}
    (hb : ws.map pw = bs) :
    (cP.map (tabP 24 5)).countP (commAll 24 (ws.map (wordT 24 gensT))) =
      cP.countP (pcommAll 24 5 bs) := by
  rw [cntW hc ws, hb]

theorem kB : (Nat.beq b0P (M24CK.getD 1 CFSG.KS.SporSch.MOC.clsD0).R &&
    Nat.beq b1P (M24CK.getD 0 CFSG.KS.SporSch.MOC.clsD0).R &&
    permOK 24 5 (mask 5) (24 * 5) (M24CK.getD 0 CFSG.KS.SporSch.MOC.clsD0).R
      (pinv 24 5 (M24CK.getD 0 CFSG.KS.SporSch.MOC.clsD0).R) &&
    permOK 24 5 (mask 5) (24 * 5) (M24CK.getD 1 CFSG.KS.SporSch.MOC.clsD0).R
      (pinv 24 5 (M24CK.getD 1 CFSG.KS.SporSch.MOC.clsD0).R)) = true := by quickRfl

theorem ebW (ws : List (List Int)) :
    ebasisOK 24 (ws.map (wordT 24 gensT)) = pebasis 24 5 (ws.map pw) := by
  rw [mapW]
  exact ebasisOK_tabP hsz (ppL ws)

theorem g1 : ((tblEq 24 b0T (toTable (m24InvReps.getD 1 1))) &&
      (tblEq 24 b1T (toTable (m24InvReps.getD 0 1))) && (ebasisOK 24 oT) && (ebasisOK 24 sT) &&
      (ebasisOK 24 s16T) && (ebasisOK 24 s32T) && (ebasisOK 24 r2T) && (ebasisOK 24 u4T) &&
      (ebasisOK 24 u5T) && (ebasisOK 24 u6T) && (ebasisOK 24 tT) && (ebasisOK 24 etT)) = true := by
  have hB := kB
  simp only [Bool.and_eq_true] at hB
  obtain ⟨⟨⟨e0, e1⟩, p0⟩, p1⟩ := hB
  have hE := kEb
  simp only [Bool.and_eq_true] at hE
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩ := hE
  have h0 : tblEq 24 b0T (toTable (m24InvReps.getD 1 1)) = true := by
    rw [b0T, wT, CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img imgRep1]
    rw [tblEq_tabP (ppw' _) (PP_of_permOK hsz p1)]
    exact e0
  have h1 : tblEq 24 b1T (toTable (m24InvReps.getD 0 1)) = true := by
    rw [b1T, wT, CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img imgRep0]
    rw [tblEq_tabP (ppw' _) (PP_of_permOK hsz p0)]
    exact e1
  have q1 : ebasisOK 24 oT = true := by rw [oT, ebW]; exact a1
  have q2 : ebasisOK 24 sT = true := by rw [sT, ebW]; exact a2
  have q3 : ebasisOK 24 s16T = true := by rw [s16T, ebW]; exact a3
  have q4 : ebasisOK 24 s32T = true := by rw [s32T, ebW]; exact a4
  have q5 : ebasisOK 24 r2T = true := by rw [r2T, ebW]; exact a5
  have q6 : ebasisOK 24 u4T = true := by rw [u4T, ebW]; exact a6
  have q7 : ebasisOK 24 u5T = true := by rw [u5T, ebW]; exact a7
  have q8 : ebasisOK 24 u6T = true := by rw [u6T, ebW]; exact a8
  have q9 : ebasisOK 24 tT = true := by rw [tT, ebW]; exact a9
  have q10 : ebasisOK 24 etT = true := by rw [etT, ebW]; exact a10
  simp only [h0, h1, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, Bool.and_self]

theorem g2 : ((cb0T.countP (commAll 24 oT) == 16) && (cb0T.countP (commAll 24 sT) == 64) &&
      (cb0T.countP (commAll 24 s16T) == 64) && (cb0T.countP (commAll 24 s32T) == 64) &&
      (cb0T.countP (commAll 24 r2T) == 16) && (cb0T.countP (commAll 24 u4T) == 16) &&
      (cb0T.countP (commAll 24 u5T) == 128) && (cb0T.countP (commAll 24 tT) == 64) &&
      (cb1T.countP (commAll 24 u6T) == 64)) = true := by
  have hC := kC2
  simp only [Bool.and_eq_true] at hC
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩ := hC
  have q1 : (cb0T.countP (commAll 24 oT) == 16) = true := by
    rw [cb0T_eq, oT, cntW' ppcb0 oW (bs := oP) rfl, beq_iff_eq, Nat.eq_of_beq_eq_true a1]
  have q2 : (cb0T.countP (commAll 24 sT) == 64) = true := by
    rw [cb0T_eq, sT, cntW' ppcb0 sW (bs := sP) rfl, beq_iff_eq, Nat.eq_of_beq_eq_true a2]
  have q3 : (cb0T.countP (commAll 24 s16T) == 64) = true := by
    rw [cb0T_eq, s16T, cntW' ppcb0 s16W (bs := s16P) rfl, beq_iff_eq,
      Nat.eq_of_beq_eq_true a3]
  have q4 : (cb0T.countP (commAll 24 s32T) == 64) = true := by
    rw [cb0T_eq, s32T, cntW' ppcb0 s32W (bs := s32P) rfl, beq_iff_eq,
      Nat.eq_of_beq_eq_true a4]
  have q5 : (cb0T.countP (commAll 24 r2T) == 16) = true := by
    rw [cb0T_eq, r2T, cntW' ppcb0 r2W (bs := r2P) rfl, beq_iff_eq, Nat.eq_of_beq_eq_true a5]
  have q6 : (cb0T.countP (commAll 24 u4T) == 16) = true := by
    rw [cb0T_eq, u4T, cntW' ppcb0 u4W (bs := u4P) rfl, beq_iff_eq, Nat.eq_of_beq_eq_true a6]
  have q7 : (cb0T.countP (commAll 24 u5T) == 128) = true := by
    rw [cb0T_eq, u5T, cntW' ppcb0 u5W (bs := u5P) rfl, beq_iff_eq, Nat.eq_of_beq_eq_true a7]
  have q8 : (cb0T.countP (commAll 24 tT) == 64) = true := by
    rw [cb0T_eq, tT, cntW' ppcb0 tW (bs := tP) rfl, beq_iff_eq, Nat.eq_of_beq_eq_true a8]
  have q9 : (cb1T.countP (commAll 24 u6T) == 64) = true := by
    rw [cb1T_eq, u6T, cntW' ppcb1 u6W (bs := u6P) rfl, beq_iff_eq,
      Nat.eq_of_beq_eq_true kC1]
  simp only [q1, q2, q3, q4, q5, q6, q7, q8, q9, Bool.and_self]

theorem allCommW (ws vs : List (List Int)) :
    (vs.map (wordT 24 gensT)).all (commAll 24 (ws.map (wordT 24 gensT))) =
      (vs.map pw).all (pcommAll 24 5 (ws.map pw)) := by
  rw [mapW vs, mapW ws]
  exact all_map_congr fun c hc => commAll_tabP (ppL ws) (ppL vs c hc)

theorem g3 : ((sT.all (commAll 24 s16T)) && (sT.all (commAll 24 s32T)) &&
      (invOK 24 d4T (invT 24 d4T)) && ((conjAll d4T r2T).all (commAll 24 u4T)) &&
      (invOK 24 d6T (invT 24 d6T)) && ((conjAll d6T tT).all (commAll 24 u6T)) &&
      (qGen.all fun g => commAll 24 u5T (toTable g))) = true := by
  have h := kG3
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := h
  have e3 : (conjAll d4T r2T).all (commAll 24 u4T) = true := by
    rw [d4T, r2T, cA, u4T, mapW]
    rw [all_map_congr fun c hc => commAll_tabP (ppL u4W) (ppcAll (ppw' d4W) (ppL r2W) c hc)]
    exact a3
  have e4 : (conjAll d6T tT).all (commAll 24 u6T) = true := by
    rw [d6T, tT, cA, u6T, mapW]
    rw [all_map_congr fun c hc => commAll_tabP (ppL u6W) (ppcAll (ppw' d6W) (ppL tW) c hc)]
    exact a4
  have e5 : (qGen.all fun g => commAll 24 u5T (toTable g)) = true := by
    rw [qGen, u5T, mapW, List.all_map]
    rw [all_congr' fun w _ => by
      simp only [Function.comp_apply]
      rw [toTable_tab w, commAll_tabP (ppL u5W) (ppw' w)]]
    have h5 := a5
    rw [List.all_map] at h5
    exact h5
  have e1 : sT.all (commAll 24 s16T) = true := by rw [sT, s16T, allCommW]; exact a1
  have e2 : sT.all (commAll 24 s32T) = true := by rw [sT, s32T, allCommW]; exact a2
  have i4 : invOK 24 d4T (invT 24 d4T) = true := by rw [d4T, wT]; exact invOK_tabP (ppw' _)
  have i6 : invOK 24 d6T (invT 24 d6T) = true := by rw [d6T, wT]; exact invOK_tabP (ppw' _)
  simp only [e1, e2, i4, e3, i6, e4, e5, Bool.and_self]

theorem mzW {bs : List Nat} (hb : ∀ b ∈ bs, PP 24 5 b) (ws : List (List Int)) (ms : List (List Nat)) :
    ((ws.map fun w => tab (wordG gensG w)).zip ms).all
        (fun p => masksOK 24 (bs.map (tabP 24 5)) (toTable p.1) p.2) =
      ((ws.map pw).zip ms).all (fun p => pmasksOK 24 5 bs p.1 p.2) := by
  rw [List.zip_map_left, List.zip_map_left, List.all_map, List.all_map]
  refine all_congr' fun p _ => ?_
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
  rw [toTable_tab, masksOK_tabP hsz hb (ppw' _)]

theorem mzT {bs : List Nat} (hb : ∀ b ∈ bs, PP 24 5 b) (ws : List (List Int)) (ms : List (List Nat)) :
    ((ws.map (wordT 24 gensT)).zip ms).all
        (fun p => masksOK 24 (bs.map (tabP 24 5)) p.1 p.2) =
      ((ws.map pw).zip ms).all (fun p => pmasksOK 24 5 bs p.1 p.2) := by
  rw [List.zip_map_left, List.zip_map_left, List.all_map, List.all_map]
  refine all_congr' fun p _ => ?_
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
  rw [wT, masksOK_tabP hsz hb (ppw' _)]

theorem kAbP : CFSG.Sporadic.Schreier.m24CentWords2.all (fun wd =>
    permOK 24 5 (mask 5) (24 * 5)
      (abWordK 24 5 (mask 5) (pidn 24 5) (M24Q.S 0) (M24Q.SI 0) (M24Q.S 1) (M24Q.SI 1) wd)
      (pinv 24 5 (abWordK 24 5 (mask 5) (pidn 24 5) (M24Q.S 0) (M24Q.SI 0) (M24Q.S 1) (M24Q.SI 1)
        wd))) = true := by quickRfl

theorem g5 : (((moGen.zip moMasks).all (fun p => masksOK 24 oT (toTable p.1) p.2)) &&
      ((nsGen.zip nsMasks).all (fun p => masksOK 24 sT (toTable p.1) p.2)) &&
      (masksOK 24 sT y5T y5Masks) && ((njT.zip njMasks).all (fun p => masksOK 24 sT p.1 p.2)) &&
      ((nqGen.zip nqMasks).all (fun p => masksOK 24 u5T (toTable p.1) p.2)) &&
      (masksOK 24 u5T y7T y7Masks) && ((mjT.zip mjMasks).all (fun p => masksOK 24 u5T p.1 p.2)) &&
      ((ntGen.zip ntMasks).all (fun p => masksOK 24 tT (toTable p.1) p.2)) &&
      (masksOK 24 tT qtT qtMasks) && ((kqT.zip kqMasks).all (fun p => masksOK 24 tT p.1 p.2)) &&
      ((cb0Gen.zip cb0Masks).all (fun p => masksOK 24 r2T (toTable p.1) p.2)) &&
      (ordTest 24 5 y5T) && (ordTest 24 7 y7T)) = true := by
  have h := kG5
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩ := h
  have hc := kCb0
  simp only [Bool.and_eq_true] at hc
  obtain ⟨c1, c2⟩ := hc
  have e11 : (cb0Gen.zip cb0Masks).all (fun p => masksOK 24 r2T (toTable p.1) p.2) = true := by
    rw [cb0Gen, r2T, mapW, List.zip_map_left, List.all_map]
    rw [List.zip_map_left, List.all_map] at c1
    rw [← c1]
    refine all_congr' fun p hp => ?_
    have hw : abOK p.1 = true := List.all_eq_true.1 c2 p.1 (List.of_mem_zip hp).1
    have himg := abWordK_rep hsz imgA imgB pA pB hw
    have hpp : PP 24 5 (abWordK 24 5 (mask 5) (pidn 24 5) (M24Q.S 0) (M24Q.SI 0) (M24Q.S 1)
        (M24Q.SI 1) p.1) :=
      PP_of_permOK hsz (List.all_eq_true.1 kAbP p.1 (List.of_mem_zip hp).1)
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
    rw [CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img himg, masksOK_tabP hsz (ppL r2W) hpp]
    rfl
  have m1 : (moGen.zip moMasks).all (fun p => masksOK 24 oT (toTable p.1) p.2) = true := by
    rw [moGen, oT, mapW oW, mzW (ppL oW)]; exact a1
  have m2 : (nsGen.zip nsMasks).all (fun p => masksOK 24 sT (toTable p.1) p.2) = true := by
    rw [nsGen, sT, mapW sW, mzW (ppL sW)]; exact a2
  have m3 : masksOK 24 sT y5T y5Masks = true := by
    rw [sT, y5T, mapW sW, wT, masksOK_tabP hsz (ppL sW) (ppw' _)]; exact a3
  have m4 : (njT.zip njMasks).all (fun p => masksOK 24 sT p.1 p.2) = true := by
    rw [njT, sT, mapW sW, mzT (ppL sW)]; exact a4
  have m5 : (nqGen.zip nqMasks).all (fun p => masksOK 24 u5T (toTable p.1) p.2) = true := by
    rw [nqGen, u5T, mapW u5W, mzW (ppL u5W)]; exact a5
  have m6 : masksOK 24 u5T y7T y7Masks = true := by
    rw [u5T, y7T, mapW u5W, wT, masksOK_tabP hsz (ppL u5W) (ppw' _)]; exact a6
  have m7 : (mjT.zip mjMasks).all (fun p => masksOK 24 u5T p.1 p.2) = true := by
    rw [mjT, u5T, mapW u5W, mzT (ppL u5W)]; exact a7
  have m8 : (ntGen.zip ntMasks).all (fun p => masksOK 24 tT (toTable p.1) p.2) = true := by
    rw [ntGen, tT, mapW tW, mzW (ppL tW)]; exact a8
  have m9 : masksOK 24 tT qtT qtMasks = true := by
    rw [tT, qtT, mapW tW, wT, masksOK_tabP hsz (ppL tW) (ppw' _)]; exact a9
  have m10 : (kqT.zip kqMasks).all (fun p => masksOK 24 tT p.1 p.2) = true := by
    rw [kqT, tT, mapW tW, mzT (ppL tW)]; exact a10
  have o5 : ordTest 24 5 y5T = true := by rw [y5T, wT, ordTest_tabP (ppw' _)]; exact a11
  have o7 : ordTest 24 7 y7T = true := by rw [y7T, wT, ordTest_tabP (ppw' _)]; exact a12
  simp only [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, e11, o5, o7, Bool.and_self]

theorem tets_lt : ∀ B ∈ tets, ∀ p ∈ B, p < 24 := by decide

theorem siftW {gens : List (Equiv.Perm (Fin 24))} {words : List (List Int)}
    {PS PSI LR TR TRI : Nat → Nat} {kS BP : Nat}
    (hQ : ChainK 24 5 gens words (#v[0, 1, 2, 3, 4] : Vector (Fin 24) 5) PS PSI LR TR TRI kS BP 2 16)
    {ws : List (List Int)}
    (h : ws.all (fun w => canonK 24 5 (mask 5) (24 * 5) (pw w) &&
      siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) LR TRI BP 5 0 (pw w)) = true) :
    (ws.all fun w => (certificate (by decide) gens words (#v[0, 1, 2, 3, 4] : Vector (Fin 24) 5)
      (by decide)).sift (tab (wordG gensG w)) 0) = true := by
  rw [List.all_eq_true]
  intro w hw
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 (List.all_eq_true.1 h w hw)
  exact chainK_sift (by decide) (by decide) hQ (tab_img w) h1 h2

theorem g6 : ((sW.all fun w => lsChain.sift (tab (wordG gensG w)) 0) &&
      (etW.all fun w => lqChain.sift (tab (wordG gensG w)) 0) && (etT.all (commAll 24 u5T)) &&
      (countProducts 24 (commAll 24 u5T) (levelTables lqChain) (idT 24) == 64) &&
      (blocksOK tets y5T) && (njT.all (blocksOK tets)) && (sT.all (fixesBlocks tets)) &&
      (countProducts 24 (fixesBlocks tets) (levelTables lsChain) (idT 24) == 192)) = true := by
  have hs := kSift
  simp only [Bool.and_eq_true] at hs
  obtain ⟨s1, s2⟩ := hs
  have h6 := kG6
  simp only [Bool.and_eq_true] at h6
  obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ := h6
  have e1 : (sW.all fun w => lsChain.sift (tab (wordG gensG w)) 0) = true := siftW chainLS s1
  have e2 : (etW.all fun w => lqChain.sift (tab (wordG gensG w)) 0) = true := siftW chainLQ s2
  have e3 : etT.all (commAll 24 u5T) = true := by rw [etT, u5T, allCommW]; exact b1
  have hLQ : levelTables lqChain = (trPL 24 5 CLQ.LR CLQ.TR 5).map (List.map (tabP 24 5)) :=
    levelTables_eq chainLQ (by decide) (by decide)
  have hLS : levelTables lsChain = (trPL 24 5 CLS.LR CLS.TR 5).map (List.map (tabP 24 5)) :=
    levelTables_eq chainLS (by decide) (by decide)
  have hf4 : ∀ X, PP 24 5 X → commAll 24 u5T (tabP 24 5 X) = pcommAll 24 5 u5P X :=
    fun X hX => by rw [u5T, mapW]; exact commAll_tabP (ppL u5W) hX
  have hf8 : ∀ X, PP 24 5 X → fixesBlocks tets (tabP 24 5 X) = pfixesBlocks 5 tets X :=
    fun X hX => fixesBlocks_tabP tets_lt hX
  have c4 := countProducts_tabP hf4 _ kTRP.2.2.1 _ (PP.id hsz)
  have c8 := countProducts_tabP hf8 _ kTRP.2.2.2 _ (PP.id hsz)
  have e4 : (countProducts 24 (commAll 24 u5T) (levelTables lqChain) (idT 24) == 64) = true := by
    rw [hLQ, idT_tabP hsz, c4, beq_iff_eq, Nat.eq_of_beq_eq_true kLq]
  have e8 : (countProducts 24 (fixesBlocks tets) (levelTables lsChain) (idT 24) == 192) = true := by
    rw [hLS, idT_tabP hsz, c8, beq_iff_eq, Nat.eq_of_beq_eq_true kLs]
  have e5 : blocksOK tets y5T = true := by
    rw [y5T, wT, blocksOK_tabP tets_lt (ppw' _)]; exact b2
  have e6 : njT.all (blocksOK tets) = true := by
    rw [njT, mapW, all_map_congr fun g hg => blocksOK_tabP tets_lt (ppL njW g hg)]; exact b3
  have e7 : sT.all (fixesBlocks tets) = true := by
    rw [sT, mapW, all_map_congr fun g hg => fixesBlocks_tabP tets_lt (ppL sW g hg)]; exact b4
  simp only [e1, e2, e3, e4, e5, e6, e7, e8, Bool.and_self]

theorem cos0All : ∀ c ∈ cb0P, pnormAll 24 5 r2P c (pinv 24 5 c) = true := by
  have h := kCos0
  unfold cos0K at h
  rw [Bool.and_eq_true] at h
  exact List.countP_eq_length.1 ((Nat.eq_of_beq_eq_true h.1).trans (Nat.eq_of_beq_eq_true h.2).symm)

theorem cosCnt (i : Nat) (hi : i < 15) :
    cb0P.countP (fun c => pnormAll 24 5 r2P (pc 24 5 (rsP.getD i 0) c)
      (pinv 24 5 (pc 24 5 (rsP.getD i 0) c))) = if i = 0 then 21504 else 0 := by
  have hk := kCosN
  unfold cosNK at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨e0, hok⟩, hneg⟩ := hk
  have hb : ∀ b ∈ r2P, PP 24 5 b := ppL r2W
  have hr : ∀ r ∈ rsP, PP 24 5 r := ppL r2CosetW
  have hl : rsP.length = 15 := by simp [rsP, r2CosetW]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [if_pos rfl, Nat.eq_of_beq_eq_true e0]
    have h := kCos0
    unfold cos0K at h
    rw [Bool.and_eq_true] at h
    rw [← Nat.eq_of_beq_eq_true h.1]
    exact countP_congr' fun c hc => by rw [pc_pidn hsz (ppcb0 c hc)]
  · rw [if_neg (by omega)]
    have hri : PP 24 5 (rsP.getD i 0) := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hr _ (List.getElem_mem _)
    refine countP_pnormAll_eq_zero hsz hb hok ppcb0 cos0All hri ?_
    have h := List.all_eq_true.1 hneg (i - 1) (List.mem_range.2 (by omega))
    rw [Nat.sub_add_cancel hpos, Bool.not_eq_true'] at h
    exact h

theorem sum_first {l : List Nat} {g : Nat → Nat} {c : Nat}
    (h : ∀ i < l.length, g (l.getD i 0) = if i = 0 then c else 0) (hl : 0 < l.length) :
    (l.map g).sum = c := by
  cases l with
  | nil => simp at hl
  | cons a t =>
    have h0 : g a = c := by
      have := h 0 (by simp)
      rwa [List.getD_cons_zero, if_pos rfl] at this
    have ht : ∀ x ∈ t, g x = 0 := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      have := h (j + 1) (by simp; omega)
      rwa [List.getD_cons_succ, List.getD_eq_getElem _ _ hj, if_neg (Nat.succ_ne_zero j)] at this
    have hs : (t.map g).sum = 0 := List.sum_eq_zero fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact ht x hx
    rw [List.map_cons, List.sum_cons, h0, hs, Nat.add_zero]

theorem cos_map : ∀ {l : List Nat}, (∀ r ∈ l, PP 24 5 r) →
    (l.map (tabP 24 5)).map (fun r => (cb0P.map (tabP 24 5)).countP fun c =>
        normAll 24 ((r2W.map pw).map (tabP 24 5)) (compT 24 r c)) =
      l.map (fun r => cb0P.countP fun c => pnormAll 24 5 r2P (pc 24 5 r c) (pinv 24 5 (pc 24 5 r c)))
  | [], _ => rfl
  | r :: l, h => by
    have hrp := h r List.mem_cons_self
    rw [List.map_cons, List.map_cons, List.map_cons,
      cos_map fun s hs => h s (List.mem_cons_of_mem _ hs), List.countP_map]
    congr 1
    refine countP_congr' fun c hc => ?_
    simp only [Function.comp_apply]
    rw [compT_tabP' hrp (ppcb0 c hc), normAll_tabP hsz (ppL r2W) (hrp.pc (ppcb0 c hc))]
    rfl

theorem g7 : (!(inSpan 24 tT qtT) && (inSpan 24 tT (compT 24 qtT qtT)) &&
      (invOK 24 qtT (invT 24 qtT)) &&
      (kqT.all fun k => invOK 24 k (invT 24 k) &&
        inSpan 24 tT (compT 24 (conjTab 24 k (invT 24 k) qtT) (invT 24 qtT))) &&
      (cosetOK 24 b0T r2T r2CosetT) &&
      (cosetCount 24 cb0T r2CosetT (normAll 24 r2T) == 21504)) = true := by
  have h := kG7
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := h
  have hq := ppw' qtW
  have e1 : (!(inSpan 24 tT qtT)) = true := by
    rw [tT, qtT, mapW, wT, inSpan_tabP hsz (ppL tW) hq]; exact a1
  have e2 : inSpan 24 tT (compT 24 qtT qtT) = true := by
    rw [tT, qtT, mapW, wT, compT_tabP' hq hq, inSpan_tabP hsz (ppL tW) (hq.pc hq)]; exact a2
  have e3 : invOK 24 qtT (invT 24 qtT) = true := by rw [qtT, wT]; exact invOK_tabP hq
  have e4 : (kqT.all fun k => invOK 24 k (invT 24 k) &&
      inSpan 24 tT (compT 24 (conjTab 24 k (invT 24 k) qtT) (invT 24 qtT))) = true := by
    rw [kqT, tT, qtT, mapW, mapW, wT, List.all_map, List.all_eq_true]
    intro k hk
    have hkp := ppL kqGenW k hk
    have hk' := List.all_eq_true.1 a3 k hk
    simp only [Function.comp_apply]
    rw [invOK_tabP hkp, Bool.true_and, invT_tabP hkp, invT_tabP hq, conjTab_tabP hkp hkp.pinv hq,
      compT_tabP' (PP_pcj hkp hkp.pinv hq) hq.pinv,
      inSpan_tabP hsz (ppL tW) ((PP_pcj hkp hkp.pinv hq).pc hq.pinv)]
    exact hk'
  have e5 : cosetOK 24 b0T r2T r2CosetT = true := by
    rw [b0T, r2T, r2CosetT, mapW, mapW, wT, cosetOK_tabP hsz (ppw' _) (ppL r2W) (ppL r2CosetW)]
    exact a4
  have e6 : (cosetCount 24 cb0T r2CosetT (normAll 24 r2T) == 21504) = true := by
    rw [cosetCount, cb0T_eq, r2CosetT, r2T, mapW, mapW, cos_map (ppL r2CosetW)]
    refine beq_iff_eq.2 (sum_first (fun i hi => ?_) (by simp [r2CosetW]))
    have hi' : i < 15 := by simpa [r2CosetW] using hi
    have hr : r2CosetW.map pw = rsP := rfl
    beta_reduce
    rw [hr]
    exact cosCnt i hi'
  simp only [e1, e2, e3, e4, e5, e6, Bool.and_self]

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M24 CFSG.Certificates in
open Certificates in
theorem cert7217 :
    ((tblEq 24 b0T (toTable (m24InvReps.getD 1 1))) &&
      (tblEq 24 b1T (toTable (m24InvReps.getD 0 1))) && (ebasisOK 24 oT) && (ebasisOK 24 sT) &&
      (ebasisOK 24 s16T) && (ebasisOK 24 s32T) && (ebasisOK 24 r2T) && (ebasisOK 24 u4T) &&
      (ebasisOK 24 u5T) && (ebasisOK 24 u6T) && (ebasisOK 24 tT) && (ebasisOK 24 etT)) = true ∧
    ((cb0T.countP (commAll 24 oT) == 16) && (cb0T.countP (commAll 24 sT) == 64) &&
      (cb0T.countP (commAll 24 s16T) == 64) && (cb0T.countP (commAll 24 s32T) == 64) &&
      (cb0T.countP (commAll 24 r2T) == 16) && (cb0T.countP (commAll 24 u4T) == 16) &&
      (cb0T.countP (commAll 24 u5T) == 128) && (cb0T.countP (commAll 24 tT) == 64) &&
      (cb1T.countP (commAll 24 u6T) == 64)) = true ∧
    ((sT.all (commAll 24 s16T)) && (sT.all (commAll 24 s32T)) && (invOK 24 d4T (invT 24 d4T)) &&
      ((conjAll d4T r2T).all (commAll 24 u4T)) && (invOK 24 d6T (invT 24 d6T)) &&
      ((conjAll d6T tT).all (commAll 24 u6T)) &&
      (qGen.all fun g => commAll 24 u5T (toTable g))) = true ∧
    (moChain.check && (moChain.orderCertificate == 322560) && nsChain.check &&
      (nsChain.orderCertificate == 138240) && lsChain.check &&
      (lsChain.orderCertificate == 69120) && qChain.check && (qChain.orderCertificate == 128) &&
      nqChain.check && (nqChain.orderCertificate == 21504) && lqChain.check &&
      (lqChain.orderCertificate == 10752) && ntChain.check && (ntChain.orderCertificate == 64512) &&
      kqChain.check && (kqChain.orderCertificate == 21504)) = true ∧
    (((moGen.zip moMasks).all (fun p => masksOK 24 oT (toTable p.1) p.2)) &&
      ((nsGen.zip nsMasks).all (fun p => masksOK 24 sT (toTable p.1) p.2)) &&
      (masksOK 24 sT y5T y5Masks) && ((njT.zip njMasks).all (fun p => masksOK 24 sT p.1 p.2)) &&
      ((nqGen.zip nqMasks).all (fun p => masksOK 24 u5T (toTable p.1) p.2)) &&
      (masksOK 24 u5T y7T y7Masks) && ((mjT.zip mjMasks).all (fun p => masksOK 24 u5T p.1 p.2)) &&
      ((ntGen.zip ntMasks).all (fun p => masksOK 24 tT (toTable p.1) p.2)) &&
      (masksOK 24 tT qtT qtMasks) && ((kqT.zip kqMasks).all (fun p => masksOK 24 tT p.1 p.2)) &&
      ((cb0Gen.zip cb0Masks).all (fun p => masksOK 24 r2T (toTable p.1) p.2)) &&
      (ordTest 24 5 y5T) && (ordTest 24 7 y7T)) = true ∧
    ((sW.all fun w => lsChain.sift (tab (wordG gensG w)) 0) &&
      (etW.all fun w => lqChain.sift (tab (wordG gensG w)) 0) && (etT.all (commAll 24 u5T)) &&
      (countProducts 24 (commAll 24 u5T) (levelTables lqChain) (idT 24) == 64) &&
      (blocksOK tets y5T) && (njT.all (blocksOK tets)) && (sT.all (fixesBlocks tets)) &&
      (countProducts 24 (fixesBlocks tets) (levelTables lsChain) (idT 24) == 192)) = true ∧
    (!(inSpan 24 tT qtT) && (inSpan 24 tT (compT 24 qtT qtT)) && (invOK 24 qtT (invT 24 qtT)) &&
      (kqT.all fun k => invOK 24 k (invT 24 k) &&
        inSpan 24 tT (compT 24 (conjTab 24 k (invT 24 k) qtT) (invT 24 qtT))) &&
      (cosetOK 24 b0T r2T r2CosetT) &&
      (cosetCount 24 cb0T r2CosetT (normAll 24 r2T) == 21504)) = true := ⟨g1, g2, g3, g4, g5, g6, g7⟩

end CertificateChecks.KernelKGC31M24

end

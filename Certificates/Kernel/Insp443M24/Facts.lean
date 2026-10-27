module

public import Certificates.Kernel.Insp443M24.Checks
public import Certificates.Kernel.KGC31M24.Facts7217
public import Certificates.Data.Insp443M24
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelInsp443M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3 CFSG.KC.BfsPin
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M24 CFSG.Sporadic.Mathieu
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M24OC
open CFSG.KS.SporSch.MOC CFSG.Monster.B.Mathieu CFSG.Certificates
open CFSG.SectionRank.QTK.Insp443.M24 CertificateChecks.KernelKGC31M24

theorem hz : PP 24 5 zP := (ppw' gW).pc (ppw' d6W).pinv

theorem zT_eq : zT = tabP 24 5 zP := by
  rw [zT, gT, d6T, wT, wT, invT_tabP (ppw' d6W), compT_tabP' (ppw' gW) (ppw' d6W).pinv]
  rfl

theorem ppSix : ∀ b ∈ sixP, PP 24 5 b := by
  intro b hb
  rcases List.mem_append.1 hb with hb | hb
  · exact ppcAll hz (ppL u6W) b hb
  · exact ppcAll (ppw' lW) (ppcAll hz (ppL u6W)) b hb

theorem sixT_eq : sixT = sixP.map (tabP 24 5) := by
  rw [sixT, zT_eq, u6T, mapW, conjAll_eq hz (ppL u6W), lT, wT,
    conjAll_eq (ppw' lW) (ppcAll hz (ppL u6W)), sixP, List.map_append]
  rfl

theorem spanAll {l : List Nat} (hl : ∀ b ∈ l, PP 24 5 b) :
    (l.map (tabP 24 5)).all (inSpan 24 etT) = l.all (pinSpan 24 5 etP) := by
  rw [etT, mapW]
  exact all_map_congr fun b hb => inSpan_tabP hsz (ppL etW) (hl b hb)

theorem ppLq : ∀ g ∈ lqP, PP 24 5 g := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact PP_pcj (ppw' w) (ppw' w).pinv (ppw' y7W)

theorem lqGen_tab :
    lqGen.map toTable = lqP.map (tabP 24 5) := by
  rw [lqGen, lqP, List.map_map, List.map_map]
  exact List.map_congr_left fun w _ =>
    CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img (cj_img w y7W)

theorem gensCB : (List.range 3).all (fun j => Nat.beq (CCB.S j) (wcj (cjW.getD j []) xW)) = true := by
  have h := ch725001g3
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem ordCB : ordK CCB.LR 4 = 21504 := by
  have h := ch725001g3
  simp only [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2

theorem chainCB : ChainK 24 5 cbGen cbChainW (#v[0, 1, 2, 3] : Vector (Fin 24) 4)
    CCB.S CCB.SI CCB.LR CCB.TR CCB.TRI 8 CCB.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, cgens_img rfl gensCB, by decide, CCB.head,
    CCB.hl, by norm_num, CCB.hs⟩

theorem g1 : (invOK 24 gT (invT 24 gT) && (conjAll gT tT).all (inSpan 24 etT)) = true := by
  have hg := ppw' gW
  have e1 : invOK 24 gT (invT 24 gT) = true := by rw [gT, wT]; exact invOK_tabP hg
  have e2 : (conjAll gT tT).all (inSpan 24 etT) = true := by
    rw [gT, tT, mapW, wT, conjAll_eq hg (ppL tW), spanAll (ppcAll hg (ppL tW))]
    exact ch725001g1
  simp only [e1, e2, Bool.and_self]

theorem g2 : (invOK 24 zT (invT 24 zT) && invOK 24 lT (invT 24 lT) &&
    lqChain.sift (tab (wordG gensG lW)) 0 && ebasisOK 24 sixT && sixT.all (inSpan 24 etT)) =
      true := by
  have h := ch725001g2
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := h
  have e1 : invOK 24 zT (invT 24 zT) = true := by rw [zT_eq]; exact invOK_tabP hz
  have e2 : invOK 24 lT (invT 24 lT) = true := by rw [lT, wT]; exact invOK_tabP (ppw' lW)
  have e3 : lqChain.sift (tab (wordG gensG lW)) 0 = true :=
    chainK_sift (by decide) (by decide) chainLQ (tab_img lW) a3 a4
  have e4 : ebasisOK 24 sixT = true := by rw [sixT_eq, ebasisOK_tabP hsz ppSix]; exact a1
  have e5 : sixT.all (inSpan 24 etT) = true := by rw [sixT_eq, spanAll ppSix]; exact a2
  simp only [e1, e2, e3, e4, e5, Bool.and_self]

theorem g3 : (ordTest 24 7 xT && commT 24 b0T xT && cjT.all (commT 24 b0T) && cbChain.check &&
    (cbChain.orderCertificate == 21504)) = true := by
  have h := ch725001g3
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, -⟩, -⟩ := h
  have hx := ppw' xW
  have hb := ppw' (oW.headD [])
  obtain ⟨c1, c2⟩ := chainK_check (by decide) (by decide) chainCB
  have e1 : ordTest 24 7 xT = true := by rw [xT, wT, ordTest_tabP hx]; exact a1
  have e2 : commT 24 b0T xT = true := by rw [b0T, xT, wT, wT, commT_tabP hb hx]; exact a2
  have e3 : cjT.all (commT 24 b0T) = true := by
    rw [cjT, b0T, mapW, wT, all_map_congr fun c hc => commT_tabP hb (ppL cjW c hc)]
    exact a3
  have e4 : cbChain.check = true := c1
  have e5 : (cbChain.orderCertificate == 21504) = true := beq_iff_eq.2 (c2.trans ordCB)
  simp only [e1, e2, e3, e4, e5, Bool.and_self]

theorem g4 : (invOK 24 nT (invT 24 nT) && masksOK 24 etT nT nMasks &&
    (lqGen.all fun g => invOK 24 (toTable g) (invT 24 (toTable g)) &&
      inSpan 24 etT (compT 24 (conjTab 24 (toTable g) (invT 24 (toTable g)) nT) (invT 24 nT))) &&
    ebasisOK 24 (u5T ++ conjAll nT u5T) && u5T.all (inSpan 24 etT) &&
    ((nqGen.zip nqEtMasks).all fun p => masksOK 24 etT (toTable p.1) p.2) &&
    masksOK 24 etT y7T y7EtMasks &&
    ((mjT.zip mjEtMasks).all fun p => masksOK 24 etT p.1 p.2)) = true := by
  have h := ch725001g4
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := h
  have hn : PP 24 5 nP := ppw' nW
  have hnT : nT = tabP 24 5 nP := by rw [nT, wT]; rfl
  have e1 : invOK 24 nT (invT 24 nT) = true := by rw [hnT]; exact invOK_tabP hn
  have e2 : masksOK 24 etT nT nMasks = true := by
    rw [hnT, etT, mapW, masksOK_tabP hsz (ppL etW) hn]; exact a1
  have e3 : (lqGen.all fun g => invOK 24 (toTable g) (invT 24 (toTable g)) &&
      inSpan 24 etT (compT 24 (conjTab 24 (toTable g) (invT 24 (toTable g)) nT) (invT 24 nT))) =
        true := by
    have e : (lqGen.all fun g => invOK 24 (toTable g) (invT 24 (toTable g)) &&
        inSpan 24 etT (compT 24 (conjTab 24 (toTable g) (invT 24 (toTable g)) nT)
          (invT 24 nT))) =
        ((lqGen.map toTable).all fun T => invOK 24 T (invT 24 T) &&
          inSpan 24 etT (compT 24 (conjTab 24 T (invT 24 T) nT) (invT 24 nT))) := by
      rw [List.all_map]
      rfl
    rw [e, lqGen_tab, hnT, etT, mapW]
    rw [all_map_congr (h := fun g => pinSpan 24 5 etP
      (pc 24 5 (pcj 24 5 g (pinv 24 5 g) nP) (pinv 24 5 nP))) fun g hg => by
        have hp := ppLq g hg
        rw [invOK_tabP hp, Bool.true_and, invT_tabP hp, invT_tabP hn,
          conjTab_tabP hp hp.pinv hn, compT_tabP' (PP_pcj hp hp.pinv hn) hn.pinv,
          inSpan_tabP hsz (ppL etW) ((PP_pcj hp hp.pinv hn).pc hn.pinv)]
        rfl]
    exact a2
  have e4 : ebasisOK 24 (u5T ++ conjAll nT u5T) = true := by
    rw [hnT, u5T, mapW, conjAll_eq hn (ppL u5W), ← List.map_append,
      ebasisOK_tabP hsz (fun b hb => by
        rcases List.mem_append.1 hb with hb | hb
        · exact ppL u5W b hb
        · exact ppcAll hn (ppL u5W) b hb)]
    exact a3
  have e5 : u5T.all (inSpan 24 etT) = true := by rw [u5T, mapW, spanAll (ppL u5W)]; exact a4
  have e6 : ((nqGen.zip nqEtMasks).all fun p => masksOK 24 etT (toTable p.1) p.2) = true := by
    rw [nqGen, etT, mapW etW, mzW (ppL etW)]; exact a5
  have e7 : masksOK 24 etT y7T y7EtMasks = true := by
    rw [etT, y7T, mapW etW, wT, masksOK_tabP hsz (ppL etW) (ppw' _)]; exact a6
  have e8 : ((mjT.zip mjEtMasks).all fun p => masksOK 24 etT p.1 p.2) = true := by
    rw [mjT, etT, mapW etW, mzT (ppL etW)]; exact a7
  simp only [e1, e2, e3, e4, e5, e6, e7, e8, Bool.and_self]

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M24 CFSG.Certificates
  CFSG.SectionRank.QTK.Insp443.M24 in
open Certificates in
theorem cert725001 :
    (invOK 24 gT (invT 24 gT) && (conjAll gT tT).all (inSpan 24 etT)) = true ∧
    (invOK 24 zT (invT 24 zT) && invOK 24 lT (invT 24 lT) &&
      lqChain.sift (tab (wordG gensG lW)) 0 && ebasisOK 24 sixT &&
      sixT.all (inSpan 24 etT)) = true ∧
    (ordTest 24 7 xT && commT 24 b0T xT && cjT.all (commT 24 b0T) && cbChain.check &&
      (cbChain.orderCertificate == 21504)) = true ∧
    (invOK 24 nT (invT 24 nT) && masksOK 24 etT nT nMasks &&
      (lqGen.all fun g => invOK 24 (toTable g) (invT 24 (toTable g)) &&
        inSpan 24 etT
          (compT 24 (conjTab 24 (toTable g) (invT 24 (toTable g)) nT) (invT 24 nT))) &&
      ebasisOK 24 (u5T ++ conjAll nT u5T) && u5T.all (inSpan 24 etT) &&
      ((nqGen.zip nqEtMasks).all fun p => masksOK 24 etT (toTable p.1) p.2) &&
      masksOK 24 etT y7T y7EtMasks &&
      ((mjT.zip mjEtMasks).all fun p => masksOK 24 etT p.1 p.2)) = true := ⟨g1, g2, g3, g4⟩

end CertificateChecks.KernelInsp443M24

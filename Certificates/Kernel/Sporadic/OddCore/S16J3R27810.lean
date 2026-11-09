module

public import Certificates.Kernel.Sporadic.OddCore.S16J3K27810
public import Certificates.Kernel.Sporadic.OddCore.J3BetaA5
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYData
public import Certificates.Data.Kernel.Spor.MulHF
public import CFSG.Certificates.Kernel.Enum.DefsC
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYData
public import Certificates.Kernel.J3Ref.Faith
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbOutAgree
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Spor.PK.Perm.CompC
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PcompFacts
meta import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
meta import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSpor.S16J3

open CFSG.EvenSporadicStandard.Fin76b.S16 CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native CFSG.PSL3Four.Native

meta def rootsM : Array (Array Nat) := #[tM 3, tM 4, tM 5, tM 6]
meta def vvM : Array (Array Nat) := #[cmM (tbM 1) (tbM 1), cmM (tbM 1) (tbM 2)]
meta def wM : Array (Array Nat) := #[tM 1, tM 2, tM 0]

meta def ids2M : Array (Array Nat) := Array.replicate 2 idM
meta def ids3M : Array (Array Nat) := Array.replicate 3 idM

meta def clOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  ((recOf gs).map fun x => (gs.map invA).map fun g => comp 6156 x g).flatten

meta def rRecM : Array (Array Nat) := recOf rootsM
meta def vRecM : Array (Array Nat) := recOf vvM
meta def wRecM : Array (Array Nat) := recOf wM
meta def rClM : Array (Array Nat) := clOf rootsM
meta def vClM : Array (Array Nat) := clOf vvM
meta def wClM : Array (Array Nat) := clOf wM
meta def cClM : Array (Array Nat) := clOf csM

meta def rIM : Array (Array Nat) := rootsM.map invA
meta def vIM : Array (Array Nat) := vvM.map invA
meta def wIM : Array (Array Nat) := wM.map invA

meta def mIM : Array (Array Nat) := #[invA (tM 1), invA (tM 7), invA (tM 10)]

meta def rPM : Array (Array Nat) := vvM
meta def cPM : Array (Array Nat) := #[natArr (j3CentTbl 9), tM 2]

end CertificateChecks.KernelSpor.S16J3

open CertificateChecks.KernelSpor.S16J3 in
#kmulh CertificateChecks.KernelSpor.S16J3R 6156 13 ids4M rootsM idM 40
open CertificateChecks.KernelSpor.S16J3 in
#kmulh CertificateChecks.KernelSpor.S16J3V 6156 13 ids2M vvM idM 40
open CertificateChecks.KernelSpor.S16J3 in
#kmulh CertificateChecks.KernelSpor.S16J3W 6156 13 ids3M wM idM 40
open CertificateChecks.KernelSpor.S16J3 in
#kfind CertificateChecks.KernelSpor.S16J3RCl rRecM rClM
open CertificateChecks.KernelSpor.S16J3 in
#kfind CertificateChecks.KernelSpor.S16J3VCl vRecM vClM
open CertificateChecks.KernelSpor.S16J3 in
#kfind CertificateChecks.KernelSpor.S16J3WCl wRecM wClM
open CertificateChecks.KernelSpor.S16J3 in
#kfind CertificateChecks.KernelSpor.S16J3CCl cRecM cClM
open CertificateChecks.KernelSpor.S16J3 in
#kfind CertificateChecks.KernelSpor.S16J3RP rRecM rPM
open CertificateChecks.KernelSpor.S16J3 in
#kfind CertificateChecks.KernelSpor.S16J3CP cRecM cPM
open CertificateChecks.KernelSpor.S16J3 in
#kmisc_packarrs CertificateChecks.KernelSpor.S16J3RI rIM 13
open CertificateChecks.KernelSpor.S16J3 in
#kmisc_packarrs CertificateChecks.KernelSpor.S16J3VI vIM 13
open CertificateChecks.KernelSpor.S16J3 in
#kmisc_packarrs CertificateChecks.KernelSpor.S16J3WI wIM 13
open CertificateChecks.KernelSpor.S16J3 in
#kmisc_packarrs CertificateChecks.KernelSpor.S16J3MI mIM 13

namespace CertificateChecks.KernelSpor.S16J3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.PkPow
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.F27811

@[expose] noncomputable def uK : Nat := J3CentP 0
@[expose] noncomputable def bK : Nat := J3BetaP 7
@[expose] noncomputable def vK : Nat := S 1

@[expose] noncomputable def commK (x y : Nat) : Bool := Nat.beq (pc x y) (pc y x)

@[expose] def tW : List Int := [1]
@[expose] def bW : List Int := [3, 4, 5, 3, 2, 2, 3, 4, 3, 1, 3, 1, 4, 5]
@[expose] def vW : List Int := [3, 2, 1, 2, 2, 3, 5, 3, 3, 4, 3, 5, 5]
@[expose] def xW : List Int := [1, 5, 1, 5, 1, 3, 3, 5, 5]
@[expose] def ruW : List Int := [3, 4, 1, 5, 1, 2, 2, 5, 3, 4, 3, 3, 4, 5, 1]

@[expose] def sW : List (List Int) :=
  [[3, 3, 3, 5, 3, 3, 4, 5], [3, 3, 4, 3, 3, 3, 5, 1, 4, 5],
    [3, 2, 1, 2, 2, 1, 5, 4, 3, 1, 3, 1, 5, 5], [4, 3, 2, 1, 2, 2, 5, 1, 3, 3, 5, 1, 3, 4, 5, 5],
    [2, 1, 2, 3, 5, 3, 3, 2, 2, 5, 3, 1, 5, 3, 3, 4, 3, 4], [4], [1],
    [2, 1, 2, 3, 5, 3, 3, 2, 2, 3, 3, 3, 5, 1, 3, 5, 5]]

@[expose] noncomputable def s16sift (j : Nat) : Bool := j3W (sW.getD j []) (S (Nat.add 3 j))

theorem s16step_id {n w : Nat} {G GI : Nat → Nat} {j t : Nat} (hG : G j = pidn n w)
    (ht : canonK n w (mask w) (n * w) t = true) :
    stepK n w (mask w) true G GI j t = pcomp n w (mask w) t (GI j) := by
  have e0 : stepK n w (mask w) true G GI j t =
      pcomp n w (mask w) (pcomp n w (mask w) (G j) t) (GI j) := rfl
  obtain ⟨hn, hw, hp0, hp4⟩ := CFSG.KS.PF.canon_facts ht
  have hn32 : n < 2 ^ 32 := by omega
  have hid : pcomp n w (mask w) (pidn n w) t = t := by
    refine CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw)
      (CFSG.KS.PF.pcomp_shr _ _ hn32 (CFSG.KS.PF.w_pos hw)) hp0 fun i hi => ?_
    rw [CFSG.KS.PF.pg_pcomp hn32 hi, CFSG.KS.PF.pg_pidn hn hw (hp4 i hi)]
  rw [e0, hG, hid]

theorem k_base : bAnd(cK uK, bAnd(cK tK, bAnd(cK bK, bAnd(cK vK, bAnd(cK xK,
    bAnd(cK (S 7), bAnd(cK (S 10),
    bAnd(cK (J3CentI 0), bAnd(cK (J3CentI 9), bAnd(cK (J3BetaI 1),
    bAnd(allN 3 (fun j => cK (S16J3MI j)),
    bAnd(iK uK (J3CentI 0), bAnd(iK tK (J3CentI 9), bAnd(iK bK (J3BetaI 1),
    bAnd(iK vK (S16J3MI 0), bAnd(iK (S 7) (S16J3MI 1), bAnd(iK (S 10) (S16J3MI 2),
    bAnd(iK xK xK,
    bAnd(allN 4 (fun j => bAnd(Nat.beq (S16J3R.GI j) (S (Nat.add 3 j)), bAnd(Nat.beq (S16J3R.G j) idK,
      bAnd(cK (S16J3R.GI j), bAnd(cK (S16J3RI j), iK (S16J3R.GI j) (S16J3RI j)))))),
    bAnd(Nat.beq (S16J3V.GI 0) (pc vK vK), bAnd(Nat.beq (S16J3V.GI 1) (pc vK xK),
    bAnd(allN 2 (fun j => bAnd(Nat.beq (S16J3V.G j) idK,
      bAnd(cK (S16J3V.GI j), bAnd(cK (S16J3VI j), iK (S16J3V.GI j) (S16J3VI j))))),
    bAnd(Nat.beq (S16J3W.GI 0) vK, bAnd(Nat.beq (S16J3W.GI 1) xK, bAnd(Nat.beq (S16J3W.GI 2) rK,
    bAnd(allN 3 (fun j => bAnd(Nat.beq (S16J3W.G j) idK,
      bAnd(cK (S16J3W.GI j), bAnd(cK (S16J3WI j), iK (S16J3W.GI j) (S16J3WI j))))),
    bAnd(Nat.beq (S16J3C.GI 0) (pc (S 7) rK), bAnd(Nat.beq (S16J3C.GI 1) (S 8),
    bAnd(Nat.beq (S16J3C.GI 2) (S 9), bAnd(Nat.beq (S16J3C.GI 3) (pc (S 10) rK),
    bAnd(allN 4 (fun j => bAnd(Nat.beq (S16J3C.G j) idK,
      bAnd(cK (S16J3C.GI j), bAnd(cK (S16J3CI j), iK (S16J3C.GI j) (S16J3CI j))))),
    bAnd(Nat.beq S16J3R.cnt 32, bAnd(Nat.beq S16J3V.cnt 8, bAnd(Nat.beq S16J3W.cnt 32,
    bAnd(Nat.beq S16J3C.cnt 32,
    bAnd(penumHdK idK S16J3R.cnt 40 S16J3R.T S16J3R.PL,
    bAnd(penumHdK idK S16J3V.cnt 40 S16J3V.T S16J3V.PL,
    bAnd(penumHdK idK S16J3W.cnt 40 S16J3W.T S16J3W.PL,
      penumHdK idK S16J3C.cnt 40 S16J3C.T S16J3C.PL)))))))))))))))))))))))))))))))))))))) =
    true := by
  quickRfl

theorem s16and {a b : Bool} (ha : a = true) (hb : b = true) : bAnd(a, b) = true := by
  rw [ha]
  exact hb

theorem k_siftsH (X : Bool) (hX : X = true) :
    bAnd(j3W tW tK, bAnd(j3W bW bK, bAnd(j3W vW vK, bAnd(j3W xW xK, X)))) = true := by
  subst hX
  quickRfl

theorem k_siftsU : j3W ruW (pc rK uK) = true := by
  quickRfl

theorem k_factsH (X : Bool) (hX : X = true) :
    bAnd(Nat.beq (pc rK rK) idK, bAnd(Nat.beq (pc (pc rK tK) rK) tK,
    bAnd(Nat.beq (pc (pc rK bK) rK) (J3BetaI 1),
    bAnd(commK vK tK, bAnd(commK xK tK,
    bAnd(Nat.beq (ppw 6156 13 vK 4) tK, bAnd(Nat.beq (ppw 6156 13 vK 8) idK,
    bAnd(Nat.beq (pc xK xK) idK, bAnd(bIf(Nat.beq xK idK, false, true),
    bAnd(bIf(Nat.beq xK tK, false, true),
    bAnd(Nat.beq (pc (pc xK vK) xK) (S16J3MI 0),
    bAnd(Nat.beq (pc (pc rK vK) rK) (pc vK tK), bAnd(Nat.beq (pc (pc rK xK) rK) (pc xK tK),
    bAnd(Nat.beq (pc (pc vK bK) (S16J3MI 0)) (J3BetaI 1),
    bAnd(Nat.beq (pc (pc xK bK) xK) (J3BetaI 1),
    bAnd(allN 4 (fun j => Nat.beq (pc (S (Nat.add 3 j)) (S (Nat.add 3 j))) tK),
      X)))))))))))))))) = true := by
  subst hX
  quickRfl

theorem k_factsT : bAnd(J2Cn.atK S16J3R.cnt S16J3R.T S16J3RP 0 (pc vK vK),
    bAnd(J2Cn.atK S16J3R.cnt S16J3R.T S16J3RP 1 (pc vK xK),
    bAnd(commK (pc vK vK) rK, bAnd(commK (pc vK xK) rK,
    bAnd(allN 4 (fun j => commK (S (Nat.add 7 j)) tK),
    bAnd(allN 4 (fun j => commK (S16J3C.GI j) xK),
    bAnd(J2Cn.atK S16J3C.cnt S16J3C.T S16J3CP 0 tK,
      J2Cn.atK S16J3C.cnt S16J3C.T S16J3CP 1 xK))))))) = true := by
  quickRfl

theorem k_sifts_neg : j3W vW xK = false := by
  decide +kernel

theorem rHF : slK S16J3R.cnt (hsortPtKF 6156 13 (mask 13) S16J3R.cnt S16J3R.T S16J3R.HS S16J3R.HSI)
    0 S16J3R.cnt = true := by quickRfl

theorem vHF : slK S16J3V.cnt (hsortPtKF 6156 13 (mask 13) S16J3V.cnt S16J3V.T S16J3V.HS S16J3V.HSI)
    0 S16J3V.cnt = true := by quickRfl

theorem wHF : slK S16J3W.cnt (hsortPtKF 6156 13 (mask 13) S16J3W.cnt S16J3W.T S16J3W.HS S16J3W.HSI)
    0 S16J3W.cnt = true := by quickRfl
theorem cHF : slK S16J3C.cnt (hsortPtKF 6156 13 (mask 13) S16J3C.cnt S16J3C.T S16J3C.HS S16J3C.HSI)
    0 S16J3C.cnt = true := by quickRfl
theorem rHF_neg : hsortPtKF 6156 13 (mask 13) S16J3R.cnt (fun _ => 0) S16J3R.HS S16J3R.HSI 0 =
    false := by
  decide +kernel

end CertificateChecks.KernelSpor.S16J3

#kc_each CertificateChecks.KernelSpor.S16J3.s16sift 0 8

namespace CertificateChecks.KernelSpor.S16J3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.PkPow
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.F27811

#kc_forall_chunks s16siftA (fun i => s16sift i = true) 8 CertificateChecks.KernelSpor.S16J3.s16sift 1

theorem k_sifts : bAnd(j3W tW tK, bAnd(j3W bW bK, bAnd(j3W vW vK, bAnd(j3W xW xK,
    bAnd(allN 8 (fun j => j3W (sW.getD j []) (S (Nat.add 3 j))),
      j3W ruW (pc rK uK)))))) = true :=
  k_siftsH (bAnd(allN 8 (fun j => j3W (sW.getD j []) (S (Nat.add 3 j))), j3W ruW (pc rK uK)))
    (s16and (a := allN 8 (fun j => j3W (sW.getD j []) (S (Nat.add 3 j))))
      (b := j3W ruW (pc rK uK))
      (CFSG.KS.Raw.Orb.allN_iff.2 s16siftA) k_siftsU)

theorem s16slK_all {cnt : Nat} {P : Nat → Bool} (h : slK cnt P 0 cnt = true) :
    ∀ i < cnt, P i = true := by
  intro i hi
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 h i hi
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h1
  have e : Nat.add 0 i = i := Nat.zero_add i
  rw [e, Eq.mpr Nat.blt_eq hi] at h1
  exact h1

theorem s16slK_of_all {cnt : Nat} {P : Nat → Bool} (h : ∀ i < cnt, P i = true) :
    slK cnt P 0 cnt = true := by
  unfold slK
  rw [CFSG.KS.Raw.Orb.allN_iff]
  intro d hd
  rw [CFSG.KS.Raw.Orb.strictB_eq]
  have e : Nat.add 0 d = d := Nat.zero_add d
  rw [e, Eq.mpr Nat.blt_eq hd]
  exact h d hd

open CertificateChecks.KernelJ3Ref CFSG.KS.PEnumB in
theorem s16rec_of_B {k cnt : Nat} {G GI GJ T PL POS SRT SRI CL : Nat → Nat}
    (hGI : ∀ j < k, MJ (GI j)) (hGJ : ∀ j < k, MJ (GJ j)) (hG : ∀ j < k, G j = pidn 6156 13)
    (hh : penumHdK (pidn 6156 13) cnt 40 T PL = true)
    (hb : slK cnt (penumPtB 6156 13 (mask 13) bsJ GI k cnt T PL POS SRT SRI) 0 cnt = true)
    (hc : slK (Nat.mul cnt k) (findProdB cnt 13 (mask 13) bsJ k T GJ CL) 0 (Nat.mul cnt k) = true) :
    penumSlK 6156 13 (mask 13) (6156 * 13) true G GI k cnt T PL POS SRT SRI 0 cnt = true ∧
      slK (Nat.mul cnt k) (findPtK cnt T (prodQK 6156 13 (mask 13) k T GJ) CL) 0
        (Nat.mul cnt k) = true := by
  have hb' := s16slK_all hb
  have hT := penumB_mem mj_faith hGI hh hb'
  refine ⟨s16slK_of_all (penumPtK_of_B mj_faith hGI hG hh hb'), s16slK_of_all fun c hc' => ?_⟩
  exact findPtK_prod_of_B mj_faith hT hGJ hc' (s16slK_all hc c hc')

theorem s16andE {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem s16rFacts : allN 4 (fun j => bAnd(Nat.beq (S16J3R.G j) idK,
    bAnd(Nat.beq (S16J3R.GI j) (S (Nat.add 3 j)), bAnd(cK (S16J3R.GI j), bAnd(cK (S16J3RI j),
    iK (S16J3R.GI j) (S16J3RI j)))))) = true := by
  quickRfl

theorem s16rHd : penumHdK idK S16J3R.cnt 40 S16J3R.T S16J3R.PL = true := by
  quickRfl

theorem s16rB : slK S16J3R.cnt (CFSG.KS.PEnumB.penumPtB 6156 13 (mask 13)
    CertificateChecks.KernelJ3Ref.bsJ S16J3R.GI 4 S16J3R.cnt S16J3R.T S16J3R.PL S16J3R.POS
    S16J3R.SRT S16J3R.SRI) 0 S16J3R.cnt = true := by
  quickRfl

theorem s16rF : slK (Nat.mul S16J3R.cnt 4) (CFSG.KS.PEnumB.findProdB S16J3R.cnt 13 (mask 13)
    CertificateChecks.KernelJ3Ref.bsJ 4 S16J3R.T S16J3RI S16J3RCl) 0 (Nat.mul S16J3R.cnt 4) =
    true := by
  quickRfl

open CertificateChecks.KernelJ3Ref in
theorem s16rMJ {j : Nat} (hj : j < 4) : MJ (S16J3R.GI j) ∧ MJ (S16J3RI j) ∧
    S16J3R.G j = pidn 6156 13 := by
  obtain ⟨hG, h⟩ := s16andE (CFSG.KS.Raw.Orb.allN_iff.1 s16rFacts j hj)
  obtain ⟨hS, h⟩ := s16andE h
  obtain ⟨hc, h⟩ := s16andE h
  obtain ⟨hci, hi⟩ := s16andE h
  have hw : j3W (sW.getD j []) (S (Nat.add 3 j)) = true := s16siftA j (Nat.lt_of_lt_of_le hj (by decide))
  rw [← Nat.eq_of_beq_eq_true hS] at hw
  have hm : MJ (S16J3R.GI j) := mj_of_word hc hw
  exact ⟨hm, mj_inv hm hci hi, Nat.eq_of_beq_eq_true hG⟩

theorem s16rRec :
    penumSlK 6156 13 (mask 13) (6156 * 13) true S16J3R.G S16J3R.GI 4 S16J3R.cnt S16J3R.T
      S16J3R.PL S16J3R.POS S16J3R.SRT S16J3R.SRI 0 S16J3R.cnt = true ∧
    slK (Nat.mul S16J3R.cnt 4)
      (findPtK S16J3R.cnt S16J3R.T (prodQK 6156 13 (mask 13) 4 S16J3R.T S16J3RI) S16J3RCl) 0
      (Nat.mul S16J3R.cnt 4) = true :=
  s16rec_of_B (fun _ hj => (s16rMJ hj).1) (fun _ hj => (s16rMJ hj).2.1)
    (fun _ hj => (s16rMJ hj).2.2) s16rHd s16rB s16rF

theorem rE : penumSlK 6156 13 (mask 13) (6156 * 13) true S16J3R.G S16J3R.GI 4 S16J3R.cnt S16J3R.T
    S16J3R.PL S16J3R.POS S16J3R.SRT S16J3R.SRI 0 S16J3R.cnt = true :=
  s16rRec.1

theorem s16vFacts : cK vK = true ∧ cK xK = true ∧ j3W vW vK = true ∧ j3W xW xK = true ∧
    Nat.beq (S16J3V.GI 0) (pc vK vK) = true ∧ Nat.beq (S16J3V.GI 1) (pc vK xK) = true ∧
    Nat.beq (S16J3V.G 0) idK = true ∧ Nat.beq (S16J3V.G 1) idK = true ∧
    cK (S16J3VI 0) = true ∧ cK (S16J3VI 1) = true ∧
    iK (S16J3V.GI 0) (S16J3VI 0) = true ∧ iK (S16J3V.GI 1) (S16J3VI 1) = true ∧
    penumHdK idK S16J3V.cnt 40 S16J3V.T S16J3V.PL = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl,
    by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem s16vB : slK S16J3V.cnt (CFSG.KS.PEnumB.penumPtB 6156 13 (mask 13)
    CertificateChecks.KernelJ3Ref.bsJ S16J3V.GI 2 S16J3V.cnt S16J3V.T S16J3V.PL S16J3V.POS
    S16J3V.SRT S16J3V.SRI) 0 S16J3V.cnt = true := by
  quickRfl

theorem s16vF : slK (Nat.mul S16J3V.cnt 2) (CFSG.KS.PEnumB.findProdB S16J3V.cnt 13 (mask 13)
    CertificateChecks.KernelJ3Ref.bsJ 2 S16J3V.T S16J3VI S16J3VCl) 0 (Nat.mul S16J3V.cnt 2) =
    true := by
  quickRfl

open CertificateChecks.KernelJ3Ref in
theorem s16vRec :
    penumSlK 6156 13 (mask 13) (6156 * 13) true S16J3V.G S16J3V.GI 2 S16J3V.cnt S16J3V.T
      S16J3V.PL S16J3V.POS S16J3V.SRT S16J3V.SRI 0 S16J3V.cnt = true ∧
    slK (Nat.mul S16J3V.cnt 2)
      (findPtK S16J3V.cnt S16J3V.T (prodQK 6156 13 (mask 13) 2 S16J3V.T S16J3VI) S16J3VCl) 0
      (Nat.mul S16J3V.cnt 2) = true := by
  obtain ⟨hcv, hcx, hwv, hwx, h0, h1, hG0, hG1, hc0, hc1, hi0, hi1, hh⟩ := s16vFacts
  have hv : MJ vK := mj_of_word hcv hwv
  have hx : MJ xK := mj_of_word hcx hwx
  have hGI : ∀ j < 2, MJ (S16J3V.GI j) := fun j hj => by
    match j, hj with
    | 0, _ => rw [Nat.eq_of_beq_eq_true h0]; exact mj_faith.comp _ _ hv hv
    | 1, _ => rw [Nat.eq_of_beq_eq_true h1]; exact mj_faith.comp _ _ hv hx
    | _ + 2, h => exact absurd h (by omega)
  have hGJ : ∀ j < 2, MJ (S16J3VI j) := fun j hj => by
    match j, hj with
    | 0, _ => exact mj_inv (hGI 0 (by decide)) hc0 hi0
    | 1, _ => exact mj_inv (hGI 1 (by decide)) hc1 hi1
    | _ + 2, h => exact absurd h (by omega)
  have hG : ∀ j < 2, S16J3V.G j = pidn 6156 13 := fun j hj => by
    match j, hj with
    | 0, _ => exact Nat.eq_of_beq_eq_true hG0
    | 1, _ => exact Nat.eq_of_beq_eq_true hG1
    | _ + 2, h => exact absurd h (by omega)
  exact s16rec_of_B hGI hGJ hG hh s16vB s16vF

theorem vE : penumSlK 6156 13 (mask 13) (6156 * 13) true S16J3V.G S16J3V.GI 2 S16J3V.cnt S16J3V.T
    S16J3V.PL S16J3V.POS S16J3V.SRT S16J3V.SRI 0 S16J3V.cnt = true :=
  s16vRec.1

theorem vCl : slK (Nat.mul S16J3V.cnt 2)
    (findPtK S16J3V.cnt S16J3V.T (prodQK 6156 13 (mask 13) 2 S16J3V.T S16J3VI) S16J3VCl) 0
    (Nat.mul S16J3V.cnt 2) = true :=
  s16vRec.2

@[expose] def rcW : List Int := [5, 3, 5, 1, 2, 2, 1, 2, 5, 4, 3, 3, 1, 3, 5, 1, 5]

open CertificateChecks.KernelSporSch in
theorem s16rConj : bAnd(cK (pc (pc rK (PJ3.S 0)) rK), bAnd(j3W [1] (pc (pc rK (PJ3.S 0)) rK),
    bAnd(cK (pc (pc rK (PJ3.S 1)) rK), j3W rcW (pc (pc rK (PJ3.S 1)) rK)))) = true := by
  quickRfl

open CertificateChecks.KernelJ3Ref CertificateChecks.KernelSporSch CFSG.KS.Raw.Orb
  CFSG.Monster.B.Co2 in
theorem s16rInv {ρ : Equiv.Perm (Fin 6156)} (hρ : PRep 6156 13 rK ρ) : PRep 6156 13 rK ρ⁻¹ := by
  have h := k_rout
  simp only [CFSG.KS.bAnd_iff] at h
  have hr := rep_permOfArr (invEqK_sound h.2.1).2
  have e : permOfArr 6156 (unpack 6156 13 rK) = ρ :=
    Equiv.ext fun x => Fin.ext ((hr.1 x).symm.trans ((unpack_get x.2).trans (hρ x)))
  rw [e] at hr
  exact prep_of_rep hr.2

open CertificateChecks.KernelJ3Ref CertificateChecks.KernelSporSch CFSG.KS.Raw.Orb
  CFSG.Monster.B.Co2 in
theorem s16rConjS {ρ : Equiv.Perm (Fin 6156)} (hρ : PRep 6156 13 rK ρ) {j : Nat} (hj : j < 5)
    (hm : MJ (pc (pc rK (PJ3.S j)) rK)) :
    ρ * permOfArr 6156 CFSG.Sporadic.Schreier.j3StrongArrs[j]! * ρ⁻¹ ∈ KernelK426J3.GJ := by
  obtain ⟨-, A, hA, hXA⟩ := hm
  have hq := prep_pcomp (by norm_num) (prep_pcomp (by norm_num) hρ
    (prep_PS PJ3Check.binds PJ3Check.perm hj).1) (s16rInv hρ)
  have eA : ρ * permOfArr 6156 CFSG.Sporadic.Schreier.j3StrongArrs[j]! * ρ⁻¹ = A :=
    Equiv.ext fun x => Fin.ext ((hq x).symm.trans (hXA x))
  rw [eA]
  exact hA

open CertificateChecks.KernelJ3Ref CertificateChecks.KernelSporSch in
theorem s16rConjMJ : MJ (pc (pc rK (PJ3.S 0)) rK) ∧ MJ (pc (pc rK (PJ3.S 1)) rK) := by
  have h := s16rConj
  simp only [CFSG.KS.bAnd_iff] at h
  exact ⟨mj_of_word h.1 h.2.1, mj_of_word h.2.2.1 h.2.2.2⟩

open CertificateChecks.KernelJ3Ref CertificateChecks.KernelSporSch CFSG.KS.Raw.Orb
  CFSG.Monster.B.Co2 in
theorem s16rNorm {ρ : Equiv.Perm (Fin 6156)} (hρ : PRep 6156 13 rK ρ) :
    ∀ g ∈ KernelK426J3.GJ, ρ * g * ρ⁻¹ ∈ KernelK426J3.GJ := by
  have hle : KernelK426J3.GJ ≤ KernelK426J3.GJ.comap (MulAut.conj ρ).toMonoidHom := by
    unfold KernelK426J3.GJ Gen
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    match j with
    | ⟨0, _⟩ => exact s16rConjS hρ (j := 0) (by decide) s16rConjMJ.1
    | ⟨1, _⟩ => exact s16rConjS hρ (j := 1) (by decide) s16rConjMJ.2
    | ⟨k + 2, hk⟩ => exact absurd hk (by omega)
  intro g hg
  have h := hle hg
  rw [Subgroup.mem_comap] at h
  exact h

section S16H

open CertificateChecks.KernelJ3Ref CertificateChecks.KernelSporSch CFSG.KS.Raw.Orb
  CFSG.Monster.B.Co2 CFSG.KS.PEnumB

@[expose] noncomputable def s16rP : Equiv.Perm (Fin 6156) := permOfArr 6156 (unpack 6156 13 rK)

theorem s16rho : PRep 6156 13 rK s16rP ∧ s16rP⁻¹ = s16rP := by
  have h := k_rout
  simp only [CFSG.KS.bAnd_iff] at h
  have hr := rep_permOfArr (invEqK_sound h.2.1).2
  exact ⟨prep_of_rep hr.1, hr.2.unique hr.1⟩

theorem s16rr : s16rP * s16rP = 1 := mul_eq_one_iff_eq_inv.2 s16rho.2.symm

theorem s16rN {g : Equiv.Perm (Fin 6156)} (hg : g ∈ KernelK426J3.GJ) :
    s16rP * g * s16rP ∈ KernelK426J3.GJ := by
  have h := s16rNorm s16rho.1 g hg
  rwa [s16rho.2] at h

def s16Hm (g : Equiv.Perm (Fin 6156)) : Prop := g ∈ KernelK426J3.GJ ∨ s16rP * g ∈ KernelK426J3.GJ

theorem s16Hm_mul {a b : Equiv.Perm (Fin 6156)} (ha : s16Hm a) (hb : s16Hm b) : s16Hm (a * b) := by
  unfold s16Hm at ha hb ⊢
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact Or.inl (KernelK426J3.GJ.mul_mem ha hb)
  · refine Or.inr ?_
    have e : s16rP * a * s16rP * (s16rP * b) = s16rP * (a * b) := by
      simp only [mul_assoc]
      rw [← mul_assoc s16rP s16rP b, s16rr, one_mul]
    rw [← e]
    exact KernelK426J3.GJ.mul_mem (s16rN ha) hb
  · refine Or.inr ?_
    rw [← mul_assoc]
    exact KernelK426J3.GJ.mul_mem ha hb
  · refine Or.inl ?_
    have e : s16rP * (s16rP * a) * s16rP * (s16rP * b) = a * b := by
      simp only [mul_assoc]
      rw [← mul_assoc s16rP s16rP b, s16rr, one_mul, ← mul_assoc s16rP s16rP (a * b), s16rr,
        one_mul]
    rw [← e]
    exact KernelK426J3.GJ.mul_mem (s16rN ha) hb

theorem s16Hm_inv {a : Equiv.Perm (Fin 6156)} (ha : s16Hm a) : s16Hm a⁻¹ := by
  unfold s16Hm at ha ⊢
  rcases ha with ha | ha
  · exact Or.inl (KernelK426J3.GJ.inv_mem ha)
  · refine Or.inr ?_
    have h := s16rN (KernelK426J3.GJ.inv_mem ha)
    have e : s16rP * (s16rP * a)⁻¹ * s16rP = s16rP * a⁻¹ := by
      rw [mul_inv_rev, s16rho.2]
      simp only [mul_assoc]
      rw [s16rr, mul_one]
    rwa [e] at h

theorem s16mix {A B : Equiv.Perm (Fin 6156)} (hA : A ∈ KernelK426J3.GJ)
    (hB : s16rP * B ∈ KernelK426J3.GJ) (h : ∀ b ∈ bsJ, ∀ hb : b < 6156, A ⟨b, hb⟩ = B ⟨b, hb⟩) :
    False := by
  have hk := k_rout
  simp only [CFSG.KS.bAnd_iff] at hk
  have e : B = s16rP * (s16rP * B) * s16rP * s16rP := by
    simp only [mul_assoc]
    rw [s16rr, mul_one, ← mul_assoc, s16rr, one_mul]
  obtain ⟨d, hd, rfl⟩ : ∃ d ∈ KernelK426J3.GJ, B = d * s16rP := ⟨_, s16rN hB, e⟩
  have hσ := KernelK426J3.GJ.mul_mem (KernelK426J3.GJ.inv_mem hd) hA
  refine not_agree_of_outK J3KT.hd PJ3Check.binds PJ3Check.perm PJ3.ho (by norm_num)
    PJ3Check.card_le (l := 1) (by norm_num) s16rho.1 hk.2.2 hσ fun t ht hbn => ?_
  rw [Equiv.Perm.mul_apply, h _ (by interval_cases t <;> decide) hbn, Equiv.Perm.mul_apply,
    ← Equiv.Perm.mul_apply d⁻¹ d, inv_mul_cancel, Equiv.Perm.one_apply]

theorem s16Hm_eq {A B : Equiv.Perm (Fin 6156)} (hA : s16Hm A) (hB : s16Hm B)
    (h : ∀ b ∈ bsJ, ∀ hb : b < 6156, A ⟨b, hb⟩ = B ⟨b, hb⟩) : A = B := by
  have hbs : ∀ b ∈ KernelK426J3.bs, b ∈ bsJ := fun b hb => by
    simpa [bsJ, KernelK426J3.bs] using hb
  unfold s16Hm at hA hB
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact KernelK426J3.eq_of_base hA hB fun b hb => congrArg Fin.val (h b (hbs b hb) _)
  · exact (s16mix hA hB h).elim
  · exact (s16mix hB hA fun b hb hbn => (h b hb hbn).symm).elim
  · refine mul_left_cancel (KernelK426J3.eq_of_base hA hB fun b hb => ?_)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h b (hbs b hb) (KernelK426J3.bs_lt b hb)]

def s16M (X : Nat) : Prop :=
  canonK 6156 13 (mask 13) (6156 * 13) X = true ∧
    ∃ A, s16Hm A ∧ ∀ x : Fin 6156, pg 13 (mask 13) X x = (A x : Nat)

theorem s16faith : BaseFaith 6156 13 bsJ s16M where
  n_lt := by norm_num
  bs_lt := by decide
  canon := fun _ h => h.1
  eq := fun X Y hX hY h => by
    obtain ⟨hXc, A, hA, hXA⟩ := hX
    obtain ⟨hYc, B, hB, hYB⟩ := hY
    have hAB : A = B := s16Hm_eq hA hB fun b hb hbn => Fin.ext (by
      rw [← hXA, ← hYB]
      exact h b hb)
    subst hAB
    obtain ⟨-, hw, hX0, -⟩ := PF.canon_facts hXc
    obtain ⟨-, -, hY0, -⟩ := PF.canon_facts hYc
    exact PF.eq_of_fields (PF.w_pos hw) hX0 hY0 fun i hi => by
      rw [hXA ⟨i, hi⟩, hYB ⟨i, hi⟩]
  comp := fun X Y hX hY => by
    obtain ⟨hXc, A, hA, hXA⟩ := hX
    obtain ⟨hYc, B, hB, hYB⟩ := hY
    refine ⟨CFSG.KC.BfsPin.canonK_pcomp hXc hYc, A * B, s16Hm_mul hA hB, fun x => ?_⟩
    rw [PF.pg_pcomp (by norm_num) x.2, hYB x, hXA (B x), Equiv.Perm.mul_apply]
  id := by
    refine ⟨mj_faith.id.1, 1, Or.inl KernelK426J3.GJ.one_mem, fun x => ?_⟩
    rw [PF.pg_pidn (by norm_num) (by norm_num) x.2]
    rfl

theorem s16M_of {X : Nat} (h : MJ X) : s16M X := by
  obtain ⟨hc, A, hA, hXA⟩ := h
  exact ⟨hc, A, Or.inl hA, hXA⟩

theorem s16M_r : s16M rK := by
  have hk := k_rout
  simp only [CFSG.KS.bAnd_iff] at hk
  refine ⟨hk.1, s16rP, Or.inr ?_, s16rho.1⟩
  rw [s16rr]
  exact KernelK426J3.GJ.one_mem

theorem s16M_inv {P R : Nat} (hP : s16M P) (hR : canonK 6156 13 (mask 13) (6156 * 13) R = true)
    (h : invEqK 6156 13 (mask 13) (6156 * 13) P R = true) : s16M R := by
  obtain ⟨-, A, hA, hPA⟩ := hP
  have hrep : Rep 6156 (unpack 6156 13 P) A := fun x => by
    rw [KernelK426J3.unpackGet x.2]
    exact hPA x
  have hi := rep_inv_of_isInvA hrep (invEqK_sound h).2
  exact ⟨hR, A⁻¹, s16Hm_inv hA, fun x => by rw [← KernelK426J3.unpackGet x.2]; exact hi x⟩

theorem s16rec_of_F {M : Nat → Prop} (hF : BaseFaith 6156 13 bsJ M) {k cnt : Nat}
    {G GI GJ T PL POS SRT SRI CL : Nat → Nat}
    (hGI : ∀ j < k, M (GI j)) (hGJ : ∀ j < k, M (GJ j)) (hG : ∀ j < k, G j = pidn 6156 13)
    (hh : penumHdK (pidn 6156 13) cnt 40 T PL = true)
    (hb : slK cnt (penumPtB 6156 13 (mask 13) bsJ GI k cnt T PL POS SRT SRI) 0 cnt = true)
    (hc : slK (Nat.mul cnt k) (findProdB cnt 13 (mask 13) bsJ k T GJ CL) 0 (Nat.mul cnt k) = true) :
    penumSlK 6156 13 (mask 13) (6156 * 13) true G GI k cnt T PL POS SRT SRI 0 cnt = true ∧
      slK (Nat.mul cnt k) (findPtK cnt T (prodQK 6156 13 (mask 13) k T GJ) CL) 0
        (Nat.mul cnt k) = true := by
  have hb' := s16slK_all hb
  have hT := penumB_mem hF hGI hh hb'
  refine ⟨s16slK_of_all (penumPtK_of_B hF hGI hG hh hb'), s16slK_of_all fun c hc' => ?_⟩
  exact findPtK_prod_of_B hF hT hGJ hc' (s16slK_all hc c hc')

theorem s16gens {k : Nat} {G GI GJ : Nat → Nat} (hm : ∀ j < k, s16M (GI j))
    (h : allN k (fun j => bAnd(Nat.beq (G j) idK, bAnd(cK (GI j), bAnd(cK (GJ j),
      iK (GI j) (GJ j))))) = true) :
    (∀ j < k, s16M (GJ j)) ∧ ∀ j < k, G j = pidn 6156 13 := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have h1 := allN_iff.1 h j hj
    simp only [CFSG.KS.bAnd_iff] at h1
    exact s16M_inv (hm j hj) h1.2.2.1 h1.2.2.2
  · have h1 := allN_iff.1 h j hj
    simp only [CFSG.KS.bAnd_iff] at h1
    exact Nat.eq_of_beq_eq_true h1.1

end S16H

theorem s16wB : slK S16J3W.cnt (CFSG.KS.PEnumB.penumPtB 6156 13 (mask 13)
    CertificateChecks.KernelJ3Ref.bsJ S16J3W.GI 3 S16J3W.cnt S16J3W.T S16J3W.PL S16J3W.POS
    S16J3W.SRT S16J3W.SRI) 0 S16J3W.cnt = true := by
  quickRfl

theorem s16wF : slK (Nat.mul S16J3W.cnt 3) (CFSG.KS.PEnumB.findProdB S16J3W.cnt 13 (mask 13)
    CertificateChecks.KernelJ3Ref.bsJ 3 S16J3W.T S16J3WI S16J3WCl) 0 (Nat.mul S16J3W.cnt 3) =
    true := by
  quickRfl

theorem s16cB : slK S16J3C.cnt (CFSG.KS.PEnumB.penumPtB 6156 13 (mask 13)
    CertificateChecks.KernelJ3Ref.bsJ S16J3C.GI 4 S16J3C.cnt S16J3C.T S16J3C.PL S16J3C.POS
    S16J3C.SRT S16J3C.SRI) 0 S16J3C.cnt = true := by
  quickRfl

theorem s16cF : slK (Nat.mul S16J3C.cnt 4) (CFSG.KS.PEnumB.findProdB S16J3C.cnt 13 (mask 13)
    CertificateChecks.KernelJ3Ref.bsJ 4 S16J3C.T S16J3CI S16J3CCl) 0 (Nat.mul S16J3C.cnt 4) =
    true := by
  quickRfl

theorem s16wcFacts : bAnd(Nat.beq (S16J3W.GI 0) vK, bAnd(Nat.beq (S16J3W.GI 1) xK,
    bAnd(Nat.beq (S16J3W.GI 2) rK,
    bAnd(allN 3 (fun j => bAnd(Nat.beq (S16J3W.G j) idK,
      bAnd(cK (S16J3W.GI j), bAnd(cK (S16J3WI j), iK (S16J3W.GI j) (S16J3WI j))))),
    bAnd(Nat.beq (S16J3C.GI 0) (pc (S 7) rK), bAnd(Nat.beq (S16J3C.GI 1) (S 8),
    bAnd(Nat.beq (S16J3C.GI 2) (S 9), bAnd(Nat.beq (S16J3C.GI 3) (pc (S 10) rK),
    bAnd(cK (S 7), bAnd(cK (S 8), bAnd(cK (S 9), bAnd(cK (S 10),
    bAnd(allN 4 (fun j => bAnd(Nat.beq (S16J3C.G j) idK,
      bAnd(cK (S16J3C.GI j), bAnd(cK (S16J3CI j), iK (S16J3C.GI j) (S16J3CI j))))),
    bAnd(penumHdK idK S16J3W.cnt 40 S16J3W.T S16J3W.PL,
      penumHdK idK S16J3C.cnt 40 S16J3C.T S16J3C.PL)))))))))))))) = true := by
  quickRfl

open CertificateChecks.KernelJ3Ref in
theorem s16SM {j : Nat} (hj : j < 8) (hc : cK (S (Nat.add 3 j)) = true) :
    s16M (S (Nat.add 3 j)) :=
  s16M_of (mj_of_word hc (s16siftA j hj))

open CertificateChecks.KernelJ3Ref CFSG.KS.Raw.Orb in
theorem s16wcRec :
    (penumSlK 6156 13 (mask 13) (6156 * 13) true S16J3W.G S16J3W.GI 3 S16J3W.cnt S16J3W.T
      S16J3W.PL S16J3W.POS S16J3W.SRT S16J3W.SRI 0 S16J3W.cnt = true ∧
    slK (Nat.mul S16J3W.cnt 3)
      (findPtK S16J3W.cnt S16J3W.T (prodQK 6156 13 (mask 13) 3 S16J3W.T S16J3WI) S16J3WCl) 0
      (Nat.mul S16J3W.cnt 3) = true) ∧
    (penumSlK 6156 13 (mask 13) (6156 * 13) true S16J3C.G S16J3C.GI 4 S16J3C.cnt S16J3C.T
      S16J3C.PL S16J3C.POS S16J3C.SRT S16J3C.SRI 0 S16J3C.cnt = true ∧
    slK (Nat.mul S16J3C.cnt 4)
      (findPtK S16J3C.cnt S16J3C.T (prodQK 6156 13 (mask 13) 4 S16J3C.T S16J3CI) S16J3CCl) 0
      (Nat.mul S16J3C.cnt 4) = true) := by
  have h := s16wcFacts
  simp only [CFSG.KS.bAnd_iff] at h
  obtain ⟨w0, w1, w2, hwa, c0, c1, c2, c3, k7, k8, k9, k10, hca, hwh, hch⟩ := h
  obtain ⟨hcv, hcx, hwv, hwx, -⟩ := s16vFacts
  have hv : s16M vK := s16M_of (mj_of_word hcv hwv)
  have hx : s16M xK := s16M_of (mj_of_word hcx hwx)
  have hwm : ∀ j < 3, s16M (S16J3W.GI j) := fun j hj => by
    match j, hj with
    | 0, _ => rw [Nat.eq_of_beq_eq_true w0]; exact hv
    | 1, _ => rw [Nat.eq_of_beq_eq_true w1]; exact hx
    | 2, _ => rw [Nat.eq_of_beq_eq_true w2]; exact s16M_r
    | _ + 3, h => exact absurd h (by omega)
  have hcm : ∀ j < 4, s16M (S16J3C.GI j) := fun j hj => by
    match j, hj with
    | 0, _ =>
      rw [Nat.eq_of_beq_eq_true c0]
      exact s16faith.comp _ _ (s16SM (j := 4) (by decide) k7) s16M_r
    | 1, _ => rw [Nat.eq_of_beq_eq_true c1]; exact s16SM (j := 5) (by decide) k8
    | 2, _ => rw [Nat.eq_of_beq_eq_true c2]; exact s16SM (j := 6) (by decide) k9
    | 3, _ =>
      rw [Nat.eq_of_beq_eq_true c3]
      exact s16faith.comp _ _ (s16SM (j := 7) (by decide) k10) s16M_r
    | _ + 4, h => exact absurd h (by omega)
  obtain ⟨hwi, hwg⟩ := s16gens hwm hwa
  obtain ⟨hci, hcg⟩ := s16gens hcm hca
  exact ⟨s16rec_of_F s16faith hwm hwi hwg hwh s16wB s16wF,
    s16rec_of_F s16faith hcm hci hcg hch s16cB s16cF⟩

theorem wE : penumSlK 6156 13 (mask 13) (6156 * 13) true S16J3W.G S16J3W.GI 3 S16J3W.cnt S16J3W.T
    S16J3W.PL S16J3W.POS S16J3W.SRT S16J3W.SRI 0 S16J3W.cnt = true :=
  s16wcRec.1.1

theorem cE : penumSlK 6156 13 (mask 13) (6156 * 13) true S16J3C.G S16J3C.GI 4 S16J3C.cnt S16J3C.T
    S16J3C.PL S16J3C.POS S16J3C.SRT S16J3C.SRI 0 S16J3C.cnt = true :=
  s16wcRec.2.1

theorem rCl : slK (Nat.mul S16J3R.cnt 4)
    (findPtK S16J3R.cnt S16J3R.T (prodQK 6156 13 (mask 13) 4 S16J3R.T S16J3RI) S16J3RCl) 0
    (Nat.mul S16J3R.cnt 4) = true :=
  s16rRec.2

theorem wCl : slK (Nat.mul S16J3W.cnt 3)
    (findPtK S16J3W.cnt S16J3W.T (prodQK 6156 13 (mask 13) 3 S16J3W.T S16J3WI) S16J3WCl) 0
    (Nat.mul S16J3W.cnt 3) = true :=
  s16wcRec.1.2

theorem cCl : slK (Nat.mul S16J3C.cnt 4)
    (findPtK S16J3C.cnt S16J3C.T (prodQK 6156 13 (mask 13) 4 S16J3C.T S16J3CI) S16J3CCl) 0
    (Nat.mul S16J3C.cnt 4) = true :=
  s16wcRec.2.2

@[expose] noncomputable def s16cmB (x y : Nat) : Bool :=
  CFSG.KS.SporSch.eqOnL CertificateChecks.KernelJ3Ref.bsJ
    (fun b => pg 13 (mask 13) x (pg 13 (mask 13) y b))
    (fun b => pg 13 (mask 13) y (pg 13 (mask 13) x b))

theorem s16comm_B {x y : Nat} (hx : s16M x) (hy : s16M y) : commK x y = s16cmB x y := by
  apply Bool.eq_iff_iff.2
  unfold commK s16cmB pc
  rw [Nat.beq_eq, CFSG.KS.SporSch.eqOnL_iff]
  constructor
  · intro h b hb
    have hb' := s16faith.bs_lt b hb
    rw [← PF.pg_pcomp s16faith.n_lt hb', ← PF.pg_pcomp s16faith.n_lt hb']
    exact congrArg (fun z => pg 13 (mask 13) z b) h
  · intro h
    refine s16faith.eq _ _ (s16faith.comp _ _ hx hy) (s16faith.comp _ _ hy hx) fun b hb => ?_
    have hb' := s16faith.bs_lt b hb
    rw [PF.pg_pcomp s16faith.n_lt hb', PF.pg_pcomp s16faith.n_lt hb']
    exact h b hb

theorem s16cnt_congr {cnt hi : Nat} {q q' : Nat → Bool} (h : ∀ i < cnt, q i = q' i) :
    cntBelowK cnt q hi = cntBelowK cnt q' hi := by
  unfold cntBelowK
  congr 1
  funext i
  cases hb : Nat.blt i cnt
  · rfl
  · rw [h i (Nat.blt_eq.mp hb)]

theorem s16rT : ∀ i < S16J3R.cnt, s16M (S16J3R.T i) := fun i hi =>
  s16M_of (CFSG.KS.PEnumB.penumB_mem CertificateChecks.KernelJ3Ref.mj_faith
    (fun _ hj => (s16rMJ hj).1) s16rHd (s16slK_all s16rB) i hi)

theorem s16rC : cntBelowK S16J3R.cnt (fun i => commK (S16J3R.T i) rK) 1 =
    cntBelowK S16J3R.cnt (fun i => s16cmB (S16J3R.T i) rK) 1 :=
  s16cnt_congr fun i hi => s16comm_B (s16rT i hi) s16M_r

theorem k_factsC : Nat.beq (cntBelowK S16J3R.cnt (fun i => commK (S16J3R.T i) rK) 1) 8 = true := by
  rw [s16rC]
  quickRfl

theorem k_facts : bAnd(Nat.beq (pc rK rK) idK, bAnd(Nat.beq (pc (pc rK tK) rK) tK,
    bAnd(Nat.beq (pc (pc rK bK) rK) (J3BetaI 1),
    bAnd(commK vK tK, bAnd(commK xK tK,
    bAnd(Nat.beq (ppw 6156 13 vK 4) tK, bAnd(Nat.beq (ppw 6156 13 vK 8) idK,
    bAnd(Nat.beq (pc xK xK) idK, bAnd(bIf(Nat.beq xK idK, false, true),
    bAnd(bIf(Nat.beq xK tK, false, true),
    bAnd(Nat.beq (pc (pc xK vK) xK) (S16J3MI 0),
    bAnd(Nat.beq (pc (pc rK vK) rK) (pc vK tK), bAnd(Nat.beq (pc (pc rK xK) rK) (pc xK tK),
    bAnd(Nat.beq (pc (pc vK bK) (S16J3MI 0)) (J3BetaI 1),
    bAnd(Nat.beq (pc (pc xK bK) xK) (J3BetaI 1),
    bAnd(allN 4 (fun j => Nat.beq (pc (S (Nat.add 3 j)) (S (Nat.add 3 j))) tK),
    bAnd(Nat.beq (cntBelowK S16J3R.cnt (fun i => commK (S16J3R.T i) rK) 1) 8,
    bAnd(J2Cn.atK S16J3R.cnt S16J3R.T S16J3RP 0 (pc vK vK),
    bAnd(J2Cn.atK S16J3R.cnt S16J3R.T S16J3RP 1 (pc vK xK),
    bAnd(commK (pc vK vK) rK, bAnd(commK (pc vK xK) rK,
    bAnd(allN 4 (fun j => commK (S (Nat.add 7 j)) tK),
    bAnd(allN 4 (fun j => commK (S16J3C.GI j) xK),
    bAnd(J2Cn.atK S16J3C.cnt S16J3C.T S16J3CP 0 tK,
      J2Cn.atK S16J3C.cnt S16J3C.T S16J3CP 1 xK)))))))))))))))))))))))) = true :=
  k_factsH (bAnd(Nat.beq (cntBelowK S16J3R.cnt (fun i => commK (S16J3R.T i) rK) 1) 8,
    bAnd(J2Cn.atK S16J3R.cnt S16J3R.T S16J3RP 0 (pc vK vK),
    bAnd(J2Cn.atK S16J3R.cnt S16J3R.T S16J3RP 1 (pc vK xK),
    bAnd(commK (pc vK vK) rK, bAnd(commK (pc vK xK) rK,
    bAnd(allN 4 (fun j => commK (S (Nat.add 7 j)) tK),
    bAnd(allN 4 (fun j => commK (S16J3C.GI j) xK),
    bAnd(J2Cn.atK S16J3C.cnt S16J3C.T S16J3CP 0 tK,
      J2Cn.atK S16J3C.cnt S16J3C.T S16J3CP 1 xK)))))))))
    (s16and (a := Nat.beq (cntBelowK S16J3R.cnt (fun i => commK (S16J3R.T i) rK) 1) 8)
      (b := bAnd(J2Cn.atK S16J3R.cnt S16J3R.T S16J3RP 0 (pc vK vK),
        bAnd(J2Cn.atK S16J3R.cnt S16J3R.T S16J3RP 1 (pc vK xK),
        bAnd(commK (pc vK vK) rK, bAnd(commK (pc vK xK) rK,
        bAnd(allN 4 (fun j => commK (S (Nat.add 7 j)) tK),
        bAnd(allN 4 (fun j => commK (S16J3C.GI j) xK),
        bAnd(J2Cn.atK S16J3C.cnt S16J3C.T S16J3CP 0 tK,
          J2Cn.atK S16J3C.cnt S16J3C.T S16J3CP 1 xK))))))))
      k_factsC k_factsT)

theorem k_facts_neg : Nat.beq (cntBelowK S16J3R.cnt (fun i => commK (S16J3R.T i) rK) 1) 32 =
    false := by
  rw [s16rC]
  decide +kernel

end CertificateChecks.KernelSpor.S16J3

end

module

public import Certificates.Kernel.Sporadic.OddCore.S16J3K27810
public import Certificates.Kernel.Sporadic.OddCore.J3BetaA5
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYData
public import Certificates.Data.Kernel.Spor.MulHF
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYData
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
meta import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S16J3

open CFSG.EvenSporadicStandard.Fin76b.S16 CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native CFSG.PSL3Four.Native

meta def rootsM : Array (Array Nat) := #[tM 3, tM 4, tM 5, tM 6]
meta def vvM : Array (Array Nat) := #[cmM (tbM 1) (tbM 1), cmM (tbM 1) (tbM 2)]
meta def wM : Array (Array Nat) := #[tM 1, tM 2, tM 0]

meta def ids2M : Array (Array Nat) := Array.replicate 2 idM
meta def ids3M : Array (Array Nat) := Array.replicate 3 idM

meta def clOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  ((recOf gs).map fun x => (gs ++ gs.map invA).map fun g => comp 6156 x g).flatten

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

theorem k_sifts : bAnd(j3W tW tK, bAnd(j3W bW bK, bAnd(j3W vW vK, bAnd(j3W xW xK,
    bAnd(allN 8 (fun j => j3W (sW.getD j []) (S (Nat.add 3 j))),
      j3W ruW (pc rK uK)))))) = true := by
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
      J2Cn.atK S16J3C.cnt S16J3C.T S16J3CP 1 xK)))))))))))))))))))))))) = true := by
  quickRfl

theorem k_sifts_neg : j3W vW xK = false := by
  decide +kernel

theorem k_facts_neg : Nat.beq (cntBelowK S16J3R.cnt (fun i => commK (S16J3R.T i) rK) 1) 32 =
    false := by
  decide +kernel

theorem rE : penumSlK 6156 13 (mask 13) (6156 * 13) true S16J3R.G S16J3R.GI 4 S16J3R.cnt S16J3R.T
    S16J3R.PL S16J3R.POS S16J3R.SRT S16J3R.SRI 0 S16J3R.cnt = true := by quickRfl
theorem rHF : slK S16J3R.cnt (hsortPtKF 6156 13 (mask 13) S16J3R.cnt S16J3R.T S16J3R.HS S16J3R.HSI)
    0 S16J3R.cnt = true := by quickRfl
theorem rCl : slK (Nat.mul S16J3R.cnt 8)
    (findPtK S16J3R.cnt S16J3R.T (prodQK 6156 13 (mask 13) 8 S16J3R.T (bothK 4 S16J3R.GI S16J3RI))
      S16J3RCl) 0 (Nat.mul S16J3R.cnt 8) = true := by quickRfl

theorem vE : penumSlK 6156 13 (mask 13) (6156 * 13) true S16J3V.G S16J3V.GI 2 S16J3V.cnt S16J3V.T
    S16J3V.PL S16J3V.POS S16J3V.SRT S16J3V.SRI 0 S16J3V.cnt = true := by quickRfl
theorem vHF : slK S16J3V.cnt (hsortPtKF 6156 13 (mask 13) S16J3V.cnt S16J3V.T S16J3V.HS S16J3V.HSI)
    0 S16J3V.cnt = true := by quickRfl
theorem vCl : slK (Nat.mul S16J3V.cnt 4)
    (findPtK S16J3V.cnt S16J3V.T (prodQK 6156 13 (mask 13) 4 S16J3V.T (bothK 2 S16J3V.GI S16J3VI))
      S16J3VCl) 0 (Nat.mul S16J3V.cnt 4) = true := by quickRfl

theorem wE : penumSlK 6156 13 (mask 13) (6156 * 13) true S16J3W.G S16J3W.GI 3 S16J3W.cnt S16J3W.T
    S16J3W.PL S16J3W.POS S16J3W.SRT S16J3W.SRI 0 S16J3W.cnt = true := by quickRfl
theorem wHF : slK S16J3W.cnt (hsortPtKF 6156 13 (mask 13) S16J3W.cnt S16J3W.T S16J3W.HS S16J3W.HSI)
    0 S16J3W.cnt = true := by quickRfl
theorem wCl : slK (Nat.mul S16J3W.cnt 6)
    (findPtK S16J3W.cnt S16J3W.T (prodQK 6156 13 (mask 13) 6 S16J3W.T (bothK 3 S16J3W.GI S16J3WI))
      S16J3WCl) 0 (Nat.mul S16J3W.cnt 6) = true := by quickRfl

theorem cE : penumSlK 6156 13 (mask 13) (6156 * 13) true S16J3C.G S16J3C.GI 4 S16J3C.cnt S16J3C.T
    S16J3C.PL S16J3C.POS S16J3C.SRT S16J3C.SRI 0 S16J3C.cnt = true := by quickRfl
theorem cHF : slK S16J3C.cnt (hsortPtKF 6156 13 (mask 13) S16J3C.cnt S16J3C.T S16J3C.HS S16J3C.HSI)
    0 S16J3C.cnt = true := by quickRfl
theorem cCl : slK (Nat.mul S16J3C.cnt 8)
    (findPtK S16J3C.cnt S16J3C.T (prodQK 6156 13 (mask 13) 8 S16J3C.T (bothK 4 S16J3C.GI S16J3CI))
      S16J3CCl) 0 (Nat.mul S16J3C.cnt 8) = true := by quickRfl

theorem rHF_neg : hsortPtKF 6156 13 (mask 13) S16J3R.cnt (fun _ => 0) S16J3R.HS S16J3R.HSI 0 =
    false := by
  decide +kernel

end CertificateChecks.KernelSpor.S16J3

end

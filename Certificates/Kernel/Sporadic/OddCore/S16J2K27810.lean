module

public import Certificates.Kernel.Sporadic.OddCore.F1K27811
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYData
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
meta import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
meta import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.J2BetaT CFSG.EvenSporadicStandard.Fin76b.Beta.j2BetaHex

#kmisc_hexflat CertificateChecks.KernelSpor.J2BetaT CFSG.EvenSporadicStandard.Fin76b.Beta.j2BetaHex
  3 315 9 13

namespace CertificateChecks.KernelSpor.S16J2

open CFSG.EvenSporadicStandard.Fin76b.S16 CFSG.EvenSporadicStandard.Fin76b.Beta
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.SmallOddCore

meta def idM : Array Nat := idTab 315
meta def tbM (k : Nat) : Table := j2Tb k
meta def tM (k : Nat) : Array Nat := natArr (j2Tb k)
meta def iM (x : Table) : Array Nat := natArr (invT 315 x)
meta def cmM (x y : Table) : Array Nat := natArr (compT 315 x y)

meta def rootsM : Array (Array Nat) := #[tM 3, tM 4, tM 5, tM 6]
meta def vvM : Array (Array Nat) := #[cmM (tbM 1) (tbM 1), cmM (tbM 1) (tbM 2)]
meta def wM : Array (Array Nat) := #[tM 1, tM 2, tM 0]
meta def csM : Array (Array Nat) := #[cmM (tbM 7) (tbM 0), tM 8, tM 9, tM 10, tM 11]

meta def idsM (k : Nat) : Array (Array Nat) := Array.replicate k idM
meta def ids2M : Array (Array Nat) := idsM 2
meta def ids3M : Array (Array Nat) := idsM 3
meta def ids4M : Array (Array Nat) := idsM 4
meta def ids5M : Array (Array Nat) := idsM 5

meta def invA (a : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 315 a
meta def recOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 315 idM gs[j]! t) gs.size idM 40).tabs
meta def clOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  ((recOf gs).map fun x => (gs ++ gs.map invA).map fun g => comp 315 x g).flatten

meta def rRecM : Array (Array Nat) := recOf rootsM
meta def vRecM : Array (Array Nat) := recOf vvM
meta def wRecM : Array (Array Nat) := recOf wM
meta def cRecM : Array (Array Nat) := recOf csM
meta def rClM : Array (Array Nat) := clOf rootsM
meta def vClM : Array (Array Nat) := clOf vvM
meta def wClM : Array (Array Nat) := clOf wM
meta def cClM : Array (Array Nat) := clOf csM

meta def rIM : Array (Array Nat) := rootsM.map invA
meta def vIM : Array (Array Nat) := vvM.map invA
meta def wIM : Array (Array Nat) := wM.map invA
meta def cIM : Array (Array Nat) := csM.map invA
meta def cAM : Array (Array Nat) := cRecM.map invA

meta def mIM : Array (Array Nat) := #[iM (j2BetaTbl 7), iM (tbM 1), iM (tbM 7)]

meta def rPM : Array (Array Nat) := vvM
meta def cPM : Array (Array Nat) := #[natArr (j2CentTbl 31), tM 2]

end CertificateChecks.KernelSpor.S16J2

open CertificateChecks.KernelSpor.S16J2 in
#kmulh CertificateChecks.KernelSpor.S16J2R 315 9 ids4M rootsM idM 40
open CertificateChecks.KernelSpor.S16J2 in
#kmulh CertificateChecks.KernelSpor.S16J2V 315 9 ids2M vvM idM 40
open CertificateChecks.KernelSpor.S16J2 in
#kmulh CertificateChecks.KernelSpor.S16J2W 315 9 ids3M wM idM 40
open CertificateChecks.KernelSpor.S16J2 in
#kmulh CertificateChecks.KernelSpor.S16J2C 315 9 ids5M csM idM 40
open CertificateChecks.KernelSpor.S16J2 in
#kfind CertificateChecks.KernelSpor.S16J2RCl rRecM rClM
open CertificateChecks.KernelSpor.S16J2 in
#kfind CertificateChecks.KernelSpor.S16J2VCl vRecM vClM
open CertificateChecks.KernelSpor.S16J2 in
#kfind CertificateChecks.KernelSpor.S16J2WCl wRecM wClM
open CertificateChecks.KernelSpor.S16J2 in
#kfind CertificateChecks.KernelSpor.S16J2CCl cRecM cClM
open CertificateChecks.KernelSpor.S16J2 in
#kfind CertificateChecks.KernelSpor.S16J2RP rRecM rPM
open CertificateChecks.KernelSpor.S16J2 in
#kfind CertificateChecks.KernelSpor.S16J2CP cRecM cPM
open CertificateChecks.KernelSpor.S16J2 in
#kmisc_packarrs CertificateChecks.KernelSpor.S16J2RI rIM 9
open CertificateChecks.KernelSpor.S16J2 in
#kmisc_packarrs CertificateChecks.KernelSpor.S16J2VI vIM 9
open CertificateChecks.KernelSpor.S16J2 in
#kmisc_packarrs CertificateChecks.KernelSpor.S16J2WI wIM 9
open CertificateChecks.KernelSpor.S16J2 in
#kmisc_packarrs CertificateChecks.KernelSpor.S16J2CI cIM 9
open CertificateChecks.KernelSpor.S16J2 in
#kmisc_packarrs CertificateChecks.KernelSpor.S16J2CA cAM 9
open CertificateChecks.KernelSpor.S16J2 in
#kmisc_packarrs CertificateChecks.KernelSpor.S16J2MI mIM 9

namespace CertificateChecks.KernelSpor.S16J2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.PkPow
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 315 9 (mask 9) (315 * 9) p

@[expose] noncomputable def iK (p q : Nat) : Bool := invEqK 315 9 (mask 9) (315 * 9) p q

@[expose] noncomputable def S (k : Nat) : Nat := TS16J2T.F k

@[expose] noncomputable def tK : Nat := F 31
@[expose] noncomputable def bK : Nat := J2BetaT.F 7
@[expose] noncomputable def rK : Nat := S 0
@[expose] noncomputable def vK : Nat := S 1
@[expose] noncomputable def xK : Nat := S 2

@[expose] noncomputable def quadK (y : Nat) : Bool :=
  Nat.beq y idK || Nat.beq y tK || Nat.beq y xK || Nat.beq y (pc tK xK)

theorem k_base : bAnd(cK bK, bAnd(cK (S 7), bAnd(cK rK, bAnd(cK vK, bAnd(cK xK,
    bAnd(allN 3 (fun j => cK (S16J2MI j)),
    bAnd(iK bK (S16J2MI 0), bAnd(iK vK (S16J2MI 1), bAnd(iK (S 7) (S16J2MI 2),
    bAnd(iK rK rK, bAnd(iK xK xK,
    bAnd(allN 4 (fun j => bAnd(Nat.beq (S16J2R.GI j) (S (Nat.add 3 j)), bAnd(Nat.beq (S16J2R.G j) idK,
      bAnd(cK (S16J2R.GI j), bAnd(cK (S16J2RI j), iK (S16J2R.GI j) (S16J2RI j)))))),
    bAnd(Nat.beq (S16J2V.GI 0) (pc vK vK), bAnd(Nat.beq (S16J2V.GI 1) (pc vK xK),
    bAnd(allN 2 (fun j => bAnd(Nat.beq (S16J2V.G j) idK,
      bAnd(cK (S16J2V.GI j), bAnd(cK (S16J2VI j), iK (S16J2V.GI j) (S16J2VI j))))),
    bAnd(Nat.beq (S16J2W.GI 0) vK, bAnd(Nat.beq (S16J2W.GI 1) xK, bAnd(Nat.beq (S16J2W.GI 2) rK,
    bAnd(allN 3 (fun j => bAnd(Nat.beq (S16J2W.G j) idK,
      bAnd(cK (S16J2W.GI j), bAnd(cK (S16J2WI j), iK (S16J2W.GI j) (S16J2WI j))))),
    bAnd(Nat.beq (S16J2C.GI 0) (pc (S 7) rK),
    bAnd(allN 4 (fun j => Nat.beq (S16J2C.GI (Nat.succ j)) (S (Nat.add 8 j))),
    bAnd(allN 5 (fun j => bAnd(Nat.beq (S16J2C.G j) idK,
      bAnd(cK (S16J2C.GI j), bAnd(cK (S16J2CI j), iK (S16J2C.GI j) (S16J2CI j))))),
    bAnd(Nat.beq S16J2R.cnt 32, bAnd(Nat.beq S16J2V.cnt 8, bAnd(Nat.beq S16J2W.cnt 32,
    bAnd(Nat.beq S16J2C.cnt 32,
    bAnd(penumHdK idK S16J2R.cnt 40 S16J2R.T S16J2R.PL, bAnd(penumHdK idK S16J2V.cnt 40 S16J2V.T S16J2V.PL,
    bAnd(penumHdK idK S16J2W.cnt 40 S16J2W.T S16J2W.PL,
      penumHdK idK S16J2C.cnt 40 S16J2C.T S16J2C.PL))))))))))))))))))))))))))))) = true := by
  quickRfl

theorem k_facts : bAnd(sK tK, bAnd(sK bK, bAnd(sK vK, bAnd(sK xK,
    bAnd(allN 4 (fun j => sK (S (Nat.add 3 j))), bAnd(allN 5 (fun j => sK (S (Nat.add 7 j))),
    bAnd(sK (pc rK (F 0)), bAnd(bIf(sK rK, false, true),
    bAnd(Nat.beq (pc rK rK) idK, bAnd(Nat.beq (pc (pc rK tK) rK) tK,
    bAnd(Nat.beq (pc (pc rK bK) rK) (S16J2MI 0),
    bAnd(commK vK tK, bAnd(commK xK tK,
    bAnd(Nat.beq (ppw 315 9 vK 4) tK, bAnd(Nat.beq (ppw 315 9 vK 8) idK,
    bAnd(Nat.beq (pc xK xK) idK, bAnd(bIf(Nat.beq xK idK, false, true),
    bAnd(bIf(Nat.beq xK tK, false, true),
    bAnd(Nat.beq (pc (pc xK vK) xK) (S16J2MI 1),
    bAnd(Nat.beq (pc (pc rK vK) rK) (pc vK tK), bAnd(Nat.beq (pc (pc rK xK) rK) (pc xK tK),
    bAnd(Nat.beq (pc (pc vK bK) (S16J2MI 1)) (S16J2MI 0),
    bAnd(Nat.beq (pc (pc xK bK) xK) (S16J2MI 0),
    bAnd(allN 4 (fun j => Nat.beq (pc (S (Nat.add 3 j)) (S (Nat.add 3 j))) tK),
    bAnd(Nat.beq (cntBelowK S16J2R.cnt (fun i => commK (S16J2R.T i) rK) 1) 8,
    bAnd(atK S16J2R.cnt S16J2R.T S16J2RP 0 (pc vK vK), bAnd(atK S16J2R.cnt S16J2R.T S16J2RP 1 (pc vK xK),
    bAnd(commK (pc vK vK) rK, bAnd(commK (pc vK xK) rK,
    bAnd(allN 5 (fun j => commK (S (Nat.add 7 j)) tK),
    bAnd(allN 5 (fun j => commK (S16J2C.GI j) xK),
    bAnd(atK S16J2C.cnt S16J2C.T S16J2CP 0 tK,
      atK S16J2C.cnt S16J2C.T S16J2CP 1 xK)))))))))))))))))))))))))))))))) = true := by
  quickRfl

theorem k_quad : allN 32 (fun i => bAnd(cK (S16J2CA i), bAnd(iK (S16J2C.T i) (S16J2CA i),
    bAnd(quadK (pc (S16J2C.T i) (S16J2C.T i)),
    allN 32 (fun j => quadK (pc (pc (S16J2C.T i) (S16J2C.T j)) (pc (S16J2CA i) (S16J2CA j)))))))) =
    true := by
  quickRfl

theorem rE : penumSlK 315 9 (mask 9) (315 * 9) true S16J2R.G S16J2R.GI 4 S16J2R.cnt S16J2R.T
    S16J2R.PL S16J2R.POS S16J2R.SRT S16J2R.SRI 0 S16J2R.cnt = true := by quickRfl
theorem rH : slK S16J2R.cnt (hsortPtK 315 9 (mask 9) S16J2R.cnt S16J2R.T S16J2R.HS S16J2R.HSI) 0
    S16J2R.cnt = true := by quickRfl
theorem rCl : slK (Nat.mul S16J2R.cnt 8)
    (findPtK S16J2R.cnt S16J2R.T (prodQK 315 9 (mask 9) 8 S16J2R.T (bothK 4 S16J2R.GI S16J2RI))
      S16J2RCl) 0 (Nat.mul S16J2R.cnt 8) = true := by quickRfl

theorem vE : penumSlK 315 9 (mask 9) (315 * 9) true S16J2V.G S16J2V.GI 2 S16J2V.cnt S16J2V.T
    S16J2V.PL S16J2V.POS S16J2V.SRT S16J2V.SRI 0 S16J2V.cnt = true := by quickRfl
theorem vH : slK S16J2V.cnt (hsortPtK 315 9 (mask 9) S16J2V.cnt S16J2V.T S16J2V.HS S16J2V.HSI) 0
    S16J2V.cnt = true := by quickRfl
theorem vCl : slK (Nat.mul S16J2V.cnt 4)
    (findPtK S16J2V.cnt S16J2V.T (prodQK 315 9 (mask 9) 4 S16J2V.T (bothK 2 S16J2V.GI S16J2VI))
      S16J2VCl) 0 (Nat.mul S16J2V.cnt 4) = true := by quickRfl

theorem wE : penumSlK 315 9 (mask 9) (315 * 9) true S16J2W.G S16J2W.GI 3 S16J2W.cnt S16J2W.T
    S16J2W.PL S16J2W.POS S16J2W.SRT S16J2W.SRI 0 S16J2W.cnt = true := by quickRfl
theorem wH : slK S16J2W.cnt (hsortPtK 315 9 (mask 9) S16J2W.cnt S16J2W.T S16J2W.HS S16J2W.HSI) 0
    S16J2W.cnt = true := by quickRfl
theorem wCl : slK (Nat.mul S16J2W.cnt 6)
    (findPtK S16J2W.cnt S16J2W.T (prodQK 315 9 (mask 9) 6 S16J2W.T (bothK 3 S16J2W.GI S16J2WI))
      S16J2WCl) 0 (Nat.mul S16J2W.cnt 6) = true := by quickRfl

theorem cE : penumSlK 315 9 (mask 9) (315 * 9) true S16J2C.G S16J2C.GI 5 S16J2C.cnt S16J2C.T
    S16J2C.PL S16J2C.POS S16J2C.SRT S16J2C.SRI 0 S16J2C.cnt = true := by quickRfl
theorem cH : slK S16J2C.cnt (hsortPtK 315 9 (mask 9) S16J2C.cnt S16J2C.T S16J2C.HS S16J2C.HSI) 0
    S16J2C.cnt = true := by quickRfl
theorem cCl : slK (Nat.mul S16J2C.cnt 10)
    (findPtK S16J2C.cnt S16J2C.T (prodQK 315 9 (mask 9) 10 S16J2C.T (bothK 5 S16J2C.GI S16J2CI))
      S16J2CCl) 0 (Nat.mul S16J2C.cnt 10) = true := by quickRfl

end CertificateChecks.KernelSpor.S16J2

end

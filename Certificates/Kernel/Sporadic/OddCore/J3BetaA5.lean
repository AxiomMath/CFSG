module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.PairJ3.Chain
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.Join
public import Certificates.Data.Kernel.Spor.MulHF
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5Check
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5Check
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
meta import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
meta import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#ks_chars CertificateChecks.KernelSpor.J3BetaT CFSG.EvenSporadicStandard.Fin76b.Beta.j3BetaHex

#kmisc_hexflat CertificateChecks.KernelSpor.J3BetaT
  CFSG.EvenSporadicStandard.Fin76b.Beta.j3BetaHex 4 513 13 156

namespace CertificateChecks.KernelSpor.J3BetaA5

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def betaM : Array (Array Nat) := (List.range 13).toArray.map fun k => natArr (j3BetaTbl k)

meta def idM : Array Nat := idTab 6156

meta def idsM : Array (Array Nat) := Array.replicate 2 idM

meta def gM : Array (Array Nat) := #[natArr (j3BetaTbl 5), natArr (j3BetaTbl 6)]

meta def giM : Array (Array Nat) := (gM.push (natArr (j3BetaTbl 0))).map
  (CFSG.Monster.B.Co2.Native.invCand 6156)

meta def recM : Array (Array Nat) :=
  (bfs (fun j t => conjTab 6156 idM gM[j]! t) gM.size idM 100).tabs

meta def clM : Array (Array Nat) :=
  (recM.map fun x => (gM ++ (giM.extract 0 2)).map fun g => comp 6156 x g).flatten

end CertificateChecks.KernelSpor.J3BetaA5

#kmisc_packarrs CertificateChecks.KernelSpor.J3BetaP CertificateChecks.KernelSpor.J3BetaA5.betaM 13

#kmisc_packarrs CertificateChecks.KernelSpor.J3BetaI CertificateChecks.KernelSpor.J3BetaA5.giM 13

#kmulh CertificateChecks.KernelSpor.J3BA 6156 13 CertificateChecks.KernelSpor.J3BetaA5.idsM
  CertificateChecks.KernelSpor.J3BetaA5.gM CertificateChecks.KernelSpor.J3BetaA5.idM 100

#kfind CertificateChecks.KernelSpor.J3BACl CertificateChecks.KernelSpor.J3BetaA5.recM
  CertificateChecks.KernelSpor.J3BetaA5.clM

namespace CertificateChecks.KernelSpor.J3BetaA5

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.Join
open CertificateChecks.KernelSporSch

theorem beta_join : joinK 12 (13 * 513) J3BetaT.F J3BetaP 13 = true := by
  quickRfl

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 6156 13 (mask 13) (6156 * 13) p

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 6156 13 (mask 13) p q

theorem base_ok : bAnd(szOK 6156 13, bAnd(cK (pidn 6156 13), bAnd(CFSG.KS.Prim.idK 6156 13 (mask 13),
    bAnd(cK (J3BetaP 0), bAnd(cK (J3BetaI 2),
    bAnd(invEqK 6156 13 (mask 13) (6156 * 13) (J3BetaP 0) (J3BetaI 2),
    bAnd(allN 2 (fun j => bAnd(cK (J3BA.GI j), bAnd(cK (J3BetaI j),
      bAnd(invEqK 6156 13 (mask 13) (6156 * 13) (J3BA.GI j) (J3BetaI j),
      bAnd(Nat.beq (J3BA.GI j) (J3BetaP (Nat.add j 5)), bAnd(Nat.beq (J3BA.G j) (pidn 6156 13),
      Nat.beq (pc (J3BetaP 0) (J3BA.GI j)) (pc (J3BA.GI j) (J3BetaP 0)))))))),
    bAnd(Nat.beq (J3BetaP 6) (J3BetaP 7), bAnd(Nat.beq (J3BetaP 0) (J3BetaP 8),
    bAnd(Nat.beq J3BA.cnt 60, penumHdK (pidn 6156 13) J3BA.cnt 100 J3BA.T J3BA.PL)))))))))) =
      true := by
  quickRfl

theorem sE : penumSlK 6156 13 (mask 13) (6156 * 13) true J3BA.G J3BA.GI 2 J3BA.cnt J3BA.T
    J3BA.PL J3BA.POS J3BA.SRT J3BA.SRI 0 J3BA.cnt = true := by quickRfl

theorem sHF : slK J3BA.cnt (hsortPtKF 6156 13 (mask 13) J3BA.cnt J3BA.T J3BA.HS J3BA.HSI)
    0 J3BA.cnt = true := by quickRfl

theorem sHF_neg : hsortPtKF 6156 13 (mask 13) J3BA.cnt (fun _ => 0) J3BA.HS J3BA.HSI 0 = false := by
  decide +kernel

theorem sCl : slK (Nat.mul J3BA.cnt 4)
    (findPtK J3BA.cnt J3BA.T (prodQK 6156 13 (mask 13) 4 J3BA.T (bothK 2 J3BA.GI J3BetaI)) J3BACl)
    0 (Nat.mul J3BA.cnt 4) = true := by quickRfl

@[expose] def aWord : List Int := [1, -5, 1, 3, 5, 1, 4, 5]

@[expose] def bWord : List Int := [-5, 3, 4, 3, -2, 5, -3, 1, -3, 5, 3, 4, -5]

theorem a_word : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 aWord (J3BetaP 5) =
    true := by
  quickRfl

theorem b_word : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 bWord (J3BetaP 6) =
    true := by
  quickRfl

theorem a_word_neg : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 aWord (J3BetaP 6) =
    false := by
  decide +kernel

end CertificateChecks.KernelSpor.J3BetaA5

end

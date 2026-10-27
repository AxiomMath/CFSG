module

public import Certificates.Kernel.Sporadic.OddCore.S16J2K27810
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5Check
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5Check
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
meta import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2BetaA5

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 315

meta def idsM : Array (Array Nat) := Array.replicate 2 idM

meta def gM : Array (Array Nat) := #[natArr (j2BetaTbl 5), natArr (j2BetaTbl 6)]

meta def giM : Array (Array Nat) := (gM.push (natArr (j2BetaTbl 0))).map
  (CFSG.Monster.B.Co2.Native.invCand 315)

meta def recM : Array (Array Nat) :=
  (bfs (fun j t => conjTab 315 idM gM[j]! t) gM.size idM 100).tabs

meta def clM : Array (Array Nat) :=
  (recM.map fun x => (gM ++ (giM.extract 0 2)).map fun g => comp 315 x g).flatten

end CertificateChecks.KernelSpor.J2BetaA5

#kmisc_packarrs CertificateChecks.KernelSpor.J2BAI CertificateChecks.KernelSpor.J2BetaA5.giM 9

#kmulh CertificateChecks.KernelSpor.J2BA 315 9 CertificateChecks.KernelSpor.J2BetaA5.idsM
  CertificateChecks.KernelSpor.J2BetaA5.gM CertificateChecks.KernelSpor.J2BetaA5.idM 100

#kfind CertificateChecks.KernelSpor.J2BACl CertificateChecks.KernelSpor.J2BetaA5.recM
  CertificateChecks.KernelSpor.J2BetaA5.clM

namespace CertificateChecks.KernelSpor.J2BetaA5

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelSpor.J2Cn CertificateChecks.KernelSpor.S16J2

theorem base_ok : bAnd(szOK 315 9, bAnd(cK (pidn 315 9), bAnd(CFSG.KS.Prim.idK 315 9 (mask 9),
    bAnd(cK (J2BetaT.F 0), bAnd(cK (J2BAI 2),
    bAnd(invEqK 315 9 (mask 9) (315 * 9) (J2BetaT.F 0) (J2BAI 2),
    bAnd(allN 2 (fun j => bAnd(cK (J2BA.GI j), bAnd(cK (J2BAI j),
      bAnd(invEqK 315 9 (mask 9) (315 * 9) (J2BA.GI j) (J2BAI j),
      bAnd(Nat.beq (J2BA.GI j) (J2BetaT.F (Nat.add j 5)), bAnd(Nat.beq (J2BA.G j) (pidn 315 9),
      Nat.beq (pc (J2BetaT.F 0) (J2BA.GI j)) (pc (J2BA.GI j) (J2BetaT.F 0)))))))),
    bAnd(Nat.beq (J2BetaT.F 6) (J2BetaT.F 7), bAnd(Nat.beq (J2BetaT.F 0) (J2BetaT.F 8),
    bAnd(Nat.beq J2BA.cnt 60, penumHdK (pidn 315 9) J2BA.cnt 100 J2BA.T J2BA.PL)))))))))) =
      true := by
  quickRfl

theorem sift_ok : bAnd(sK (J2BetaT.F 5), sK (J2BetaT.F 6)) = true := by quickRfl

theorem sE : penumSlK 315 9 (mask 9) (315 * 9) true J2BA.G J2BA.GI 2 J2BA.cnt J2BA.T
    J2BA.PL J2BA.POS J2BA.SRT J2BA.SRI 0 J2BA.cnt = true := by quickRfl

theorem sH : slK J2BA.cnt (hsortPtK 315 9 (mask 9) J2BA.cnt J2BA.T J2BA.HS J2BA.HSI)
    0 J2BA.cnt = true := by quickRfl

theorem sCl : slK (Nat.mul J2BA.cnt 4)
    (findPtK J2BA.cnt J2BA.T (prodQK 315 9 (mask 9) 4 J2BA.T (bothK 2 J2BA.GI J2BAI)) J2BACl)
    0 (Nat.mul J2BA.cnt 4) = true := by quickRfl

@[expose] noncomputable def parA : Array Nat := Array.ofFn (n := 60) fun i => parOf J2BA.PL i.val

@[expose] noncomputable def labA : Array Nat := Array.ofFn (n := 60) fun i => labOf J2BA.PL i.val

@[expose] noncomputable def imgK : Array Table :=
  (List.range' 1 59).foldl (fun r k => r.push (compT 5 r[parA[k]!]! piA5J2[labA[k]!]!))
    #[idT 5]

@[expose] noncomputable def invL5 (x : Table) : Array Nat :=
  (List.range 5).foldl (fun r i => r.set! (x[i]!).toNat i) (Array.replicate 5 0)

@[expose] noncomputable def pK (x : Table) : Bool :=
  (List.range 5).all fun i => decide ((x[i]!).toNat < 5) && (invL5 x)[(x[i]!).toNat]! == i

@[expose] noncomputable def eq5 (x y : Table) : Bool := (List.range 5).all fun i => ap x i == ap y i

@[expose] noncomputable def cayK : Bool :=
  imgK.size == 60 && imgK.toList.all pK && eq5 imgK[0]! (idT 5) &&
    (List.range 60).all (fun k => (List.range 2).all fun l =>
      Nat.blt (r32 J2BACl (4 * k + l)) 60 &&
        eq5 imgK[r32 J2BACl (4 * k + l)]! (compT 5 imgK[k]! piA5J2[l]!)) &&
    (List.range 60).all (fun k => eq5 imgK[k]! (idT 5) == Nat.beq (J2BA.T k) (pidn 315 9)) &&
    piA5J2.toList.all pK

theorem cay_ok : cayK = true := by
  decide +kernel

theorem cay_neg : ((List.range 60).all fun k => (List.range 2).all fun l =>
    eq5 imgK[r32 J2BACl (4 * k + l)]! (compT 5 imgK[k]! piA5J2[1 - l]!)) = false := by
  decide +kernel

end CertificateChecks.KernelSpor.J2BetaA5

end

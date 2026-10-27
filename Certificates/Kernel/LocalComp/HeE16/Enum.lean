module

public import Certificates.Kernel.Sporadic.OddCore.HeL2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBE16Inputs
meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBE16Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBStr
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBStr

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeE16

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.GrSLit.HeldFix

meta def u1M : Array (Array Nat) := heU1Tabs ()

meta def u2M : Array (Array Nat) := heU2Tabs ()

meta def id42M : Array Nat := idTab 42

meta def normPosM (U : Array Tab) (first : Bool) : Array (Array Nat) :=
  let idx := indexOf (enumBFS 42 U 8).tabs
  ((List.range 9).toArray.map fun j => (List.range 3).toArray.map fun i =>
    let x := if first then conjTab 42 heXTabs[j]! heXInvs[j]! U[i]!
      else conjTab 42 heXInvs[j]! heXTabs[j]! U[i]!
    #[idx.getD x 0]).flatten

meta def np11M : Array (Array Nat) := normPosM (heU1Tabs ()) true

meta def np12M : Array (Array Nat) := normPosM (heU1Tabs ()) false

meta def np21M : Array (Array Nat) := normPosM (heU2Tabs ()) true

meta def np22M : Array (Array Nat) := normPosM (heU2Tabs ()) false

end CertificateChecks.KernelLC.HeE16

#kpenum CertificateChecks.KernelLC.HU1E 42 6 false CertificateChecks.KernelLC.HeE16.u1M
  CertificateChecks.KernelLC.HeE16.u1M CertificateChecks.KernelLC.HeE16.id42M 8

#kpenum CertificateChecks.KernelLC.HU2E 42 6 false CertificateChecks.KernelLC.HeE16.u2M
  CertificateChecks.KernelLC.HeE16.u2M CertificateChecks.KernelLC.HeE16.id42M 8

#kmisc_packarrs CertificateChecks.KernelLC.HeE16.NP11 CertificateChecks.KernelLC.HeE16.np11M 32

#kmisc_packarrs CertificateChecks.KernelLC.HeE16.NP12 CertificateChecks.KernelLC.HeE16.np12M 32

#kmisc_packarrs CertificateChecks.KernelLC.HeE16.NP21 CertificateChecks.KernelLC.HeE16.np21M 32

#kmisc_packarrs CertificateChecks.KernelLC.HeE16.NP22 CertificateChecks.KernelLC.HeE16.np22M 32

namespace CertificateChecks.KernelLC.HeE16

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CertificateChecks.KernelSpor

@[expose] noncomputable def normK (UG T : Nat → Nat) (cnt : Nat) (N1 N2 : Nat → Nat) : Bool :=
  allN 9 (fun j => allN 3 (fun i =>
    bAnd(strictB (N1 (Nat.add (Nat.mul 3 j) i)) (fun q => bAnd(Nat.blt q cnt,
      Nat.beq (T q) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (HXE.G j) (UG i)) (HXI j)))),
    strictB (N2 (Nat.add (Nat.mul 3 j) i)) (fun q => bAnd(Nat.blt q cnt,
      Nat.beq (T q) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (HXI j) (UG i)) (HXE.G j)))))))

@[expose] noncomputable def centK (UG : Nat → Nat) : Nat :=
  cntK (fun t => allN 3 (fun g => Nat.beq (pcomp 42 6 (mask 6) (HXE.T t) (UG g))
    (pcomp 42 6 (mask 6) (UG g) (HXE.T t)))) 168

theorem kGens : bAnd(Nat.beq HU1E.k 3, bAnd(Nat.beq HU2E.k 3,
    allN 3 (fun j => bAnd(Nat.beq (HU1E.G j) (HRE.G j),
      Nat.beq (HU2E.G j) (HRE.G (Nat.add j 3)))))) = true := by
  quickRfl

theorem kHd : bAnd(penumHdK (pidn 42 6) HU1E.cnt 8 HU1E.T HU1E.PL,
    bAnd(penumHdK (pidn 42 6) HU2E.cnt 8 HU2E.T HU2E.PL,
      bAnd(Nat.beq HU1E.cnt 8, Nat.beq HU2E.cnt 8))) = true := by
  quickRfl

theorem kSl1 : penumSlK 42 6 (mask 6) (42 * 6) false HU1E.G HU1E.GI HU1E.k HU1E.cnt HU1E.T HU1E.PL
    HU1E.POS HU1E.SRT HU1E.SRI 0 8 = true := by
  quickRfl

theorem kSl2 : penumSlK 42 6 (mask 6) (42 * 6) false HU2E.G HU2E.GI HU2E.k HU2E.cnt HU2E.T HU2E.PL
    HU2E.POS HU2E.SRT HU2E.SRI 0 8 = true := by
  quickRfl

theorem kNorm1 : normK HU1E.G HU1E.T HU1E.cnt NP11 NP12 = true := by
  quickRfl

theorem kNorm2 : normK HU2E.G HU2E.T HU2E.cnt NP21 NP22 = true := by
  quickRfl

theorem kCent1 : Nat.beq (centK HU1E.G) 64 = true := by
  quickRfl

theorem kCent2 : Nat.beq (centK HU2E.G) 64 = true := by
  quickRfl

end CertificateChecks.KernelLC.HeE16

end

module

public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.Spor.MulHF
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J3Inputs
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J3Inputs
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
meta import CFSG.GroupTheory.Fitting.CharacteristicP
meta import CFSG.GroupTheory.LocalCores.Components
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#ks_chars CertificateChecks.KernelSpor.J3HypT CFSG.EvenSporadicStandard.HypOne.J3.hypHex

#kmisc_hexflat CertificateChecks.KernelSpor.J3HypT CFSG.EvenSporadicStandard.HypOne.J3.hypHex
  4 513 13 144

namespace CertificateChecks.KernelSpor.J3HypSyl

open CFSG.EvenSporadicStandard.HypOne.J3 CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def hypM : Array (Array Nat) := (List.range 12).toArray.map fun k => natArr (hypTbl k)

meta def idM : Array Nat := idTab 6156

meta def idsM : Array (Array Nat) := Array.replicate 3 idM

meta def sM : Array (Array Nat) := sgP0.map natArr

end CertificateChecks.KernelSpor.J3HypSyl

#kmisc_packarrs CertificateChecks.KernelSpor.J3HypP CertificateChecks.KernelSpor.J3HypSyl.hypM 13

#kmulh CertificateChecks.KernelSpor.J3HS 6156 13 CertificateChecks.KernelSpor.J3HypSyl.idsM
  CertificateChecks.KernelSpor.J3HypSyl.sM CertificateChecks.KernelSpor.J3HypSyl.idM 128

namespace CertificateChecks.KernelSpor.J3HypSyl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.Join

theorem hyp_join : joinK 12 (13 * 513) J3HypT.F J3HypP 12 = true := by
  quickRfl

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 6156 13 (mask 13) (6156 * 13) p

theorem base_ok : bAnd(szOK 6156 13, bAnd(cK (pidn 6156 13), bAnd(CFSG.KS.Prim.idK 6156 13 (mask 13),
    bAnd(cK (J3CentP 9),
    bAnd(allN 3 (fun j => bAnd(cK (J3HS.GI j), bAnd(Nat.beq (J3HS.GI j) (J3HypP (Nat.add j 1)),
      Nat.beq (J3HS.G j) (pidn 6156 13)))),
    bAnd(Nat.beq J3HS.cnt 128, penumHdK (pidn 6156 13) J3HS.cnt 128 J3HS.T J3HS.PL)))))) =
      true := by
  quickRfl

theorem sE : penumSlK 6156 13 (mask 13) (6156 * 13) true J3HS.G J3HS.GI 3 J3HS.cnt J3HS.T
    J3HS.PL J3HS.POS J3HS.SRT J3HS.SRI 0 J3HS.cnt = true := by quickRfl

theorem sHF : slK J3HS.cnt (hsortPtKF 6156 13 (mask 13) J3HS.cnt J3HS.T J3HS.HS J3HS.HSI)
    0 J3HS.cnt = true := by quickRfl

theorem sHF_neg : hsortPtKF 6156 13 (mask 13) J3HS.cnt (fun _ => 0) J3HS.HS J3HS.HSI 0 = false := by
  decide +kernel

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 6156 13 (mask 13) p q

@[expose] noncomputable def centerK (t : Nat) : Bool :=
  (List.range 128).any (fun i => Nat.beq (J3HS.T i) t) &&
    (List.range 128).all (fun i =>
      !((List.range 3).all fun j => Nat.beq (pc (J3HS.T i) (J3HS.GI j)) (pc (J3HS.GI j) (J3HS.T i))) ||
        Nat.beq (J3HS.T i) (pidn 6156 13) || Nat.beq (J3HS.T i) t) &&
    (List.range 128).any (fun i => Nat.beq (pc (J3HS.T i) (J3HS.T i)) t)

@[expose] noncomputable def centerKF (t : Nat) : Bool :=
  (List.range 128).any (fun i => Nat.beq (J3HS.T i) t) &&
    (List.range 128).all (fun i =>
      !((List.range 3).all fun j =>
          eq22 6156 13 (mask 13) (J3HS.T i) (J3HS.GI j) (J3HS.GI j) (J3HS.T i)) ||
        Nat.beq (J3HS.T i) (pidn 6156 13) || Nat.beq (J3HS.T i) t) &&
    (List.range 128).any (fun i => eq2 6156 13 (mask 13) t (J3HS.T i) (J3HS.T i))

theorem center_okF : centerKF (J3CentP 9) = true := by
  quickRfl

theorem center_neg : centerKF (pidn 6156 13) = false := by
  decide +kernel

end CertificateChecks.KernelSpor.J3HypSyl

end

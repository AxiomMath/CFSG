module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue2
public import Certificates.Kernel.LocalComp.L34RData
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicCertInputs
public import Certificates.Data.CFSGNative.PSL3Four.L34RLev
meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicCertInputs
meta import Certificates.Data.CFSGNative.PSL3Four.L34RLev
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
meta import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34E16

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts

meta def tM : Array (Array Nat) := wordTabs wT₀

meta def eM : Array (Array Nat) := e16Gens

meta def idM : Array Nat := idTab 42

end CertificateChecks.KernelLC.L34E16

#kpenum CertificateChecks.KernelLC.ETE 42 6 false CertificateChecks.KernelLC.L34E16.tM
  CertificateChecks.KernelLC.L34E16.tM CertificateChecks.KernelLC.L34E16.idM 64

#kpenum CertificateChecks.KernelLC.EEE 42 6 false CertificateChecks.KernelLC.L34E16.eM
  CertificateChecks.KernelLC.L34E16.eM CertificateChecks.KernelLC.L34E16.idM 16

namespace CertificateChecks.KernelLC.L34E16

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] noncomputable def wfoldL (G : Nat → Nat) (acc : Nat) (wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun j _ ih a => ih (pcomp 42 6 (mask 6) a (G j))) wd acc

@[expose] noncomputable def lg (j : Nat) : Nat :=
  [L34R.G 0, L34R.G 1, L34R.G 2].getD j (L34R.G 2)

theorem k_gens : bAnd(Nat.beq ETE.k 4, bAnd(allN 4 (fun j =>
    Nat.beq (ETE.G j) (wfoldL lg (pidn 42 6) (lget2 wT₀ j))),
    gensK e16Gens 42 6 EEE.k EEE.G)) = true := by
  quickRfl

theorem k_hd : bAnd(penumHdK (pidn 42 6) ETE.cnt 64 ETE.T ETE.PL,
    bAnd(penumHdK (pidn 42 6) EEE.cnt 16 EEE.T EEE.PL, Nat.beq EEE.cnt 16)) = true := by
  quickRfl

theorem k_slT : penumSlK 42 6 (mask 6) (42 * 6) false ETE.G ETE.GI ETE.k ETE.cnt ETE.T ETE.PL
    ETE.POS ETE.SRT ETE.SRI 0 64 = true := by
  quickRfl

theorem k_slE : penumSlK 42 6 (mask 6) (42 * 6) false EEE.G EEE.GI EEE.k EEE.cnt EEE.T EEE.PL
    EEE.POS EEE.SRT EEE.SRI 0 16 = true := by
  quickRfl

theorem k_in : allN 4 (fun j => (allN ETE.cnt (fun q => (Nat.beq (ETE.T q) (EEE.G j)).not)).not) =
    true := by
  quickRfl

theorem k_ab : allN 16 (fun a => bAnd(Nat.beq (pcomp 42 6 (mask 6) (EEE.T a) (EEE.T a)) (pidn 42 6),
    allN 16 (fun b => Nat.beq (pcomp 42 6 (mask 6) (EEE.T a) (EEE.T b))
      (pcomp 42 6 (mask 6) (EEE.T b) (EEE.T a))))) = true := by
  quickRfl

end CertificateChecks.KernelLC.L34E16

end

module

public import Certificates.Kernel.Sporadic.OddCore.SuzDData
public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Data.Kernel.CentScan
public import Certificates.Data.Kernel.L34Scan
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzOuterCheck
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelSpor.SuzK0

meta def idM : Array Nat := CFSG.PSL3Four.Native.idTab 42

meta def svM : Array (Array Nat) := #[CFSG.EvenSporadicStandard.Solomon78.suzTabV0]

meta def dM : Array (Array Nat) := CFSG.Sporadic.SuzOddCore.dGens

end CertificateChecks.KernelSpor.SuzK0

public section

set_option maxRecDepth 400000

#kpenum CertificateChecks.KernelSpor.SK0 42 6 false CertificateChecks.KernelSpor.SuzDGen.kM
  CertificateChecks.KernelSpor.SuzDGen.kM CertificateChecks.KernelSpor.SuzK0.idM 40320

#kmisc_packarrs CertificateChecks.KernelSpor.SuzSV CertificateChecks.KernelSpor.SuzK0.svM 6

#kmisc_packarrs CertificateChecks.KernelSpor.SuzDP CertificateChecks.KernelSpor.SuzK0.dM 6

namespace CertificateChecks.KernelSpor.SuzK0

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CertificateChecks.KernelSpor
open CFSG.KC.L34Scan CFSG.KC.CentScan
open CFSG.KLie.CT (andB)

@[expose] noncomputable def kSl (s : Nat) : Bool :=
  penumSlK 42 6 (mask 6) (42 * 6) false SK0.G SK0.GI 22 SK0.cnt SK0.T SK0.PL SK0.POS SK0.SRT
    SK0.SRI (Nat.mul s (nat_lit 1260)) (nat_lit 1260)

theorem k_hd : andB (Nat.beq SK0.cnt 40320) (andB (Nat.beq SK0.k 22)
    (andB (penumHdK (pidn 42 6) SK0.cnt 40320 SK0.T SK0.PL)
      (allN 22 fun j => Nat.beq (SK0.G j) (SuzDK.K j)))) = true := by
  quickRfl

@[expose] noncomputable def scSl (s : Nat) : Bool :=
  strictB (pidn 42 6) fun e => strictB (SuzSV 0) fun v =>
    scanSl (fun x => andB (centIdK 42 6 5 SuzDP e x) (offK 42 6 5 SuzDP v x)) SK0.T 1260 s

end CertificateChecks.KernelSpor.SuzK0

end

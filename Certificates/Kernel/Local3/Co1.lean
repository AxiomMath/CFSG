module

public import Certificates.Data.Kernel.Local3K
public import Certificates.Kernel.LocalComp.M1Gen
public import Certificates.Kernel.Local3.Masks
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Kernel.Local3.Masks
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.Certificates.NativeSchreierCard
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.Open.Defs

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelLocal3.Co1.SA CFSG.Blueprint.NativeSporadic.Co1Seed1
#lc_m1 CertificateChecks.KernelLocal3.Co1.SA CFSG.Blueprint.NativeSporadic.Co1Seed1 24
#ks_chars CertificateChecks.KernelLocal3.Co1.SB CFSG.Blueprint.NativeSporadic.Co1Seed2
#lc_m1 CertificateChecks.KernelLocal3.Co1.SB CFSG.Blueprint.NativeSporadic.Co1Seed2 24
#ks_chars CertificateChecks.KernelLocal3.Co1.MS CertificateChecks.KernelLocal3.co1Masks

namespace CertificateChecks.KernelLocal3.Co1

open CFSG.KC.Local3K CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

set_option maxHeartbeats 0 in
theorem local3_K : local3K 24 SA.M SB.M MS.chars co1Local3 co1Root = true := by
  decide +kernel

theorem local3_neg :
    (!local3K 24 SA.M SB.M MS.chars { co1Local3 with ords := [2, 2, 3] } co1Root) = true := by
  decide +kernel

end CertificateChecks.KernelLocal3.Co1

end

module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Insp443He
public meta import Certificates.Data.Insp443He

public section

namespace CertificateChecks.KernelSchreierFam.He725

open CFSG.SectionRank.QTK.Insp443.He CFSG.Quasithin.KGC31.He CFSG.Monster.B.Co2.Native

meta def cArrM : Array (Array Nat) := #[wA c7W, wAi c7W]

meta def qAM : Array (Array Nat) := qA.toArray

meta def sufM (wd : List Int) : Array (Array Nat) :=
  (Array.range ((wd.length + 31) / 32 + 1)).map fun i => wA (wd.drop (32 * i))

meta def r0M : Array (Array Nat) := sufM x7W
meta def r1M : Array (Array Nat) := sufM c7W
meta def r2M : Array (Array Nat) := sufM (qW.getD 0 [])
meta def r3M : Array (Array Nat) := sufM (qW.getD 1 [])
meta def r4M : Array (Array Nat) := sufM (qW.getD 2 [])
meta def r5M : Array (Array Nat) := sufM (qW.getD 3 [])

end CertificateChecks.KernelSchreierFam.He725

#kmisc_packarrs CertificateChecks.KernelSchreierFam.He725.R0
  CertificateChecks.KernelSchreierFam.He725.r0M 14
#kmisc_packarrs CertificateChecks.KernelSchreierFam.He725.R1
  CertificateChecks.KernelSchreierFam.He725.r1M 14
#kmisc_packarrs CertificateChecks.KernelSchreierFam.He725.R2
  CertificateChecks.KernelSchreierFam.He725.r2M 14
#kmisc_packarrs CertificateChecks.KernelSchreierFam.He725.R3
  CertificateChecks.KernelSchreierFam.He725.r3M 14
#kmisc_packarrs CertificateChecks.KernelSchreierFam.He725.R4
  CertificateChecks.KernelSchreierFam.He725.r4M 14
#kmisc_packarrs CertificateChecks.KernelSchreierFam.He725.R5
  CertificateChecks.KernelSchreierFam.He725.r5M 14

#kmisc_packarrs CertificateChecks.KernelSchreierFam.He725.CC
  CertificateChecks.KernelSchreierFam.He725.cArrM 14
#kmisc_packarrs CertificateChecks.KernelSchreierFam.He725.QQ
  CertificateChecks.KernelSchreierFam.He725.qAM 14

end

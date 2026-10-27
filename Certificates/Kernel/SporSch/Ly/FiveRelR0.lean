module

public import Certificates.Kernel.SporSch.Ly.FiveRelData
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LyFR

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyFiveRel CertificateChecks.KernelSporSch.LyBS

@[expose] noncomputable def relK (k : Nat) : Bool :=
  bAnd(relAt mul LyFL.D.AA LyFL.D.BB (LyFTP.F 0) (LyFTG.F 0) (LyFRN.F 0) (LyFRQ.F 0) TT NF k 0,
    relAt mul LyFL.D.AA LyFL.D.BB (LyFTP.F 0) (LyFTG.F 0) (LyFRN.F 0) (LyFRQ.F 0) TT NF k 1)

@[expose] noncomputable def relBlk (g : Nat) : Bool := allBlk (Nat.mul 32 g) relK 32

end CertificateChecks.KernelSporSch.LyFR

#kss_each CertificateChecks.KernelSporSch.LyFRR0 CertificateChecks.KernelSporSch.LyFR.relBlk 45

end

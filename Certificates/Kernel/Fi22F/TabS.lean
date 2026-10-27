module

public import Certificates.Kernel.Fi22F.TabSData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelFi22F

open CFSG.KC.LceJson CFSG.KD.FiFS

theorem tabS_ok : tabOk B WT RT ST LV INV INV8 (nat_lit 12) nC mLV a m HS (nat_lit 204) (nat_lit 73) nf JF JV
    S1 X1 = true := by
  quickRfl

end CertificateChecks.KernelFi22F

end

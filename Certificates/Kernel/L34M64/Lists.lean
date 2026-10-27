module

public import Certificates.Data.Kernel.L34M64.Twin
public import Certificates.Kernel.L34M64.Data
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelL34M64

open CFSG.KC.L34M64 CFSG.KD.L34M64

theorem ch7241out :
    (OUT == [CFSG.Quasithin.H13.Ch9.L34M.idC64, FLD, GR, compK FLD GR]) = true := by
  quickRfl

theorem ch7241u : (U == (List.range 64).map fun u => compK (X23.getD (u / 16 % 4) [])
    (compK (X12.getD (u % 4) []) (X13.getD (u / 4 % 4) []))) = true := by
  quickRfl

theorem ch7241cols : (COLS == (List.range 256).map fun p =>
    compK (U.getD (p % 64) []) (OUT.getD (p / 64 % 2 + 2 * (p / 128 % 2)) [])) = true := by
  quickRfl

theorem ch7241dat : (DAT == (COLS.filter isInvK).map fun cs => (cs, pickWitK 64 3 cs)) = true := by
  quickRfl

theorem ch7241k1 : chk1K 64 DAT = true := by
  quickRfl

end CertificateChecks.KernelL34M64

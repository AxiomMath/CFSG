module

public import Certificates.Kernel.TitsOver.Three.SEnum3
public import Certificates.Kernel.MaxD2.TitsD.Data
public import Certificates.Data.Kernel.TitsOver.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TitsOver
open CertificateChecks.KernelMaxD2.TitsD (PT)

theorem s3_sl3200 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 3200 400 = true := by quickRfl
theorem s3_sl3600 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 3600 400 = true := by quickRfl
theorem s3_sl4000 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 4000 400 = true := by quickRfl
theorem s3_sl4400 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 4400 400 = true := by quickRfl
theorem s3_sl4800 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 4800 400 = true := by quickRfl
theorem s3_sl5200 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 5200 400 = true := by quickRfl
theorem s3_sl5600 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 5600 400 = true := by quickRfl
theorem s3_sl6000 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 6000 400 = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end

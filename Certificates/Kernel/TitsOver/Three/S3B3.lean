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

theorem s3_sl9600 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 9600 400 = true := by quickRfl
theorem s3_sl10000 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 10000 400 = true := by quickRfl
theorem s3_sl10400 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 10400 400 = true := by quickRfl
theorem s3_sl10800 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 10800 400 = true := by quickRfl
theorem s3_sl11200 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 11200 400 = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end

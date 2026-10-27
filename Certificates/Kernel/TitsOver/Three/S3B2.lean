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

theorem s3_sl6400 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 6400 400 = true := by quickRfl
theorem s3_sl6800 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 6800 400 = true := by quickRfl
theorem s3_sl7200 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 7200 400 = true := by quickRfl
theorem s3_sl7600 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 7600 400 = true := by quickRfl
theorem s3_sl8000 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 8000 400 = true := by quickRfl
theorem s3_sl8400 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 8400 400 = true := by quickRfl
theorem s3_sl8800 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 8800 400 = true := by quickRfl
theorem s3_sl9200 : penumSlBK 1755 11 (mask 11) (1755 * 11) S3E.G S3E.k S3E.cnt 6 (r32 PT) S3E.T
    S3E.PL S3E.POS S3E.SRT S3E.SRI 9200 400 = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end

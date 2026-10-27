module

public import Certificates.Data.Kernel.SporSch.OddRows
public import CFSG.LocalAnalysis.OddStandard.MathieuInvolutionData
public import Certificates.Kernel.SporSch.Mathieu.M11Data
public import Certificates.Kernel.SporSch.Mathieu.M12Data
public import Certificates.Kernel.SporSch.Mathieu.M22Data
public import Certificates.Kernel.SporSch.Mathieu.M23Data
public import Certificates.Kernel.SporSch.Mathieu.M24Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.OddRowsK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.OddRows CFSG.OddStandard
open CFSG.Sporadic.Schreier CertificateChecks.KernelSporSch

theorem m11 : rowsK 11 4 M11C1.S M11C1.SI M11C1.LR M11C1.TR M11C1.TRI M11C1.BP 3
    m11CentWords1.length m11Primes1 m11Specs1 2000 = true := by quickRfl

theorem m12a : rowsK 12 4 M12C1.S M12C1.SI M12C1.LR M12C1.TR M12C1.TRI M12C1.BP 3
    m12CentWords1.length m12Primes1 m12Specs1 2000 = true := by quickRfl

theorem m12b : rowsK 12 4 M12C2.S M12C2.SI M12C2.LR M12C2.TR M12C2.TRI M12C2.BP 3
    m12CentWords2.length m12Primes2 m12Specs2 2000 = true := by quickRfl

theorem m22 : rowsK 22 5 M22C1.S M22C1.SI M22C1.LR M22C1.TR M22C1.TRI M22C1.BP 3
    m22CentWords1.length m22Primes1 m22Specs1 2000 = true := by quickRfl

theorem m23 : rowsK 23 5 M23C1.S M23C1.SI M23C1.LR M23C1.TR M23C1.TRI M23C1.BP 4
    m23CentWords1.length m23Primes1 m23Specs1 2000 = true := by quickRfl

theorem m24a : rowsK 24 5 M24C1.S M24C1.SI M24C1.LR M24C1.TR M24C1.TRI M24C1.BP 3
    m24CentWords1.length m24Primes1 m24Specs1 2000 = true := by quickRfl

theorem m24b : rowsK 24 5 M24C2.S M24C2.SI M24C2.LR M24C2.TR M24C2.TRI M24C2.BP 4
    m24CentWords2.length m24Primes2 m24Specs2 2000 = true := by quickRfl

end CertificateChecks.KernelSporSch.OddRowsK

end

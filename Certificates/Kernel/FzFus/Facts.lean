module

public import Certificates.Data.FzFusK3
import CFSG.Certificates.Kernel.FzFus.Sound
import Certificates.Kernel.FzFus.Checks

public section

namespace CertificateChecks.KernelFzFus

open Certificates.FzFus Certificates.FzFus.K

theorem classFact : ClassFact := classB_sound ch442351cls

theorem rowsFact : RowsFact := rowsB_sound ch442351rows

theorem subsFact : SubsFact := subsB_sound ch442351subs

theorem pair7Fact : Pair7Fact := p7B_sound ch442351pair

end CertificateChecks.KernelFzFus

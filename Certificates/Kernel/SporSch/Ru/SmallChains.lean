module

public import Certificates.Kernel.Sporadic.RawGenSch
public import Certificates.Kernel.Sporadic.RawGenSchPJ
public import Certificates.Kernel.Sporadic.RawGenSchPFJ
public import Certificates.Kernel.SporSch.Ru.Lines
public import Certificates.Kernel.SporSch.Ru.SCPFLv
public import Certificates.Kernel.SporSch.Ru.SCPFF0
public import Certificates.Kernel.SporSch.Ru.SCPFF1
public import Certificates.Kernel.SporSch.Ru.SCPSF0
public import Certificates.Kernel.SporSch.Ru.SCPSF1
public import Certificates.Kernel.SporSch.Ru.SCPSLv
public import Certificates.Kernel.SporSch.Ru.SCRJ
public import Certificates.Kernel.SporSch.Ru.SCRK
public import Certificates.Kernel.SporSch.Ru.SCRR
public import Certificates.Kernel.SporSch.Ru.SCRSmall
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_joinpf CertificateChecks.KernelSporSch.RuFS 1

#ks_rawchain_sl2_joinpf CertificateChecks.KernelSporSch.RuSS2 1

end

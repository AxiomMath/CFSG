module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.TextSound
public import CFSG.Sporadic.Schreier.RuDefs
meta import CFSG.Sporadic.Schreier.RuDefs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Sporadic.Schreier.RuEnum
public import Mathlib.GroupTheory.Schreier
meta import CFSG.Sporadic.Schreier.RuEnum
meta import Mathlib.GroupTheory.Schreier

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.RuT4060 CFSG.Sporadic.RuSchreier.ru4060Text

#ks_hexlines CertificateChecks.KernelSporSch.RuT4060 CFSG.Sporadic.RuSchreier.ru4060Text 3 4060 12

end

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

#ks_chars CertificateChecks.KernelSporSch.RuT1920 CFSG.Sporadic.RuSchreier.ru1920Text

#ks_hexlines CertificateChecks.KernelSporSch.RuT1920 CFSG.Sporadic.RuSchreier.ru1920Text 3 1920 11

#ks_chars CertificateChecks.KernelSporSch.RuT80 CFSG.Sporadic.RuSchreier.ru80Text

#ks_hexlines CertificateChecks.KernelSporSch.RuT80 CFSG.Sporadic.RuSchreier.ru80Text 3 80 7

end

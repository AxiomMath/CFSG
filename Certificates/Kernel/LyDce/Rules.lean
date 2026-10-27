module

public import Certificates.Kernel.LyDce.Data
public import CFSG.Sporadic.Recognition.LyonsFinalModularInputs

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100

public section

namespace CertificateChecks.KernelLyDce

open CFSG.KC.LyDce CFSG.Sporadic.Recognition.LyonsSims.LyFinal

theorem dR_ok : dRulesOK modularD dLen dR = true := by decide +kernel

end CertificateChecks.KernelLyDce

end

module

public import Certificates.Kernel.LyBase.EvWords
public import CFSG.Sporadic.Recognition.LyonsFinalCore107

public section

namespace CertificateChecks.KernelLyBase

open CFSG.Sporadic.Recognition.LyonsSims.LyFinal

theorem e_fix : eEvCore.all eFix = true := by decide +kernel

theorem tr_fix : trEvCore.all trFix = true := by decide +kernel

end CertificateChecks.KernelLyBase

end

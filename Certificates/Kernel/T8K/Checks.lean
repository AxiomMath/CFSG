module

public import Certificates.Data.Kernel.T8K
public import Certificates.Kernel.WordRelK.Tab

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelT8K.Checks

open CFSG.Monster.B.TwoA.Sp8.WordRel CFSG.KC.T8K CertificateChecks.KernelWordRelK.Tab

theorem commA1 : commPL gensA1 = true := by decide +kernel

theorem commA2 : commPL gensA2 = true := by decide +kernel

theorem commA4 : commPL gensA4' = true := by decide +kernel

theorem conjX : conjT TAB xWord xT9 = true := by decide +kernel

theorem conjY : conjT TAB yWord yT9 = true := by decide +kernel

end CertificateChecks.KernelT8K.Checks

end

module

public import Certificates.Kernel.LyDce.ChainData
public import Certificates.Data.Kernel.LyDce.Conj
public import CFSG.Sporadic.Recognition.LyonsFinalCore107

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100

public section

namespace CertificateChecks.KernelLyDce

open CFSG.KC.LyDce CFSG.Sporadic.Recognition.LyonsSims.LyFinal

theorem conj_ok : ∀ n < 4, conjOK (modularE ++ modularD) (rootC (n + 1)) (sG.getD n []) = true := by
  intro n hn
  interval_cases n <;> decide +kernel

theorem E_mem : ∀ r ∈ modularE, r ∈ Rcore107 := by decide +kernel

end CertificateChecks.KernelLyDce

end

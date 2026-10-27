module

public import Certificates.Data.Kernel.FzFus.Codes
import CFSG.Certificates.Kernel.Common.Eval
import CFSG.Certificates.Kernel.Common.Harness
meta import Certificates.Data.Kernel.FzFus.Twin

public section

namespace CertificateChecks.KernelFzFus

open Certificates.FzJt.K Certificates.FzFus.K

#kc_eval CertificateChecks.KernelFzFus Cl Certificates.FzFus.Twin.cls
#kc_eval CertificateChecks.KernelFzFus Rw Certificates.FzFus.Twin.rows
#kc_eval CertificateChecks.KernelFzFus Pr Certificates.FzFus.Twin.pairs

theorem ch442351cls : classB Cl.W = true := by quickRfl
theorem ch442351rows : rowsB rowsT Rw.W = true := by quickRfl
theorem ch442351subs : subsB subsT = true := by quickRfl
theorem ch442351pair : p7B Pr.A Pr.P Pr.X = true := by quickRfl

theorem ch442351neg_cls : classB Cl.W.tail = false := by decide +kernel
theorem ch442351neg_conj : conjOK (Nat.add 317 0) = false := by decide +kernel
theorem ch442351neg_rows : rowsB rowsT Rw.W.tail = false := by decide +kernel
theorem ch442351neg_row : rowOK (Nat.add 73 (Nat.mul 1024 4352)) = false := by decide +kernel
theorem ch442351neg_subs : subRow [0, 2, 22, 23, 21, 19, 1, 4, 7, 10, 13] = false := by
  decide +kernel
theorem ch442351neg_pair : p7B (List.cons 0 Pr.A) Pr.P Pr.X = false := by decide +kernel
theorem ch442351neg_pairP : p7B Pr.A [0] Pr.X = false := by decide +kernel

end CertificateChecks.KernelFzFus

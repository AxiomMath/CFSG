module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
meta import Certificates.Data.Kernel.MaxD2.GenHeis
meta import Certificates.Data.HSOverData
import Certificates.Data.Kernel.MaxD2.GenHeis

namespace CertificateChecks.KernelMaxD2.HSU35E

open CFSG.KS.MaxD2 Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.HSOver

meta def preNR (D : Data) : Gen.Pre :=
  { nT := (nEnum D).tabs, rT := Gen.hrTabs D, rep := #[], repi := #[], keys := #[], order := #[] }

meta def preP : Gen.Pre := preNR hsOverDataP
meta def preR : Gen.Pre := preNR hsOverDataR
meta def chPM : Array Nat := Gen.centHints hsOverDataP preP
meta def chRM : Array Nat := Gen.centHints hsOverDataR preR
meta def nhPM : Array Nat := Gen.normHints hsOverDataP preP
meta def nhRM : Array Nat := Gen.normHints hsOverDataR preR
meta def msM : Array Nat := #[Gen.torusPos hsOverDataP preP, Gen.torusPos hsOverDataR preR]

end CertificateChecks.KernelMaxD2.HSU35E

public section

#krows CertificateChecks.KernelMaxD2.HSU35E.CHP CertificateChecks.KernelMaxD2.HSU35E.chPM
#krows CertificateChecks.KernelMaxD2.HSU35E.CHR CertificateChecks.KernelMaxD2.HSU35E.chRM
#krows CertificateChecks.KernelMaxD2.HSU35E.NHP CertificateChecks.KernelMaxD2.HSU35E.nhPM
#krows CertificateChecks.KernelMaxD2.HSU35E.NHR CertificateChecks.KernelMaxD2.HSU35E.nhRM
#krows CertificateChecks.KernelMaxD2.HSU35E.MS CertificateChecks.KernelMaxD2.HSU35E.msM

end

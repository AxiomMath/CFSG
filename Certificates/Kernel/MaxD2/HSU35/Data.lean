module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.HSFiveU35Check

namespace CertificateChecks.KernelMaxD2.HSU35

open CFSG.PSL3Four.Native Certificates.FusD2Perm Certificates.MaxD2Perm Certificates.MaxD2Heis
  Certificates.HSOver Certificates.HSU35

meta def qtM : Array (Array Nat) :=
  #[tabC, invTab 100 tabC] ++ uaGens.map (invTab 100)

meta def qhM : Array Nat :=
  let wi := invTab 100 tabW
  #[((List.range 8).find? fun j => comp 100 (comp 100 tabW tabT) wi == powT 100 tabT j).getD 0]

meta def eG : Array (Array Nat) := e9Gens

meta def idT : Array Nat := idTab 100

end CertificateChecks.KernelMaxD2.HSU35

public section

#kmisc_packarrs CertificateChecks.KernelMaxD2.HSU35.QT CertificateChecks.KernelMaxD2.HSU35.qtM 7
#krows CertificateChecks.KernelMaxD2.HSU35.QH CertificateChecks.KernelMaxD2.HSU35.qhM

#kpenum CertificateChecks.KernelMaxD2.HSU35.EE 100 7 false CertificateChecks.KernelMaxD2.HSU35.eG
  CertificateChecks.KernelMaxD2.HSU35.eG CertificateChecks.KernelMaxD2.HSU35.idT 9

end

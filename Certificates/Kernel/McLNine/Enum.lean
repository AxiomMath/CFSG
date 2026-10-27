module

public import Certificates.Kernel.Sporadic.OddCore.McLL
public import CFSG.Sporadic.SmallOddCore.McLIndexNineInputs
meta import CFSG.Sporadic.SmallOddCore.McLIndexNineInputs
public import CFSG.Sporadic.SmallOddCore.LocalSpec
meta import CFSG.Sporadic.SmallOddCore.LocalSpec

public section

namespace CertificateChecks.KernelSpor.McLNine

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

meta def ugM : Array (Array Nat) := (mclIndexNineUTbls ()).toArray.map natArr

meta def id275 : Array Nat := idTab 275

meta def cwOf (t : Array Nat) : Nat :=
  ((List.range 3).find? fun j => comp 275 t ugM[j]! != comp 275 ugM[j]! t).getD 3

meta def cwM : List Nat :=
  (bfs (fun j t => comp 275 ugM[j]! t) 3 id275 128).tabs.toList.map cwOf

end CertificateChecks.KernelSpor.McLNine

#kpenum CertificateChecks.KernelSpor.MUE 275 9 false CertificateChecks.KernelSpor.McLNine.ugM
  CertificateChecks.KernelSpor.McLNine.ugM CertificateChecks.KernelSpor.McLNine.id275 128

#knatlist CertificateChecks.KernelSpor.MUE.CW CertificateChecks.KernelSpor.McLNine.cwM

end

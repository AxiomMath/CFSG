module

public import Certificates.Kernel.McLNine.Enum
meta import Certificates.Kernel.McLNine.Enum

public section

namespace CertificateChecks.KernelSpor.McLThree

open CertificateChecks.KernelSpor.McLNine

meta def eM (j q : Nat) : Nat := if j = 3 then q else (ugM[j]!)[q]!

meta def witM (q : Nat) : Nat × Nat × Nat :=
  if q = 262 ∨ q = 272 then (0, 0, 0)
  else if (List.range 3).all (fun j => eM j q == q) then (4, 0, 0)
  else
    let cs := (List.range 4).flatMap fun a => (List.range 4).flatMap fun b =>
      (List.range 4).map fun c => (a, b, c)
    (cs.find? fun (a, b, c) =>
      let x := eM a q
      let y := eM b (eM c q)
      x != q && y != q && x != y).getD (0, 0, 0)

meta def waM : List Nat := (List.range 275).map fun q => (witM q).1

meta def wbM : List Nat := (List.range 275).map fun q => (witM q).2.1

meta def wcM : List Nat := (List.range 275).map fun q => (witM q).2.2

end CertificateChecks.KernelSpor.McLThree

#knatlist CertificateChecks.KernelSpor.McL3W.A CertificateChecks.KernelSpor.McLThree.waM

#knatlist CertificateChecks.KernelSpor.McL3W.B CertificateChecks.KernelSpor.McLThree.wbM

#knatlist CertificateChecks.KernelSpor.McL3W.C CertificateChecks.KernelSpor.McLThree.wcM

end

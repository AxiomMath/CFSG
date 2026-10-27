module

public import Certificates.Kernel.U38Q.Data
public meta import Certificates.Data.HuppertU38Q.Check

public section

namespace CertificateChecks.KernelU38Q

open U38Sylow

meta def comM (a b : Array Nat) : Bool :=
  [0, 167, 270].all fun p => a[b[p]!]! == b[a[p]!]!

meta def cuM : List Nat := (List.range 729).filter fun i => cubeOne (qCert ()).pts[i]!

meta def cwM : List Nat :=
  let pts := (qCert ()).pts
  cuM.map fun u =>
    let C := (List.range 729).filter fun j => comM pts[u]! pts[j]!
    let pr : Nat × Nat :=
      if C.length == 81 then
        (C.findSome? fun j => (C.find? fun k => !comM pts[j]! pts[k]!).map fun k => (j, k)).getD
          (0, 0)
      else (0, 0)
    C.length * 1048576 + pr.1 * 1024 + pr.2

end CertificateChecks.KernelU38Q

end

#knatlist CertificateChecks.KernelU38Q.CU CertificateChecks.KernelU38Q.cuM
#knatlist CertificateChecks.KernelU38Q.CW CertificateChecks.KernelU38Q.cwM

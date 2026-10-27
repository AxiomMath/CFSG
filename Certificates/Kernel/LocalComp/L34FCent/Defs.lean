module

public import Certificates.Kernel.LocalComp.L34RData
public import Certificates.Kernel.LocalComp.L34Syl.Data
public import Certificates.Kernel.LocalComp.L34SData

public section

namespace CertificateChecks.KernelLC.L34FCent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.L34K
open CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def cen4Pt (a b c d x : Nat) : Bool :=
  orB (notB (andB (commPt 42 6 x a) (andB (commPt 42 6 x b)
    (andB (commPt 42 6 x c) (commPt 42 6 x d)))))
    (notB (notInK 16 CertificateChecks.KernelLC.L34SyF.T x))

@[expose] noncomputable def fcent6126 (lo n : Nat) : Bool :=
  strictB (CertificateChecks.KernelLC.L34SyF.T 1) fun a =>
    strictB (CertificateChecks.KernelLC.L34SyF.T 2) fun b =>
      strictB (CertificateChecks.KernelLC.L34SyF.T 3) fun c =>
        strictB (CertificateChecks.KernelLC.L34SyF.T 4) fun d =>
          allN n fun s => allN 1344 fun t =>
            strictB (Nat.add (Nat.mul 1344 (Nat.add lo s)) t) fun i =>
              strictB (CertificateChecks.KernelLC.L34R.T i) fun x => cen4Pt a b c d x

@[expose] noncomputable def fconj6126 : Bool :=
  strictB (RP 2) fun r => notB (allN 16 fun a =>
    notB (notInK 16 CertificateChecks.KernelLC.L34SyF.T
      (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) r (CertificateChecks.KernelLC.L34SyF.T a)) r)))

end CertificateChecks.KernelLC.L34FCent

end

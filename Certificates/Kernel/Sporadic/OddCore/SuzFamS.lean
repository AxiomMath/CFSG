module

public import Certificates.Kernel.Sporadic.OddCore.SuzFam
public import Certificates.Kernel.Sporadic.OddCore.SuzCert
public import Certificates.Kernel.Sporadic.Suz.Text2306
public import Certificates.Kernel.SporSch.Ru.RowsGen

public section

namespace CertificateChecks.KernelSpor.SuzFamD

open CFSG.KC.Enum CFSG.KS CFSG.KS.Row CertificateChecks.KernelSpor.Suz2306

@[expose] noncomputable def fe (d j : Nat) : Nat := pg 15 (mask 15) (FAM d) j

@[expose] noncomputable def ak (k x : Nat) : Nat := rg 15 (mask 15) SuzCertT.F (Nat.mul 715 k) x

@[expose] noncomputable def bK (k : Nat) : Nat := nIf(Nat.beq k 0, B0, B1)

@[expose] noncomputable def imgK (k d : Nat) : Bool :=
  strictB (pg 11 (mask 11) (bK k) d) (fun e => bAnd(Nat.blt e 1782,
  strictB (FAM d) (fun A => strictB (FAM e) (fun E =>
  strictB (PI (Nat.add (Nat.mul 2 d) k)) (fun P =>
    allN 2080 (fun j => strictB (fld(P, Nat.mul 12 j, mask 12)) (fun p =>
      bAnd(Nat.blt p 2080, Nat.beq (ak k (fld(A, Nat.mul 15 j, mask 15)))
        (fld(E, Nat.mul 15 p, mask 15))))))))))

@[expose] noncomputable def incK (d : Nat) : Bool :=
  strictB (FAM d) (fun A => bAnd(Nat.blt (fld(A, Nat.mul 15 2079, mask 15)) 22880,
    allN 2079 (fun j => Nat.blt (fld(A, Nat.mul 15 j, mask 15))
      (fld(A, Nat.mul 15 (Nat.succ j), mask 15)))))

@[expose] noncomputable def imgSl (k s : Nat) : Bool :=
  allBlk (Nat.mul 64 s) (fun d => bIf(Nat.blt d 1782, imgK k d, true)) 64

@[expose] noncomputable def incSl (s : Nat) : Bool := allBlk (Nat.mul 891 s) incK 891

end CertificateChecks.KernelSpor.SuzFamD

end

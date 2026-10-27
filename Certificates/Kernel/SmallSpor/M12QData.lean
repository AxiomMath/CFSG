module

public import Certificates.Kernel.SmallSpor.M12Data
public meta import Certificates.Data.ExitTwoM12
public meta import CFSG.Monster.B.Mathieu.Order
public meta import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelSmallSpor.M12Q

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12

meta def pk (g : Equiv.Perm (Fin 12)) : Nat :=
  CFSG.KS.RawGen.pack 4 (CFSG.Monster.B.Mathieu.imageList g).toArray

meta def eA (wd : List Int) : Equiv.Perm (Fin 12) := evalCodes [m12gA, m12gB] wd

meta def eB (wd : List Int) : Equiv.Perm (Fin 12) := evalCodes [m12gA, m12bp] wd

meta def wv : List Nat := [pk m12bp, pk m12bp⁻¹, pk (eA wG)]

meta def q0 : List Nat := (q8List (eA wI0) (eA wJ0)).map pk

meta def q1 : List Nat := (q8List (eA wI1) (eA wJ1)).map pk

meta def b0 : List Nat := (q8List (eB wI0) (eB wJ0)).map pk

meta def b1 : List Nat := (q8List (eB wI1) (eB wJ1)).map pk

meta def ri : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 12 4 CertificateChecks.KernelSmallSpor.M12.k1G).1
  let r := (CFSG.Monster.B.Mathieu.imageList (m12InvReps.getD 0 1)).toArray
  (List.range pts.size).filter fun i =>
    CFSG.KS.RawGen.comp 12 pts[i]! pts[i]! == r

meta def nri : List Nat := [ri.length]

end CertificateChecks.KernelSmallSpor.M12Q

end

#kss_natlist CertificateChecks.KernelSmallSpor.M12Q.WV CertificateChecks.KernelSmallSpor.M12Q.wv
#kss_natlist CertificateChecks.KernelSmallSpor.M12Q.Q0 CertificateChecks.KernelSmallSpor.M12Q.q0
#kss_natlist CertificateChecks.KernelSmallSpor.M12Q.Q1 CertificateChecks.KernelSmallSpor.M12Q.q1
#kss_natlist CertificateChecks.KernelSmallSpor.M12Q.B0 CertificateChecks.KernelSmallSpor.M12Q.b0
#kss_natlist CertificateChecks.KernelSmallSpor.M12Q.B1 CertificateChecks.KernelSmallSpor.M12Q.b1
#kss_natlist CertificateChecks.KernelSmallSpor.M12Q.RI CertificateChecks.KernelSmallSpor.M12Q.ri
#kss_natlist CertificateChecks.KernelSmallSpor.M12Q.NR CertificateChecks.KernelSmallSpor.M12Q.nri

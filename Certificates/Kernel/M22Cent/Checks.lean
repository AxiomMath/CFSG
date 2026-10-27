module

public import Certificates.Data.Kernel.M22Cent.Defs

public section

namespace CertificateChecks.KernelM22Cent

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  Certificates.Kernel.M22Cent

theorem centXs_eq : centXs = xsL := by
  decide +kernel

theorem conj_ok : ((List.finRange 4).all fun k => (List.finRange 22).all fun j =>
    tf (centConj (xsL.getD k.val [])) (tf betaTab j) == tf betaTab (xf k.val j)) = true := by
  decide +kernel

theorem beta_inv : ((List.finRange 22).all fun j => tf betaTab (tf betaTab j) == j) = true := by
  decide +kernel

theorem xf_comm : ((List.finRange 4).all fun k => (List.finRange 4).all fun l =>
    (List.finRange 22).all fun j => xf k.val (xf l.val j) == xf l.val (xf k.val j)) = true := by
  decide +kernel

theorem fe_inv : ((List.range 16).all fun e => (List.finRange 22).all fun j =>
    fe e (fe e j) == j) = true := by
  decide +kernel

theorem orbit_ok : ((List.finRange 22).all fun q =>
    !mv q || (List.range 16).any fun e => fe e 0 == q) = true := by
  decide +kernel

theorem mv_zero : mv 0 = true := by
  decide +kernel

theorem pres_ok : (((List.range 4).all fun k => presB (xf k)) && presB (tf betaTab)) = true := by
  decide +kernel

theorem wit_ok : ((List.finRange 22).all fun p =>
    mv p || witL.any fun w => w.1 == p && witB p w.2.1 w.2.2) = true := by
  decide +kernel

end CertificateChecks.KernelM22Cent

module

public import Certificates.Kernel.SporSch.HN.T0Data
public import Certificates.Data.Kernel.SporSch.HNT0
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSporSch.HNT0

open CFSG.KD.HNT0 CFSG.KS.HNT0

theorem root : rootK AL DF DFO ZP 343 = true := by quickRfl

theorem dfo_end : Nat.beq (DFO 343) 7339 = true := by quickRfl

#kc_each CertificateChecks.KernelSporSch.HNT0 ch10509d (fun j => subK AL PR DF DFO ZP j) 0 343

theorem eb : ebK AL PR 687 ZP EB ZW = true := by quickRfl

theorem neg_root : Bool.not (rootK AL DF DFO ZP 342) = true := by quickRfl
theorem neg_sub : Bool.not (subK AL PR DF (fun j => Nat.add (DFO j) (Nat.beq j 1).toNat) ZP 0) =
    true := by quickRfl
theorem neg_kid : Bool.not (subK (fun a => Nat.land (AL a) (Nat.sub (Nat.shiftLeft 1 1024) 1)) PR
    DF DFO ZP 0) = true := by quickRfl
theorem neg_zw : Bool.not (ebK AL PR 687 ZP EB [5, 12, 268]) = true := by quickRfl
theorem neg_eb : Bool.not (ebK AL PR 687 ZP [[0, 3, 29, 33, 33], [1, 2, 4, 14, 23],
    [5, 14, 31, 59, 82]] ZW) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNT0

end

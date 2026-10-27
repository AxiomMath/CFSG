module

public import Certificates.Data.Kernel.PermCent.U33CentQ
public import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.U33T

open CFSG.GH74.KGroups.U33

#kc_each centBlkQ 0 8

theorem centBlk0 : centBlk 0 = true := (centBlkQ_eq 0).symm.trans centBlkQ0
theorem centBlk1 : centBlk 1 = true := (centBlkQ_eq 1).symm.trans centBlkQ1
theorem centBlk2 : centBlk 2 = true := (centBlkQ_eq 2).symm.trans centBlkQ2
theorem centBlk3 : centBlk 3 = true := (centBlkQ_eq 3).symm.trans centBlkQ3
theorem centBlk4 : centBlk 4 = true := (centBlkQ_eq 4).symm.trans centBlkQ4
theorem centBlk5 : centBlk 5 = true := (centBlkQ_eq 5).symm.trans centBlkQ5
theorem centBlk6 : centBlk 6 = true := (centBlkQ_eq 6).symm.trans centBlkQ6
theorem centBlk7 : centBlk 7 = true := (centBlkQ_eq 7).symm.trans centBlkQ7

theorem len21110 : (elemsC QP).length ≤ 8 * 756 := by
  decide +kernel

theorem neg21110 : ((elemsC QP).all fun s => !decide (s * s = 1) || decide (s = 1) ||
    (coreC (centC (elemsC QP) s)).length == 17) = false := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.U33T

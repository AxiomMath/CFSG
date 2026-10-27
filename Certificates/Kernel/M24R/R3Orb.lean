module

public import Certificates.Data.Kernel.M24R.R3Orb
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option profiler true
set_option profiler.threshold 200

#kc_repo #kc_ktree CFSG.KC.M24R3 OR
  "Certificates/Kernel/M24R/data/orb.bin" 66 4 1330560 9119718571786199805

namespace CFSG.KC.M24R3

theorem ch21194_orb0 : orbBlk OR (nat_lit 0) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb1 : orbBlk OR (nat_lit 504) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb2 : orbBlk OR (nat_lit 1008) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb3 : orbBlk OR (nat_lit 1512) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb4 : orbBlk OR (nat_lit 2016) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb5 : orbBlk OR (nat_lit 2520) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb6 : orbBlk OR (nat_lit 3024) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb7 : orbBlk OR (nat_lit 3528) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb8 : orbBlk OR (nat_lit 4032) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb9 : orbBlk OR (nat_lit 4536) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb10 : orbBlk OR (nat_lit 5040) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb11 : orbBlk OR (nat_lit 5544) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb12 : orbBlk OR (nat_lit 6048) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb13 : orbBlk OR (nat_lit 6552) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb14 : orbBlk OR (nat_lit 7056) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb15 : orbBlk OR (nat_lit 7560) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb16 : orbBlk OR (nat_lit 8064) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb17 : orbBlk OR (nat_lit 8568) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb18 : orbBlk OR (nat_lit 9072) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb19 : orbBlk OR (nat_lit 9576) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb20 : orbBlk OR (nat_lit 10080) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb21 : orbBlk OR (nat_lit 10584) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb22 : orbBlk OR (nat_lit 11088) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb23 : orbBlk OR (nat_lit 11592) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb24 : orbBlk OR (nat_lit 12096) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb25 : orbBlk OR (nat_lit 12600) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb26 : orbBlk OR (nat_lit 13104) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb27 : orbBlk OR (nat_lit 13608) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb28 : orbBlk OR (nat_lit 14112) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb29 : orbBlk OR (nat_lit 14616) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb30 : orbBlk OR (nat_lit 15120) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb31 : orbBlk OR (nat_lit 15624) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb32 : orbBlk OR (nat_lit 16128) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb33 : orbBlk OR (nat_lit 16632) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb34 : orbBlk OR (nat_lit 17136) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb35 : orbBlk OR (nat_lit 17640) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb36 : orbBlk OR (nat_lit 18144) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb37 : orbBlk OR (nat_lit 18648) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb38 : orbBlk OR (nat_lit 19152) (nat_lit 504) = true := by decide +kernel

theorem ch21194_orb39 : orbBlk OR (nat_lit 19656) (nat_lit 504) = true := by decide +kernel

#kc_forall_chunks ch21194_orbAll (fun k => orbBlk OR (504 * k) 504 = true) 40
  CFSG.KC.M24R3.ch21194_orb 1

theorem ch21194_orb_neg_swap :
    orbBlk (fun n => Bool.rec (OR n) (OR 6) (Nat.beq n 5)) (nat_lit 0) (nat_lit 8) = false := by
  decide +kernel

theorem ch21194_orb_neg_key : orbOK (fun n => Nat.add (OR n) (nat_lit 1099511627776)) (nat_lit 1) =
    false := by
  decide +kernel

theorem ch21194_orb_neg_gen : orbOK (fun n => Nat.xor (OR n) (nat_lit 1073741824)) (nat_lit 1) =
    false := by
  decide +kernel

end CFSG.KC.M24R3

end

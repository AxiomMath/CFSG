module

public import Certificates.Data.Kernel.Hall82K.Bridge

set_option maxRecDepth 100000

public section

namespace CFSG.KC.Hall82K

open CFSG.CGT.Hall82

theorem ch840004br_s40 : zipArrK s40K hallS40Arr = true := by decide +kernel

theorem ch840004br_rm : zipArrK rmK hallRMArr = true := by decide +kernel

theorem ch840004br_gens : zipArrK c5GensK hallStMGensArr = true := by decide +kernel

theorem ch840004br_q0 : q0BridgeK = true := by decide +kernel

theorem ch840004br_w : wBridgeK = true := by decide +kernel

theorem ch840004br_qt : qtBridgeK = true := by decide +kernel

theorem ch840004br_idx : idxBridgeK = true := by decide +kernel

theorem ch840004br_u0 : u0K = hallU0List := rfl

theorem ch840004br_k : kK = hallKList := rfl

theorem ch840004br_neg :
    zipArrK rmK.tail hallRMArr.tail = true ∧ zipArrK rmK hallRMArr.tail = false ∧
      zipArrK rmK.tail hallRMArr = false := by
  decide +kernel

end CFSG.KC.Hall82K

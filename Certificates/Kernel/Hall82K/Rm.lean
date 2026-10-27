module

public import Certificates.Kernel.Hall82K.RmData
public import Certificates.Kernel.Hall82K.EnumData
public import CFSG.CGT.Hall82.DModelData

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Hall82R

open CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.Hall82K CFSG.KD.Hall82E CFSG.CGT.Hall82

theorem ch840003rmK : P.allN 8 (fun e => Nat.beq (rmC RMP e) (rmK.getD e 0)) = true := by
  decide +kernel

theorem ch840003u0 : P.allN 64 (fun v => beqB (memL v hallU0List) (inUK v)) = true := by
  decide +kernel

theorem ch840003basic : rmBasicK RMP = true := by decide +kernel

theorem ch840003mem : rmMemK EM RMI RMP = true := by decide +kernel

theorem ch840003notLe : rmNotLeK EL RMP = true := by decide +kernel

theorem ch840003nv : P.allN 2160 (nvAtK EM EL RMP NVW) = true := by decide +kernel

theorem ch840003sub : P.allN 256 (subsetAtK EL RMP SW) = true := by decide +kernel

theorem ch840003uInv : P.allN 2160 (uInvAtK EM) = true := by decide +kernel

theorem ch840003rmU : rmUK RMP = true := by decide +kernel

theorem ch840003fix : fixRmK RMP = true := by decide +kernel

theorem ch840003uMax : P.allN 64 (uMaxAtK EL UMW) = true := by decide +kernel

end CFSG.KD.Hall82R

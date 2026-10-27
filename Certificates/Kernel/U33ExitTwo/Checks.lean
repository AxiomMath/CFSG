module

public import Certificates.Data.Kernel.U33ExitTwo
public import Certificates.Kernel.U33ExitTwo.Data
public import CFSG.GH74.KGroups.U33Inputs

public section

namespace CFSG.KD.U33Exit

open CFSG.KC.U33Exit CFSG.GH74.KGroups.U33

theorem gens_ok : (repB (u33Gen.getD 0 0) pa && repB (u33Gen.getD 1 0) pb &&
    repB (u33Gen.getD 2 0) sg0 && repB u33T pu) = true := by
  decide +kernel

theorem ent_ok : u33C.all (entOK u33Gen u33T) = true := by
  decide +kernel

theorem inc_ok : incB 0 (u33C.map Prod.fst) = true := by
  decide +kernel

theorem len_ok : Nat.beq u33C.length 192 = true := by
  decide +kernel

theorem uniq_ok : uniqOK u33T u33C u33Qi u33Qo = true := by
  decide +kernel

theorem wit_ok : witOK u33Gen u33T u33W = true := by
  decide +kernel

end CFSG.KD.U33Exit

end

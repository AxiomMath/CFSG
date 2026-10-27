module

public import Certificates.Data.Kernel.F4Syl3Model
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.F4Syl3 "Certificates/Kernel/F4Syl3/data/model.json.gz" 5611
  9714946842021026086 (reps : List Nat) (tgt : List Nat) (cover : List (Nat × Nat))
  (lineA : List Nat) (lineB : List Nat)

namespace CFSG.KD.F4Syl3

open CFSG.KC.F4Syl3

theorem model_ok : modelChk = true := by decide +kernel

theorem cover_ok : coverChk reps tgt cover = true := by decide +kernel

theorem line_ok : lineChk tgt cover lineA lineB = true := by decide +kernel

end CFSG.KD.F4Syl3

end

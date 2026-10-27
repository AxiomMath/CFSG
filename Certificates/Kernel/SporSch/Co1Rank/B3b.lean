module

public import Certificates.Data.Kernel.SporSch.Co1RankCand
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.Co1RankB3b "Certificates/Kernel/SporSch/Co1Rank/data/b3b.json.gz"
  2095387 5604931406187757160
  (d : Nat) (Kt : Nat) (NCt : Nat) (PHt : Nat) (T2A : List (List Nat)) (nU : Nat) (UC : Nat)
  (reps : List (List Nat × Nat × List (Nat × Nat × List Nat × List Nat)))

namespace CFSG.KD.Co1RankB3b

open CFSG.KC.Co1RankCand

@[expose] noncomputable def dat : Dat := ⟨d, Kt, NCt, PHt, T2A, nU, UC, reps⟩

set_option profiler true in
theorem chk_ok : chkC dat = true := by decide +kernel

end CFSG.KD.Co1RankB3b

end

module

public import Certificates.Data.Kernel.SporSch.Co1RankRec
public import Certificates.Kernel.SporSch.Co1Rank.TabB
public import Certificates.Kernel.SporSch.Co1Rank.B1
public import Certificates.Kernel.SporSch.Co1Rank.B2
public import Certificates.Kernel.SporSch.Co1Rank.B3a
public import Certificates.Kernel.SporSch.Co1Rank.B3b
public import Certificates.Kernel.SporSch.Co1Rank.B4a
public import Certificates.Kernel.SporSch.Co1Rank.B4b
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.Co1RankRecB "Certificates/Kernel/SporSch/Co1Rank/data/recb.json.gz"
  140241 3136977343690526440
  (S : List (List (List (List Nat)))) (X : List (List (List (Nat × Nat))))

namespace CFSG.KD.Co1RankRecB

open CFSG.KC.Co1RankRec

@[expose] noncomputable def dat : Dat := ⟨S, X⟩

@[expose] noncomputable def repsR : List Reps :=
  [Co1RankB1.reps, Co1RankB2.reps, List.append Co1RankB3a.reps Co1RankB3b.reps,
    List.append Co1RankB4a.reps Co1RankB4b.reps]

set_option profiler true in
theorem chkR_ok : chkR Co1RankTabB.dat repsR dat = true := by decide +kernel

set_option profiler true in
theorem sameTab_ok :
    List.all [Co1RankB1.dat, Co1RankB2.dat, Co1RankB3a.dat, Co1RankB3b.dat, Co1RankB4a.dat,
      Co1RankB4b.dat] (fun C => sameTab C Co1RankTabB.dat) = true := by decide +kernel

end CFSG.KD.Co1RankRecB

end

module

public import Certificates.Data.Kernel.SporSch.Co1RankRec
public import Certificates.Kernel.SporSch.Co1Rank.TabC
public import Certificates.Kernel.SporSch.Co1Rank.C1
public import Certificates.Kernel.SporSch.Co1Rank.C2
public import Certificates.Kernel.SporSch.Co1Rank.C3a
public import Certificates.Kernel.SporSch.Co1Rank.C3b
public import Certificates.Kernel.SporSch.Co1Rank.C3c
public import Certificates.Kernel.SporSch.Co1Rank.C4
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.Co1RankRecC "Certificates/Kernel/SporSch/Co1Rank/data/recc.json.gz"
  51299 15414439045466986083
  (S : List (List (List (List Nat)))) (X : List (List (List (Nat × Nat))))

namespace CFSG.KD.Co1RankRecC

open CFSG.KC.Co1RankRec

@[expose] noncomputable def dat : Dat := ⟨S, X⟩

@[expose] noncomputable def repsR : List Reps :=
  [Co1RankC1.reps, Co1RankC2.reps,
    List.append Co1RankC3a.reps (List.append Co1RankC3b.reps Co1RankC3c.reps), Co1RankC4.reps]

set_option profiler true in
theorem chkR_ok : chkR Co1RankTabC.dat repsR dat = true := by decide +kernel

set_option profiler true in
theorem sameTab_ok :
    List.all [Co1RankC1.dat, Co1RankC2.dat, Co1RankC3a.dat, Co1RankC3b.dat, Co1RankC3c.dat,
      Co1RankC4.dat] (fun C => sameTab C Co1RankTabC.dat) = true := by decide +kernel

end CFSG.KD.Co1RankRecC

end

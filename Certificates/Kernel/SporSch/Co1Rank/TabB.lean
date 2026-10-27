module

public import Certificates.Data.Kernel.SporSch.Co1RankTab
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.Co1RankTabB "Certificates/Kernel/SporSch/Co1Rank/data/tabb.json.gz"
  158764 1071953836562215594
  (d : Nat) (Kt : Nat) (NCt : Nat) (PHt : Nat) (nG : Nat) (REL : Nat) (CW : List Nat) (G : List Nat)
  (BS : List Nat) (WL : List Nat) (cM : Nat) (T2A : List (List Nat)) (nU : Nat) (UC : Nat)
  (P : List Nat)

namespace CFSG.KD.Co1RankTabB

open CFSG.KC.Co1RankTab

@[expose] noncomputable def dat : Dat := ⟨d, Kt, NCt, PHt, nG, REL, CW, G, BS, WL, cM, T2A, nU, UC, P⟩

set_option profiler true in
theorem chkT_ok : chkT dat = true := by decide +kernel

set_option profiler true in
theorem chkM_ok : chkM dat = true := by decide +kernel

set_option profiler true in
theorem chkP_ok : chkP dat = true := by decide +kernel

end CFSG.KD.Co1RankTabB

end

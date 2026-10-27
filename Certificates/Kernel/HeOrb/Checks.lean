module

public import Certificates.Kernel.HeOrb.Data
public import Certificates.Data.Kernel.HeOrbK
import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

public section

namespace CFSG.KD.HeOrb

open CFSG.KC.HeOrb CFSG.KC.Enum

@[expose] noncomputable def famB (c : Nat) : Bool :=
  allN (nat_lit 9) fun t => blkK PT AL BE TA TB (Nat.add (Nat.mul (nat_lit 9) c) t)

theorem mat_ok : matK SA.chars SB.chars TA TB = true := by quickRfl

theorem hd_ok : hdK PT AL BE PA LA R = true := by quickRfl

theorem srt_ok : srtK PT SO = true := by quickRfl

end CFSG.KD.HeOrb

#kss_each CFSG.KD.HeOrb.B CFSG.KD.HeOrb.famB 29

end

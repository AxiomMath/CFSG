module

public import Certificates.Data.Kernel.SporSch.Co1RankBnd
public import Certificates.Kernel.SporSch.Co1Rank.TabB
public import Certificates.Kernel.SporSch.Co1Rank.B1
public import Certificates.Kernel.SporSch.Co1Rank.B2
public import Certificates.Kernel.SporSch.Co1Rank.B3a
public import Certificates.Kernel.SporSch.Co1Rank.B3b
public import Certificates.Kernel.SporSch.Co1Rank.B4a
public import Certificates.Kernel.SporSch.Co1Rank.B4b

public section

namespace CFSG.KD.Co1RankBndB

open CFSG.KC.Co1RankBnd

set_option profiler true in
theorem bnd_ok :
    List.all [Co1RankB1.dat, Co1RankB2.dat, Co1RankB3a.dat, Co1RankB3b.dat, Co1RankB4a.dat,
      Co1RankB4b.dat] bndOK = true := by decide +kernel

set_option profiler true in
theorem tab_ok : tabOK Co1RankTabB.dat = true := by decide +kernel

end CFSG.KD.Co1RankBndB

end

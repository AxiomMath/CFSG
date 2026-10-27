module

public import Certificates.Data.Kernel.SporSch.Co1RankBnd
public import Certificates.Kernel.SporSch.Co1Rank.TabC
public import Certificates.Kernel.SporSch.Co1Rank.C1
public import Certificates.Kernel.SporSch.Co1Rank.C2
public import Certificates.Kernel.SporSch.Co1Rank.C3a
public import Certificates.Kernel.SporSch.Co1Rank.C3b
public import Certificates.Kernel.SporSch.Co1Rank.C3c
public import Certificates.Kernel.SporSch.Co1Rank.C4

public section

namespace CFSG.KD.Co1RankBndC

open CFSG.KC.Co1RankBnd

set_option profiler true in
theorem bnd_ok :
    List.all [Co1RankC1.dat, Co1RankC2.dat, Co1RankC3a.dat, Co1RankC3b.dat, Co1RankC3c.dat,
      Co1RankC4.dat] bndOK = true := by decide +kernel

set_option profiler true in
theorem tab_ok : tabOK Co1RankTabC.dat = true := by decide +kernel

end CFSG.KD.Co1RankBndC

end

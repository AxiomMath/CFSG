module

public import Certificates.Data.Kernel.LyOmega.Chart
public import Certificates.Data.Kernel.LyOmega.Small
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.LyOm "Certificates/Kernel/Ly3085/Omega/data/consts_nats.bin.gz"
  92677 9712522558979226336 bCM7 bH7 bHV bHW bL7 bLV bLW bMASK7 bONE7 fCMF fHF fLF fONEF sCM7 sCMb
  sH7 sHb sL7 sLb sONE
#kc_repo #kc_nat_items_gz CFSG.KD.LyOm "Certificates/Kernel/Ly3085/Omega/data/base_nats.bin.gz"
  292150 9616506091962583303 T TI P[2] PI[2] Gt[2] FL UT1 PP1 BE1 UT2 PP2 BE2 UT3 PP3 BE3 UT4 PP4
  BE4 SS R0 Q0 R1 Q1 KQ0 KR0 KQ1 KR1 BI2 BI4 X3 WG1[] WG2[] WG3[] WG4[] WF3_0[] WF3_1[] WF4_0[]
  WF4_1[] WH2_0[] WH2_1[] WH3_0[] WH3_1[] WH3_2[] WH4_0[] WH4_1[] WH4_2[] WH4_3[] WYB[] WTA[] WTB[]
  PTA PTB PYB PTT TTt RTl

public section

namespace CFSG.KD.LyOm

@[expose] noncomputable def BC : CFSG.KC.LyOm.BConsts :=
  ⟨bL7, bH7, bCM7, bONE7, bMASK7, bLV, bHV, bLW, bHW, fLF, fHF, fCMF, fONEF⟩

@[expose] noncomputable def SC : CFSG.KC.LyOm.SConsts := ⟨sLb, sHb, sCMb, sL7, sH7, sCM7, sONE⟩

end CFSG.KD.LyOm

end

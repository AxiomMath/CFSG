module

public import Certificates.Data.Kernel.LyOmega.Tree
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.HarnessParts
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.LyO2 "Certificates/Kernel/Ly3085/O2/data/o2_nats.bin.gz"
  1728420 12329721834491796328 n P[2] PI[2] Lh CMh L7 CM7 ONE7 MASK7 Hh H7 MS[]
#kc_repo #kc_ktree_parts CFSG.KD.LyO2 KX 18648 4 282274776 4857288634790782197
  ("Certificates/Kernel/Ly3085/O2/data/o2_kx.bin.0" 70568694 1463536312665096746)
  ("Certificates/Kernel/Ly3085/O2/data/o2_kx.bin.1" 70568694 1554079376936185648)
  ("Certificates/Kernel/Ly3085/O2/data/o2_kx.bin.2" 70568694 12239124836274081904)
  ("Certificates/Kernel/Ly3085/O2/data/o2_kx.bin.3" 70568694 1234592067548548371)
#kc_repo #kc_ktree CFSG.KD.LyO2 PT "Certificates/Kernel/Ly3085/O2/data/o2_pt.bin" 168 4 2543016
  94917164074651023
#kc_repo #kc_ktree CFSG.KD.LyO2 SG "Certificates/Kernel/Ly3085/O2/data/o2_sg.bin" 160 4 2421920
  17735481383132448533

public section

namespace CFSG.KD.LyO2

@[expose] noncomputable def C : CFSG.KC.LyOm.Consts := ⟨Lh, Hh, CMh, L7, H7, CM7, ONE7, MASK7, MS⟩

end CFSG.KD.LyO2

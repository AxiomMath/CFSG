module

public import Certificates.Kernel.Ly3085.Omega.Data
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.LyF3 "Certificates/Kernel/Ly3085/Omega/data/f3_decls.items.gz" 74606 1052712889543086032
  n nc GTx[128] WCx[64] PIx[8] PJx[8]
#kc_repo #kc_ktree_gz CFSG.KD.LyF3 KX "Certificates/Kernel/Ly3085/Omega/data/f3_kx.bin.gz" 74592 4 74592 11179812766035823614
#kc_repo #kc_ktree_gz CFSG.KD.LyF3 PT "Certificates/Kernel/Ly3085/Omega/data/f3_pt.bin.gz" 256 4 256 624921549616694072
#kc_repo #kc_ktree_gz CFSG.KD.LyF3 WT "Certificates/Kernel/Ly3085/Omega/data/f3_wt.bin.gz" 4704 4 4704 16118303348804697796
#kc_repo #kc_ktree_gz CFSG.KD.LyF3 SG "Certificates/Kernel/Ly3085/Omega/data/f3_sg.bin.gz" 160 4 160 667160170035030864
#kc_select CFSG.KD.LyF3 GT GTx 128
#kc_select CFSG.KD.LyF3 WC WCx 64
#kc_select CFSG.KD.LyF3 PI PIx 8
#kc_select CFSG.KD.LyF3 PJ PJx 8

#kc_repo #kc_nat_items_gz CFSG.KD.LyF4 "Certificates/Kernel/Ly3085/Omega/data/f4_decls.items.gz" 74600 6116439324321878565
  n nc GTx[128] WCx[64] PIx[8] PJx[8]
#kc_repo #kc_ktree_gz CFSG.KD.LyF4 KX "Certificates/Kernel/Ly3085/Omega/data/f4_kx.bin.gz" 74592 4 895104 12328112170605263660
#kc_repo #kc_ktree_gz CFSG.KD.LyF4 PT "Certificates/Kernel/Ly3085/Omega/data/f4_pt.bin.gz" 256 4 3072 9370671005930097740
#kc_repo #kc_ktree_gz CFSG.KD.LyF4 WT "Certificates/Kernel/Ly3085/Omega/data/f4_wt.bin.gz" 4704 4 56448 10465892236902857584
#kc_repo #kc_ktree_gz CFSG.KD.LyF4 SG "Certificates/Kernel/Ly3085/Omega/data/f4_sg.bin.gz" 160 4 1920 1667333259254124454
#kc_select CFSG.KD.LyF4 GT GTx 128
#kc_select CFSG.KD.LyF4 WC WCx 64
#kc_select CFSG.KD.LyF4 PI PIx 8
#kc_select CFSG.KD.LyF4 PJ PJx 8

public section

namespace CFSG.KD.LyF3

@[expose] noncomputable def BC : CFSG.KC.LyOm.BConsts := CFSG.KD.LyOm.BC

end CFSG.KD.LyF3

namespace CFSG.KD.LyF4

@[expose] noncomputable def BC : CFSG.KC.LyOm.BConsts := CFSG.KD.LyOm.BC

end CFSG.KD.LyF4

end

module

public import Certificates.Kernel.Ly3085.Omega.Data
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.LyO1 "Certificates/Kernel/Ly3085/Omega/data/o1_decls.items.gz" 3767001 18330381247398312194
  n nc GTx[128] WCx[64] PIx[8] PJx[8] TAx[8] TBx[8] TTx[8] YBx[8]
#kc_repo #kc_ktree_gz CFSG.KD.LyO1 KX "Certificates/Kernel/Ly3085/Omega/data/o1_kx.bin.gz" 74592 4 22825152 17407677099295439635
#kc_repo #kc_ktree_gz CFSG.KD.LyO1 PT "Certificates/Kernel/Ly3085/Omega/data/o1_pt.bin.gz" 256 4 78336 12697926192285376437
#kc_repo #kc_ktree_gz CFSG.KD.LyO1 WT "Certificates/Kernel/Ly3085/Omega/data/o1_wt.bin.gz" 4704 4 1439424 17654966640198778048
#kc_repo #kc_ktree_gz CFSG.KD.LyO1 SG "Certificates/Kernel/Ly3085/Omega/data/o1_sg.bin.gz" 160 4 48960 17433183729840909776
#kc_select CFSG.KD.LyO1 GT GTx 128
#kc_select CFSG.KD.LyO1 WC WCx 64
#kc_select CFSG.KD.LyO1 PI PIx 8
#kc_select CFSG.KD.LyO1 PJ PJx 8
#kc_select CFSG.KD.LyO1 TA TAx 8
#kc_select CFSG.KD.LyO1 TB TBx 8
#kc_select CFSG.KD.LyO1 TT TTx 8
#kc_select CFSG.KD.LyO1 YB YBx 8

public section

namespace CFSG.KD.LyO1

@[expose] noncomputable def BC : CFSG.KC.LyOm.BConsts := CFSG.KD.LyOm.BC

end CFSG.KD.LyO1

end

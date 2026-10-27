module

public import Certificates.Kernel.Ly3085.Omega.Data
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.LyS3 "Certificates/Kernel/Ly3085/Omega/data/s3_decls.items.gz" 6780 16991795698392570004
  n nl m KS[] QS[]
#kc_repo #kc_ktree_gz CFSG.KD.LyS3 KX "Certificates/Kernel/Ly3085/Omega/data/s3_kx.bin.gz" 4312 4 27415696 9717507944143093264
#kc_repo #kc_ktree_gz CFSG.KD.LyS3 PT "Certificates/Kernel/Ly3085/Omega/data/s3_pt.bin.gz" 176 4 1119008 13715035028432645898
#kc_repo #kc_ktree_gz CFSG.KD.LyS3 SG "Certificates/Kernel/Ly3085/Omega/data/s3_sg.bin.gz" 160 4 1017280 2178282113863158882

#kc_repo #kc_nat_items_gz CFSG.KD.LyS4 "Certificates/Kernel/Ly3085/Omega/data/s4_decls.items.gz" 6778 17376696090605506112
  n nl m KS[] QS[]
#kc_repo #kc_ktree_gz CFSG.KD.LyS4 KX "Certificates/Kernel/Ly3085/Omega/data/s4_kx.bin.gz" 4312 4 526064 12952205195389582487
#kc_repo #kc_ktree_gz CFSG.KD.LyS4 PT "Certificates/Kernel/Ly3085/Omega/data/s4_pt.bin.gz" 176 4 21472 18417897406473118635
#kc_repo #kc_ktree_gz CFSG.KD.LyS4 SG "Certificates/Kernel/Ly3085/Omega/data/s4_sg.bin.gz" 160 4 19520 15199120295390280297

public section

@[expose] noncomputable def CFSG.KD.LyS3.SC : CFSG.KC.LyOm.SConsts := CFSG.KD.LyOm.SC
@[expose] noncomputable def CFSG.KD.LyS4.SC : CFSG.KC.LyOm.SConsts := CFSG.KD.LyOm.SC

end

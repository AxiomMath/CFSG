module

public import Certificates.Kernel.Ly3085.Omega.Data
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.LyH2 "Certificates/Kernel/Ly3085/Omega/data/h2_decls.items.gz" 6774 1556635563205746421
  n nl m KS[] QS[]
#kc_repo #kc_ktree_gz CFSG.KD.LyH2 KX "Certificates/Kernel/Ly3085/Omega/data/h2_kx.bin.gz" 4312 4 409640 8928299309766669677
#kc_repo #kc_ktree_gz CFSG.KD.LyH2 PT "Certificates/Kernel/Ly3085/Omega/data/h2_pt.bin.gz" 176 4 16720 1866966552149318290
#kc_repo #kc_ktree_gz CFSG.KD.LyH2 SG "Certificates/Kernel/Ly3085/Omega/data/h2_sg.bin.gz" 160 4 15200 7337657454394934210
#kc_repo #kc_ktree_gz CFSG.KD.LyH2 CT "Certificates/Kernel/Ly3085/Omega/data/h2_ct.bin.gz" 512 4 1024 6040818433698813054

#kc_repo #kc_nat_items_gz CFSG.KD.LyH3 "Certificates/Kernel/Ly3085/Omega/data/h3_decls.items.gz" 10154 18012357182799872923
  n nl m KS[] QS[]
#kc_repo #kc_ktree_gz CFSG.KD.LyH3 KX "Certificates/Kernel/Ly3085/Omega/data/h3_kx.bin.gz" 4312 4 194040 11511748807986049624
#kc_repo #kc_ktree_gz CFSG.KD.LyH3 PT "Certificates/Kernel/Ly3085/Omega/data/h3_pt.bin.gz" 176 4 7920 8807649639961575657
#kc_repo #kc_ktree_gz CFSG.KD.LyH3 SG "Certificates/Kernel/Ly3085/Omega/data/h3_sg.bin.gz" 160 4 7200 4709902155031623401
#kc_repo #kc_ktree_gz CFSG.KD.LyH3 CT "Certificates/Kernel/Ly3085/Omega/data/h3_ct.bin.gz" 512 4 512 12347528153647054162

#kc_repo #kc_nat_items_gz CFSG.KD.LyH4 "Certificates/Kernel/Ly3085/Omega/data/h4_decls.items.gz" 13530 15750656387162866947
  n nl m KS[] QS[]
#kc_repo #kc_ktree_gz CFSG.KD.LyH4 KX "Certificates/Kernel/Ly3085/Omega/data/h4_kx.bin.gz" 4312 4 68992 12607118760418298996
#kc_repo #kc_ktree_gz CFSG.KD.LyH4 PT "Certificates/Kernel/Ly3085/Omega/data/h4_pt.bin.gz" 176 4 2816 5221756857460725599
#kc_repo #kc_ktree_gz CFSG.KD.LyH4 SG "Certificates/Kernel/Ly3085/Omega/data/h4_sg.bin.gz" 160 4 2560 7844397159500313169
#kc_repo #kc_ktree_gz CFSG.KD.LyH4 CT "Certificates/Kernel/Ly3085/Omega/data/h4_ct.bin.gz" 512 4 512 8697502547105242378

public section

@[expose] noncomputable def CFSG.KD.LyH2.SC : CFSG.KC.LyOm.SConsts := CFSG.KD.LyOm.SC
@[expose] noncomputable def CFSG.KD.LyH3.SC : CFSG.KC.LyOm.SConsts := CFSG.KD.LyOm.SC
@[expose] noncomputable def CFSG.KD.LyH4.SC : CFSG.KC.LyOm.SConsts := CFSG.KD.LyOm.SC

end

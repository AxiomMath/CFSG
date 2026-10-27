module

public import Certificates.Data.Kernel.O8.Pair
public import Certificates.Kernel.O8Pair.Data
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeSylowData
import CFSG.Certificates.Kernel.BabyMonster.Load

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8P

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KC.O8P CFSG.EvenSmallLie.OmegaEight

@[expose] noncomputable def GT0 : GTab := ⟨D.V, D.NR, D.GT, D.G1, D.G1I, D.G2, D.G2I⟩

@[expose] noncomputable def WT0 : WTab := ⟨GT0, D.NE, D.NS, D.NC, D.WM, D.WS, D.WC⟩

@[expose] noncomputable def ET0 : ETab := ⟨WT0, saCodes, yIdxT, D.IN, D.EI, D.ES, D.EC, D.WJ⟩

@[expose] noncomputable def slp : Nat → Bool := slpAt D.V D.A D.B

@[expose] noncomputable def chi : Nat → Bool := chiAt saParT saLabT D.CH

@[expose] noncomputable def scan : Nat → Bool := scanAt saCodes D.CH D.PO D.EI D.NO

@[expose] noncomputable def ent : Nat → Bool := entAt ET0

end CertificateChecks.KernelO8P

#bm_bool CertificateChecks.KernelO8P kNR (Nat.beq D.NR 14958)
#bm_bool CertificateChecks.KernelO8P kNO (Nat.beq D.NO 224)
#bm_bool CertificateChecks.KernelO8P kSlp_0 (CFSG.KC.Enum.allBlk 0 slp 2048)
#bm_bool CertificateChecks.KernelO8P kSlp_1 (CFSG.KC.Enum.allBlk 2048 slp 2048)
#bm_bool CertificateChecks.KernelO8P kSlp_2 (CFSG.KC.Enum.allBlk 4096 slp 2048)
#bm_bool CertificateChecks.KernelO8P kSlp_3 (CFSG.KC.Enum.allBlk 6144 slp 2048)
#bm_bool CertificateChecks.KernelO8P kSlp_4 (CFSG.KC.Enum.allBlk 8192 slp 2048)
#bm_bool CertificateChecks.KernelO8P kSlp_5 (CFSG.KC.Enum.allBlk 10240 slp 2048)
#bm_bool CertificateChecks.KernelO8P kSlp_6 (CFSG.KC.Enum.allBlk 12288 slp 2048)
#bm_bool CertificateChecks.KernelO8P kSlp_7 (CFSG.KC.Enum.allBlk 14336 slp 622)
#bm_bool CertificateChecks.KernelO8P kChi (CFSG.KC.Enum.allN 8192 chi)
#bm_bool CertificateChecks.KernelO8P kScan_0 (CFSG.KC.Enum.allBlk 0 scan 2048)
#bm_bool CertificateChecks.KernelO8P kScan_1 (CFSG.KC.Enum.allBlk 2048 scan 2048)
#bm_bool CertificateChecks.KernelO8P kScan_2 (CFSG.KC.Enum.allBlk 4096 scan 2048)
#bm_bool CertificateChecks.KernelO8P kScan_3 (CFSG.KC.Enum.allBlk 6144 scan 2048)
#bm_bool CertificateChecks.KernelO8P kEnt_0 (CFSG.KC.Enum.allBlk 0 ent 32)
#bm_bool CertificateChecks.KernelO8P kEnt_1 (CFSG.KC.Enum.allBlk 32 ent 32)
#bm_bool CertificateChecks.KernelO8P kEnt_2 (CFSG.KC.Enum.allBlk 64 ent 32)
#bm_bool CertificateChecks.KernelO8P kEnt_3 (CFSG.KC.Enum.allBlk 96 ent 32)
#bm_bool CertificateChecks.KernelO8P kEnt_4 (CFSG.KC.Enum.allBlk 128 ent 32)
#bm_bool CertificateChecks.KernelO8P kEnt_5 (CFSG.KC.Enum.allBlk 160 ent 32)
#bm_bool CertificateChecks.KernelO8P kEnt_6 (CFSG.KC.Enum.allBlk 192 ent 32)

end

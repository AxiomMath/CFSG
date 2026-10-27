module

public import Certificates.Data.Kernel.SlpClsPc
public import Certificates.Data.Kernel.LyS0.Check
public import Certificates.Kernel.SporSch.Ly.BSData
public import Certificates.Kernel.SporSch.Ly.FiveLanesData
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.LyFivePc "Certificates/Kernel/LyFivePc/data/classes.json.gz" 10207 3186925382534784011
    (prgX : List (Nat × Nat)) (rxX : Nat) (sgX : List Nat) (entX : List (List Nat))
    (lpX : List (Nat × Nat)) (abX : List Nat)
    (prgY : List (Nat × Nat)) (rxY : Nat) (sgY : List Nat) (entY : List (List Nat))
    (lpY : List (Nat × Nat)) (abY : List Nat)
    (rel : List (List Nat))

public section

namespace CFSG.KD.LyFivePc

@[expose] noncomputable def clsW (Xg : Nat) (prg : List (Nat × Nat)) (rx : Nat) (sg : List Nat)
    (rel ent : List (List Nat)) (lp : List (Nat × Nat)) (ab : List Nat) : Bool :=
  CFSG.KC.SlpPc.clsPc CFSG.KD.LyS0.mul CFSG.KD.OrdLy.ONE CertificateChecks.KernelSporSch.LyBS.A
    CertificateChecks.KernelSporSch.LyBS.B Xg prg rx sg rel ent lp ab

@[expose] noncomputable def XX : Nat := CertificateChecks.KernelSporSch.LyFL.D.XX

@[expose] noncomputable def YY : Nat :=
  CFSG.KD.LyS0.mul CertificateChecks.KernelSporSch.LyFL.D.V0
    CertificateChecks.KernelSporSch.LyFL.D.V1

end CFSG.KD.LyFivePc

end

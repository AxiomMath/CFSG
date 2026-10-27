module

public import Certificates.Kernel.SporSch.Co2S.GenSetReplaySplit
public import Certificates.Kernel.SporSch.Co2M.Local
public import Certificates.Data.Kernel.SporSch.Co2SFix
public import Certificates.Data.Kernel.SporSch.SetReplay
public import CFSG.Sporadic.Co2Schreier.OrbitCheck
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.Kernel.SporSch.Co2SFix
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_setreplay_data CertificateChecks.KernelSporSch.Co2OZ 2300 12 CFSG.Sporadic.Co2Schreier.aArrs
  CFSG.KS.SporSch.Co2SFix.co2IzNat 56925 4096 64 1

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.SporSch CFSG.KS.SporSch.Co2SFix

@[expose] noncomputable def OZX : Nat → Nat := rowGet Co2OZ.XT (nat_lit 3436)

@[expose] noncomputable def OZS : Nat → Nat := rowGet Co2OZ.ST (nat_lit 20)

@[expose] noncomputable def OZSI : Nat → Nat := rowGet Co2OZ.SIT (nat_lit 20)

theorem oz_c : Co2OZ.c = 56925 := rfl

theorem oz_rx : Co2OZ.rx = 3436 := rfl

theorem gens_ok : allN 2 (fun k => Nat.beq (Co2OZ.G k) (AP k)) = true := by quickRfl

theorem start_ok : startK 12 284 (OZX 0) co2IzNat = true := by quickRfl

theorem fix_ok : ((List.range 2300).filter (fun p => Nat.beq (vmK (VG (PV 0) p) zP.1) (VG (PV 0) p))
    == co2IzNat) = true := by
  decide +kernel

end CertificateChecks.KernelSporSch.Co2M

end

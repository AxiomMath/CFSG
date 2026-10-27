module

public import Certificates.Kernel.MonsterB.Chain3025
public import Certificates.Kernel.MonsterB.Co2Perms
public import Certificates.Kernel.SporSch.OrbWitGen
public import CFSG.Certificates.Kernel.MonsterB.Co2StabSound
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import Mathlib.GroupTheory.Schreier

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMonB.Co2S CFSG.Monster.B.Co2.Native.chainStrongHex
#kmisc_hexflat CertificateChecks.KernelMonB.Co2S CFSG.Monster.B.Co2.Native.chainStrongHex 3 2300 12 20
#ks_chars CertificateChecks.KernelMonB.Co2O CFSG.Monster.B.Co2.Native.chainOrbitsHex
#kmisc_hexflat CertificateChecks.KernelMonB.Co2O CFSG.Monster.B.Co2.Native.chainOrbitsHex 3 2300 12 1

namespace CertificateChecks.Chain3025

meta def stabGensM : Array (Array Nat) := CFSG.Monster.B.Co2.Native.stabGens ()

meta def orbsM : Array (Array Nat) := CFSG.Monster.B.Co2.Native.chainOrbits ()

end CertificateChecks.Chain3025

#ks_orbwit CertificateChecks.Chain3025.Co2W 2300 12 CertificateChecks.Chain3025.stabGensM
  CertificateChecks.Chain3025.orbsM

public section

namespace CertificateChecks.Chain3025

open CFSG.KS.Raw CFSG.KC.Enum CFSG.KS.Co2Stab

theorem strong_ok : allN 20 (fun j => Nat.beq (Co2M.S j) (KernelMonB.Co2S.F j)) = true := by
  quickRfl

theorem pair_ok : allN 2 (fun j => Nat.beq (KernelMonB.Co2Q.F j) (Co2M.S j)) = true := by quickRfl

theorem base_ok : allN 10 (fun t =>
    Nat.beq (CFSG.Monster.B.Co2.Native.chainBase[t]!) (pg 12 (CFSG.KS.mask 12) Co2M.BP t)) = true := by
  decide +kernel

theorem sizes_ok : allN 10 (fun i =>
    Nat.beq (rcnt (Co2M.LR i)) (CFSG.Monster.B.Co2.Native.orbitLengths[i]!)) = true := by
  decide +kernel

theorem fix_ok : allN 20 (fun j =>
    Bool.rec (motive := fun _ => Bool) (!(Nat.ble 2 j)) (Nat.ble 2 j) (Nat.beq (at12 (Co2M.S j) 0) 0)) =
      true := by
  quickRfl

theorem first_ok : at12 (KernelMonB.Co2O.F 0) 0 = 0 := by decide +kernel

theorem stab_ok : stabK Co2M.S (KernelMonB.Co2O.F 0) Co2W.OPI Co2W.WP Co2W.WG Co2W.WD = true := by
  quickRfl

end CertificateChecks.Chain3025

end

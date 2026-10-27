module

public import Certificates.Kernel.J4Ov.C4207
public import Certificates.Kernel.J4Ov.Defs4206
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Ov

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4Ov CFSG.Sporadic.J4.Native CertificateChecks.KernelJ4Q
  CFSG.Quasithin.J4Ov

@[expose] noncomputable def excChk4206 (Z Zi m : Nat) : Bool :=
  andB (canonJ pad Zi) (andB (Nat.beq (mulJ c rm Z Zi) one) (andB (Nat.blt m 2048)
    (Nat.beq (mulJ c rm (mulJ c rm Z (etaK c rm one Us 1131)) Zi) (etaK c rm one Us m))))

@[expose] noncomputable def exc4206K (i : Nat) : Bool :=
  orB (notB (rep4207 i).exc)
    (strictB (z4207 i) fun Z => strictB (zi4207 i) fun Zi => excChk4206 Z Zi (rep4207 i).c)

theorem exc4206_ok : allR 49 exc4206K = true := by quickRfl

theorem ls4206_ok : eqLK LS (repData.map RepEntry.l) = true := by quickRfl

theorem kp4206_ok : andB (Nat.beq KP.length 2) (andB (eqLK (KP.getD 0 []) (CFSG.Sporadic.J4.QT2.repPaths.getD 5 []))
    (eqLK (KP.getD 1 []) (CFSG.Sporadic.J4.QT2.repPaths.getD 6 []))) = true := by quickRfl

theorem r0_4206_ok : Nat.beq R0 (v2N CFSG.Sporadic.J4.Native.rootV) = true := by quickRfl

theorem w4206_ok : (W.map (List.map Int.ofNat) == rx4207) = true := by quickRfl

theorem wl4206_ok : allR 49 (fun t => (W.getD t []).all fun l => andB (Nat.ble 1 l) (Nat.ble l 3)) =
    true := by quickRfl

end CertificateChecks.KernelJ4Ov

end

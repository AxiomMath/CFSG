module

public import Certificates.Kernel.TwoF4Loc.Data
public import Certificates.Kernel.TwoF4Lie.Data
public import Certificates.Data.Kernel.TwoF4LocK
public import Certificates.Data.TwoF4LocData
public import Certificates.Kernel.SporSch.Tits.Action2262
public import Certificates.Kernel.SporSch.Tits.Common
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTwoF4Loc

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TwoF4LocK CFSG.KD.TwoF4Loc CFSG.TwoF4Loc
  CertificateChecks.KernelSporSch.TitsAction CertificateChecks.KernelSporSch

@[expose] noncomputable def F (h : Nat) : Nat := CertificateChecks.KernelMisc.TitsText.F h

@[expose] noncomputable def FI (h : Nat) : Nat := CFSG.KD.TwoF4Lie.TGI h

theorem base : (wordIs F FI CFSG.TwoF4Lie.tWord (TT 0) && wordIs F FI CFSG.TwoF4Lie.cWord (TC 0) &&
    wordIs F FI locQWord (TQ 0) &&
    Nat.beq (mul (mul (TC 0) TitsZ) (mul (TC 0) (TC 0))) (TZ 0) &&
    Nat.beq (mul (mul (mul (TC 0) (TC 0)) TitsZ) (TC 0)) (TZ 1) && cn (TZ 0) && cn (TZ 1) &&
    lineK lpK (TC 0) && vK TitsZ (TZ 0) (TZ 1) && qK (TT 0) TitsZ (TZ 0) (TQ 0) &&
    collK lpK (TT 0) && (colK lpK).all (fun x => cl.contains x) &&
    cl.all (fun x => (colK lpK).contains x) && fixL (TT 0) == fx && fx.length == 27) = true := by
  quickRfl

theorem words : wordsK F FI TW TWI cws = true := by quickRfl

theorem chains : locChains = ch.map (fun r => r.map fun e => (e.1, cws.getD e.2 "")) := by
  decide +kernel

theorem chainIdx : (ch.length == 27 && ch.all fun r => r.all fun e => e.2 < cws.length) = true := by
  decide +kernel

theorem rows : allN 27 (fun k => rowK F FI lpK TW TWI cl TitsZ (TT 0) (TZ 0) (TZ 1) (TM k) (TMI k)
    (fx.getD k 0) (locWords.getD k "") (ch.getD k [])) = true := by quickRfl

end CertificateChecks.KernelTwoF4Loc

end

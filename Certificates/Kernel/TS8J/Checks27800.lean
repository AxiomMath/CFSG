module

public import Certificates.Data.Kernel.TS8JK
public import Certificates.Kernel.Multipliers.U43BChain
public import Certificates.Kernel.U43Rho.Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
meta import Certificates.Kernel.Misc.PackJson
import Certificates.Kernel.Misc.PackJson

set_option maxRecDepth 400000

public section

#kc_repo #kmisc_json_pack CFSG.KD.TS8J "Certificates/Kernel/TS8J/data/jt.json.gz" 1062959
  16771013148907347095 (el E 10) (gn G 10) (mt M 8) (rp RP 8) (pa PA 8) (la LA 8) (so SO 8)
  (si SI 8) (iv IV 8)

end

#kc_repo #kc_json_gz CFSG.KD.TS8J "Certificates/Kernel/TS8J/data/js.json.gz" 2915
  9815829865046942859 (RT : List (Nat × List Nat)) (ZA : List (Nat × List Nat))
  (ZC : List (Nat × Nat)) (AC : List (List (Nat × Nat))) (GW : List (List Nat)) (CW : List Nat)
  (zc : Nat) (ac : Nat)

public section

namespace CFSG.KD.TS8J

open CFSG.KC.TS8JK CFSG.KC.TS8WrK

@[expose] noncomputable def LT (l : Nat) : Nat :=
  ifN (Nat.beq l 0) (CertificateChecks.KernelU43B.C.S 0)
    (ifN (Nat.beq l 1) (CertificateChecks.KernelU43B.C.S 1)
      (ifN (Nat.beq l 2) (CertificateChecks.KernelU43B.C.SI 0)
        (ifN (Nat.beq l 3) (CertificateChecks.KernelU43B.C.SI 1)
          (CertificateChecks.KernelU43Rho.RH 0))))

theorem ch27800gen : genOK LT G GW = true := by quickRfl

theorem ch27800cw : cwOK LT E CW zc ac = true := by quickRfl

theorem ch27800tree : treeOK E (RP 0) (PA 0) (LA 0) = true := by quickRfl

theorem ch27800iv : ivOK M (IV 0) = true := by quickRfl

theorem ch27800sort : sortOK E (SO 0) (SI 0) = true := by quickRfl

theorem ch27800rec0 : recR E G (RP 0) 0 16 = true := by quickRfl
theorem ch27800rec1 : recR E G (RP 0) 16 16 = true := by quickRfl
theorem ch27800rec2 : recR E G (RP 0) 32 16 = true := by quickRfl
theorem ch27800rec3 : recR E G (RP 0) 48 16 = true := by quickRfl
theorem ch27800rec4 : recR E G (RP 0) 64 16 = true := by quickRfl
theorem ch27800rec5 : recR E G (RP 0) 80 16 = true := by quickRfl
theorem ch27800rec6 : recR E G (RP 0) 96 16 = true := by quickRfl
theorem ch27800rec7 : recR E G (RP 0) 112 16 = true := by quickRfl
theorem ch27800rec8 : recR E G (RP 0) 128 16 = true := by quickRfl
theorem ch27800rec9 : recR E G (RP 0) 144 16 = true := by quickRfl
theorem ch27800rec10 : recR E G (RP 0) 160 16 = true := by quickRfl
theorem ch27800rec11 : recR E G (RP 0) 176 16 = true := by quickRfl
theorem ch27800rec12 : recR E G (RP 0) 192 16 = true := by quickRfl
theorem ch27800rec13 : recR E G (RP 0) 208 16 = true := by quickRfl
theorem ch27800rec14 : recR E G (RP 0) 224 16 = true := by quickRfl
theorem ch27800rec15 : recR E G (RP 0) 240 16 = true := by quickRfl

theorem ch27800mt0 : mtR M (RP 0) (PA 0) (LA 0) 0 32 = true := by quickRfl
theorem ch27800mt1 : mtR M (RP 0) (PA 0) (LA 0) 32 32 = true := by quickRfl
theorem ch27800mt2 : mtR M (RP 0) (PA 0) (LA 0) 64 32 = true := by quickRfl
theorem ch27800mt3 : mtR M (RP 0) (PA 0) (LA 0) 96 32 = true := by quickRfl
theorem ch27800mt4 : mtR M (RP 0) (PA 0) (LA 0) 128 32 = true := by quickRfl
theorem ch27800mt5 : mtR M (RP 0) (PA 0) (LA 0) 160 32 = true := by quickRfl
theorem ch27800mt6 : mtR M (RP 0) (PA 0) (LA 0) 192 32 = true := by quickRfl
theorem ch27800mt7 : mtR M (RP 0) (PA 0) (LA 0) 224 32 = true := by quickRfl

theorem ch27800rt : rtOK M RT = true := by quickRfl

theorem ch27800z : zOK M RT ZA ZC = true := by quickRfl

theorem ch27800za : zaGo M RT ZA AC = true := by quickRfl

theorem ch27800rows : rowsOK M RT zc ac ZA = true := by quickRfl

theorem neg27800gen : notB (genOK LT G ([0] :: GW.tail)) = true := by quickRfl

theorem neg27800cw : notB (cwOK LT E (0 :: CW) zc ac) = true := by quickRfl

theorem neg27800tree : notB (treeOK E (RP 0) (PA 0) (LA 0 + 256)) = true := by quickRfl

theorem neg27800rec : notB (recR E G (RP 0 + 1) 0 1) = true := by quickRfl

theorem neg27800mt : notB (mtR (fun a => M a + 256) (RP 0) (PA 0) (LA 0) 0 1) = true := by quickRfl

theorem neg27800iv : notB (ivOK M (IV 0 + 1)) = true := by quickRfl

theorem neg27800sort : notB (sortOK E (SO 0 + 1) (SI 0)) = true := by quickRfl

theorem neg27800z : notB (zOK M RT ZA (ZC.set 1 (4, 0))) = true := by quickRfl

theorem neg27800row : notB (rowsOK M RT 0 0 ZA) = true := by quickRfl

end CFSG.KD.TS8J

end

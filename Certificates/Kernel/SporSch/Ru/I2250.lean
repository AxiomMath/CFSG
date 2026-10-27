module

public import Certificates.Kernel.SporSch.Ru.I2250Data
public import Certificates.Kernel.SporSch.Ru.SData
public import Certificates.Kernel.SporSch.Ru.TreePL
public import Certificates.Kernel.SporSch.Ru.Wit
public import Certificates.Data.Kernel.SporSch.Ru2250K
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_natBin CertificateChecks.KernelSporSch.RuI ZJ "Certificates/Kernel/SporSch/Ru/data/zj.bin" 40960 17121555972902504756
#kc_repo #kc_natBin CertificateChecks.KernelSporSch.RuI CNT "Certificates/Kernel/SporSch/Ru/data/cnt2250.bin" 288 6128533084993583545

namespace CertificateChecks.KernelSporSch.RuI

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.Ru2250
  CFSG.Sporadic.RuSchreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def o0 : Nat := roff 4060 (4060 * 12) (RuSS.LR 0)

@[expose] noncomputable def o1 : Nat := roff 4060 (4060 * 12) (RuSS.LR 1)

@[expose] noncomputable def pInv (_ _ T0 T1 : Nat) : Bool := invK 4060 12 (mask 12) T0 T1

@[expose] noncomputable def pF92 (_ _ T0 T1 : Nat) : Bool :=
  bAnd(invK 4060 12 (mask 12) T0 T1, Nat.beq (fixK 4060 12 (mask 12) T0 T1) (nat_lit 92))

@[expose] noncomputable def pF0 (_ _ T0 T1 : Nat) : Bool :=
  bAnd(invK 4060 12 (mask 12) T0 T1, Nat.beq (fixK 4060 12 (mask 12) T0 T1) (nat_lit 0))

@[expose] noncomputable def pCm (i : Nat) (_ _ T0 T1 : Nat) : Bool := cmK 4060 12 (mask 12) T0 T1 (X i)

@[expose] noncomputable def pAll (a b T0 T1 : Nat) : Bool :=
  bAnd(prK 4060 12 (mask 12) T0 T1 (X 0) (X 1), bAnd(prK 4060 12 (mask 12) T0 T1 (X 0) (X 2),
    bAnd(prK 4060 12 (mask 12) T0 T1 (X 1) (X 2),
      bIf(pF92 a b T0 T1, zwK 4060 12 (mask 12) (nat_lit 593775) RuTree.plK A0 A1 Z T0 T1
        (fld(ZJ, Nat.mul (nat_lit 20) (Nat.add (Nat.mul (nat_lit 8) a) b), nat_lit 1048575)), true))))

@[expose] noncomputable def cnt (k f : Nat) : Nat :=
  pg 12 (mask 12) CNT (Nat.add (Nat.mul 6 k) f)

@[expose] noncomputable def cntOK (P : Nat → Nat → Nat → Nat → Bool) (f k : Nat) : Bool :=
  strictB o0 (fun o0 => strictB o1 (fun o1 =>
    Nat.beq (cntK RuSS.TR o0 o1 8 P (Nat.mul 64 k) 64) (cnt k f)))

@[expose] noncomputable def cntInv (k : Nat) : Bool := cntOK pInv 0 k

@[expose] noncomputable def cntF92 (k : Nat) : Bool := cntOK pF92 1 k

@[expose] noncomputable def cntF0 (k : Nat) : Bool := cntOK pF0 2 k

@[expose] noncomputable def cntX0 (k : Nat) : Bool := cntOK (pCm 0) 3 k

@[expose] noncomputable def cntX1 (k : Nat) : Bool := cntOK (pCm 1) 4 k

@[expose] noncomputable def cntX2 (k : Nat) : Bool := cntOK (pCm 2) 5 k

@[expose] noncomputable def allOK (k : Nat) : Bool :=
  strictB o0 (fun o0 => strictB o1 (fun o1 =>
    rowK RuSS.TR o0 o1 pAll (Nat.shiftRight k 1) (Nat.mul 4 (Nat.land k 1)) 4))

@[expose] noncomputable def allOKm (m i : Nat) : Bool := allOK (Nat.add (Nat.mul 512 m) i)

@[expose] noncomputable def tot (f : Nat) : Nat :=
  foldN 32 (fun k s => Nat.add s (cnt k f)) (nat_lit 0)

@[expose] noncomputable def xW (i : Nat) : Bool :=
  wordEqK 4060 12 (mask 12) (pidn 4060 12) SG SGI 4 (ruFusRec (i + 1)).1 (X i)

@[expose] noncomputable def hW (i : Nat) : Bool :=
  bAnd(compEqK 4060 12 (mask 12) (4060 * 12) (RuW.FG i) A0 (Q1 i),
  bAnd(compEqK 4060 12 (mask 12) (4060 * 12) (Q1 i) (RuW.FGI i) (Q2 i),
  bAnd(compEqK 4060 12 (mask 12) (4060 * 12) (Q2 i) (X i) (Q3 i),
  bAnd(powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) (Q3 i) ((ruFusD (i + 1) - 1) / 2)
    (Q4 i),
  bAnd(compEqK 4060 12 (mask 12) (4060 * 12) (Q4 i) (RuW.FG i) (H i),
  bAnd(compEqK 4060 12 (mask 12) (4060 * 12) (H i) A0 (HA i),
    compEqK 4060 12 (mask 12) (4060 * 12) (X i) (H i) (HA i)))))))

end CertificateChecks.KernelSporSch.RuI

namespace CertificateChecks.KernelSporSch.RuI

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.Ru2250
  CFSG.Sporadic.RuSchreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG

theorem xW0 : xW 0 = true := by quickRfl
theorem xW1 : xW 1 = true := by quickRfl
theorem xW2 : xW 2 = true := by quickRfl
theorem xC : allN 3 (fun i => canonK 4060 12 (mask 12) (4060 * 12) (X i)) = true := by quickRfl
theorem hW0 : hW 0 = true := by quickRfl
theorem hW1 : hW 1 = true := by quickRfl
theorem hW2 : hW 2 = true := by quickRfl
theorem fixA0 : fixedK 4060 12 (mask 12) A0 [] = true := by quickRfl
theorem zwA1 : zwK 4060 12 (mask 12) 593775 RuTree.plK A0 A1 Z A1 A1 268237 = true := by quickRfl
theorem sqA0 : sqIdK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) A0 = true := by quickRfl
theorem neA0 : neIdK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) A0 = true := by quickRfl
theorem pwA1 : bAnd(powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) A1 4 (pidn 4060 12),
    bAnd(powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) A1 2 R2,
      neIdK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) R2)) = true := by quickRfl
theorem p13 : bAnd(compEqK 4060 12 (mask 12) (4060 * 12) A0 A1 P01,
    powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) P01 13 (pidn 4060 12)) = true := by
  quickRfl
theorem pAB2 : bAnd(compEqK 4060 12 (mask 12) (4060 * 12) A0 R2 AB2,
    bAnd(powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) AB2 14 (pidn 4060 12),
    bAnd(powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) AB2 7 R7,
    bAnd(neIdK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) R7,
    bAnd(powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) AB2 2 R2B,
      neIdK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) R2B))))) = true := by quickRfl
theorem p29 : bAnd(compEqK 4060 12 (mask 12) (4060 * 12) P01 A0 P010,
    bAnd(compEqK 4060 12 (mask 12) (4060 * 12) P010 R2 Q29,
      powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) Q29 29 (pidn 4060 12))) = true := by
  quickRfl
theorem pNC : bAnd(compEqK 4060 12 (mask 12) (4060 * 12) A1 A0 P10,
    neK 4060 12 (mask 12) (4060 * 12) P01 P10) = true := by quickRfl
theorem cnt0 : Nat.beq (rcnt (RuSS.LR 0)) 2048 = true := by quickRfl
theorem cnt1 : Nat.beq (rcnt (RuSS.LR 1)) 8 = true := by quickRfl
theorem totOK : bAnd(Nat.beq (tot 0) 687, bAnd(Nat.beq (tot 1) 495, bAnd(Nat.beq (tot 2) 192,
    bAnd(Nat.beq (tot 3) 256, bAnd(Nat.beq (tot 4) 256, Nat.beq (tot 5) 256))))) = true := by
  quickRfl

theorem negCnt : (!Nat.beq (strictN o0 (fun o0 => strictN o1 (fun o1 =>
    cntK RuSS.TR o0 o1 8 pInv 0 8))) 4) = true := by quickRfl

theorem negZw : (!zwK 4060 12 (mask 12) 593775 RuTree.plK A0 A1 Z A1 A1 268238) = true := by
  quickRfl

theorem negId : bAnd(bIf(strictB o0 (fun o0 => strictB o1 (fun o1 =>
    invK 4060 12 (mask 12) (RuSS.TR o0) (RuSS.TR o1))), false, true),
    bIf(strictB o0 (fun o0 => strictB o1 (fun o1 =>
      prK 4060 12 (mask 12) (RuSS.TR o0) (RuSS.TR o1) (X 0) (X 0))), false, true)) = true := by
  quickRfl

theorem negXW : (!wordEqK 4060 12 (mask 12) (pidn 4060 12) SG SGI 4 (ruFusRec 1).1 (X 1)) =
    true := by quickRfl

end CertificateChecks.KernelSporSch.RuI

end

module

public import Certificates.Kernel.LocalComp.L34Un.Defs
public import Certificates.Kernel.LocalComp.L34SChk
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Un

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KS.PEnum CertificateChecks.KernelLC.L34X Certificates.L34Unitary
open CFSG.KLie.CT (notB)

theorem k_e0 : bAnd(gensK e0Gens 42 6 UE0.k UE0.G, bAnd(Nat.beq UE0.cnt 9,
    bAnd(penumHdK (pidn 42 6) UE0.cnt 9 UE0.T UE0.PL,
      penumSlK 42 6 (mask 6) (42 * 6) false UE0.G UE0.GI UE0.k UE0.cnt UE0.T UE0.PL UE0.POS
        UE0.SRT UE0.SRI 0 9))) = true := by
  quickRfl

theorem k_b : Nat.beq (L34S.T 19566) (UE0.G 1) = true := by
  quickRfl

theorem k_p0 : bAnd(Nat.beq UP0.k 10, bAnd(Nat.beq UP0.cnt 20160,
    bAnd(penumHdK (pidn 42 6) UP0.cnt 20160 UP0.T UP0.PL, bAnd(gensK (borelGens 0) 42 6 5 UP0.G,
      allN 5 (fun i => Nat.beq (UP0.G (Nat.add i 5))
        (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) R0 (UP0.G i)) R0)))))) = true := by
  quickRfl

theorem k_p1 : bAnd(Nat.beq UP1.k 10, bAnd(Nat.beq UP1.cnt 20160,
    bAnd(penumHdK (pidn 42 6) UP1.cnt 20160 UP1.T UP1.PL, bAnd(gensK (borelGens 1) 42 6 5 UP1.G,
      allN 5 (fun i => Nat.beq (UP1.G (Nat.add i 5))
        (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) R0 (UP1.G i)) R0)))))) = true := by
  quickRfl

theorem k_p2 : bAnd(Nat.beq UP2.k 10, bAnd(Nat.beq UP2.cnt 20160,
    bAnd(penumHdK (pidn 42 6) UP2.cnt 20160 UP2.T UP2.PL, bAnd(gensK (borelGens 2) 42 6 5 UP2.G,
      allN 5 (fun i => Nat.beq (UP2.G (Nat.add i 5))
        (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) R0 (UP2.G i)) R0)))))) = true := by
  quickRfl

theorem k_p3 : bAnd(Nat.beq UP3.k 10, bAnd(Nat.beq UP3.cnt 20160,
    bAnd(penumHdK (pidn 42 6) UP3.cnt 20160 UP3.T UP3.PL, bAnd(gensK (borelGens 3) 42 6 5 UP3.G,
      allN 5 (fun i => Nat.beq (UP3.G (Nat.add i 5))
        (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) R0 (UP3.G i)) R0)))))) = true := by
  quickRfl

theorem k_p4 : bAnd(Nat.beq UP4.k 10, bAnd(Nat.beq UP4.cnt 20160,
    bAnd(penumHdK (pidn 42 6) UP4.cnt 20160 UP4.T UP4.PL, bAnd(gensK (borelGens 4) 42 6 5 UP4.G,
      allN 5 (fun i => Nat.beq (UP4.G (Nat.add i 5))
        (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) R0 (UP4.G i)) R0)))))) = true := by
  quickRfl

theorem k_p5 : bAnd(Nat.beq UP5.k 10, bAnd(Nat.beq UP5.cnt 20160,
    bAnd(penumHdK (pidn 42 6) UP5.cnt 20160 UP5.T UP5.PL, bAnd(gensK (borelGens 5) 42 6 5 UP5.G,
      allN 5 (fun i => Nat.beq (UP5.G (Nat.add i 5))
        (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) R0 (UP5.G i)) R0)))))) = true := by
  quickRfl

theorem kNeg : notB (unK (pidn 42 6) (pidn 42 6) R0) = true := by
  quickRfl

end CertificateChecks.KernelLC.L34Un

end

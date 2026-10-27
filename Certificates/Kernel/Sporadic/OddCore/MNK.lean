module

public import Certificates.Kernel.Sporadic.OddCore.MNR1
public import Certificates.Kernel.Sporadic.OddCore.MNR2
public import Certificates.Kernel.Sporadic.OddCore.MNK1
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.MNd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 275 9 (mask 9) p q

@[expose] noncomputable def idK : Nat := pidn 275 9

@[expose] noncomputable def F (k : Nat) : Nat := McLCT.F k

@[expose] noncomputable def I (k : Nat) : Nat := MNI k

@[expose] noncomputable def S (j : Nat) : Nat := CertificateChecks.KernelCensus.McLC.S j

@[expose] noncomputable def SI (j : Nat) : Nat := CertificateChecks.KernelCensus.McLC.SI j

@[expose] noncomputable def sK (G : Nat) : Bool :=
  siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) CertificateChecks.KernelCensus.McLC.LR
    CertificateChecks.KernelCensus.McLC.TRI CertificateChecks.KernelCensus.McLC.BP 5 0 G

@[expose] noncomputable def involK (s : Nat) : Bool :=
  bAnd(Nat.beq (pc s s) idK, bIf(Nat.beq s idK, false, true))

@[expose] noncomputable def pw (e x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idK (fun _ acc => strictN acc (fun a => pc x a)) e

@[expose] noncomputable def isId (e x : Nat) : Bool := Nat.beq (pw e x) idK

@[expose] noncomputable def notId (e x : Nat) : Bool := bIf(Nat.beq (pw e x) idK, false, true)

@[expose] noncomputable def commK (x y : Nat) : Bool := Nat.beq (pc x y) (pc y x)

@[expose] noncomputable def atK (cnt : Nat) (T POS : Nat → Nat) (i y : Nat) : Bool :=
  bAnd(Nat.blt (r32 POS i) cnt, Nat.beq (T (r32 POS i)) y)

@[expose] noncomputable def cw (x h hi : Nat) : Nat := pc x (pc (pc h x) hi)

theorem k_base : bAnd(szOK 275 9, bAnd(canonK 275 9 (mask 9) (275 * 9) idK,
    bAnd(CFSG.KS.Prim.idK 275 9 (mask 9),
    bAnd(allN 30 (fun k => bAnd(canonK 275 9 (mask 9) (275 * 9) (F k),
      bAnd(canonK 275 9 (mask 9) (275 * 9) (I k), invEqK 275 9 (mask 9) (275 * 9) (F k) (I k)))),
    allN 2 (fun j => bAnd(canonK 275 9 (mask 9) (275 * 9) (S j),
      canonK 275 9 (mask 9) (275 * 9) (SI j))))))) = true := by
  quickRfl

theorem k_bindR :
    bAnd(allN 2 (fun j => bAnd(Nat.beq (MN.R1.G j) (S j), Nat.beq (MN.R1.GI j) (SI j))),
    bAnd(allN 2 (fun j => bAnd(Nat.beq (MN.R2.G j) (S j), Nat.beq (MN.R2.GI j) (SI j))),
    bAnd(Nat.beq MN.R1.R (F 4), Nat.beq MN.R2.R (F 17)))) = true := by
  quickRfl

theorem k_bindM :
    bAnd(allN 3 (fun j => bAnd(Nat.beq (MN.SY.G j) idK, Nat.beq (MN.SY.GI j) (F (Nat.succ j)))),
    bAnd(allN 2 (fun j => bAnd(Nat.beq (MN.K1.G j) idK, Nat.beq (MN.K1.GI j) (F (Nat.add 5 j)))),
    allN 4 (fun j => bAnd(Nat.beq (MN.K2.G j) idK, Nat.beq (MN.K2.GI j) (F (Nat.add 18 j)))))) =
    true := by
  quickRfl

@[expose] noncomputable def qbK (a k r : Nat) (G GI : Nat → Nat) (R : Nat) : Bool :=
  bAnd(allN k (fun j => bAnd(Nat.beq (G j) (F (Nat.add a j)), Nat.beq (GI j) (I (Nat.add a j)))),
    Nat.beq R (F r))

theorem k_bindQ : bAnd(qbK 5 2 7 MN.Q1a.G MN.Q1a.GI MN.Q1a.R,
    bAnd(qbK 5 2 9 MN.Q1b.G MN.Q1b.GI MN.Q1b.R,
    bAnd(qbK 5 2 11 MN.Q1c.G MN.Q1c.GI MN.Q1c.R, bAnd(qbK 5 2 13 MN.Q1d.G MN.Q1d.GI MN.Q1d.R,
    bAnd(qbK 5 2 15 MN.Q1e.G MN.Q1e.GI MN.Q1e.R, bAnd(qbK 18 4 22 MN.Q2a.G MN.Q2a.GI MN.Q2a.R,
    bAnd(qbK 18 4 24 MN.Q2b.G MN.Q2b.GI MN.Q2b.R, bAnd(qbK 18 4 26 MN.Q2c.G MN.Q2c.GI MN.Q2c.R,
    qbK 18 4 28 MN.Q2d.G MN.Q2d.GI MN.Q2d.R)))))))) = true := by
  quickRfl

theorem k_heads : bAnd(penumHdK MN.R1.R MN.R1.cnt 120000 MN.R1.T MN.R1.PL,
    bAnd(penumHdK MN.R2.R MN.R2.cnt 120000 MN.R2.T MN.R2.PL,
    bAnd(penumHdK idK MN.SY.cnt 120000 MN.SY.T MN.SY.PL,
    bAnd(penumHdK idK MN.K1.cnt 120000 MN.K1.T MN.K1.PL,
    bAnd(penumHdK idK MN.K2.cnt 120000 MN.K2.T MN.K2.PL,
    bAnd(penumHdK MN.Q1a.R MN.Q1a.cnt 120000 MN.Q1a.T MN.Q1a.PL,
    bAnd(penumHdK MN.Q1b.R MN.Q1b.cnt 120000 MN.Q1b.T MN.Q1b.PL,
    bAnd(penumHdK MN.Q1c.R MN.Q1c.cnt 120000 MN.Q1c.T MN.Q1c.PL,
    bAnd(penumHdK MN.Q1d.R MN.Q1d.cnt 120000 MN.Q1d.T MN.Q1d.PL,
    bAnd(penumHdK MN.Q1e.R MN.Q1e.cnt 120000 MN.Q1e.T MN.Q1e.PL,
    bAnd(penumHdK MN.Q2a.R MN.Q2a.cnt 120000 MN.Q2a.T MN.Q2a.PL,
    bAnd(penumHdK MN.Q2b.R MN.Q2b.cnt 120000 MN.Q2b.T MN.Q2b.PL,
    bAnd(penumHdK MN.Q2c.R MN.Q2c.cnt 120000 MN.Q2c.T MN.Q2c.PL,
    penumHdK MN.Q2d.R MN.Q2d.cnt 120000 MN.Q2d.T MN.Q2d.PL))))))))))))) = true := by
  quickRfl

theorem k_sizes : bAnd(Nat.beq MN.R1.cnt 22275, bAnd(Nat.beq MN.R2.cnt 113400,
    bAnd(Nat.beq MN.SY.cnt 256, bAnd(Nat.beq MN.K1.cnt 40320, bAnd(Nat.beq MN.K2.cnt 7920,
    bAnd(Nat.beq MN.Q1a.cnt 112, bAnd(Nat.beq MN.Q1b.cnt 2880, bAnd(Nat.beq MN.Q1c.cnt 2880,
    bAnd(Nat.beq MN.Q1d.cnt 1344, bAnd(Nat.beq MN.Q1e.cnt 1120, bAnd(Nat.beq MN.Q2a.cnt 1584,
    bAnd(Nat.beq MN.Q2b.cnt 720, bAnd(Nat.beq MN.Q2c.cnt 720, Nat.beq MN.Q2d.cnt 440))))))))))))) =
    true := by
  quickRfl

theorem k_u : bAnd(involK (F 0), bAnd(bIf(sK (F 0), false, true),
    allN 2 (fun j => bAnd(sK (S j), sK (pc (pc (F 0) (S j)) (I 0)))))) = true := by
  quickRfl

theorem k_syl : allN 3 (fun j => bIf(sK (F (Nat.succ j)), true, sK (pc (F (Nat.succ j)) (F 0)))) =
    true := by
  quickRfl

theorem k_reps : bAnd(involK (F 4), bAnd(involK (F 17), bAnd(sK (F 4),
    bAnd(bIf(sK (F 17), false, true), sK (pc (F 17) (F 0)))))) = true := by
  quickRfl

theorem k_cg : bAnd(allN 2 (fun j => bAnd(sK (F (Nat.add 5 j)), commK (F (Nat.add 5 j)) (F 4))),
    allN 4 (fun j => bAnd(sK (F (Nat.add 18 j)), commK (F (Nat.add 18 j)) (F 17)))) = true := by
  quickRfl

@[expose] noncomputable def oddK (r p t : Nat) : Bool :=
  bAnd(sK (F r), bAnd(commK (F r) (F t), bAnd(isId p (F r), notId 1 (F r))))

@[expose] noncomputable def conjK (r h t ord : Nat) : Bool :=
  bAnd(sK (F h), bAnd(commK (F h) (F t),
    (isId ord (cw (F r) (F h) (I h)) &&
      (CFSG.Sporadic.Schreier.Native.divParts ord).all fun e => notId e (cw (F r) (F h) (I h)))))

theorem k_odd : bAnd(oddK 7 3 4, bAnd(oddK 9 7 4, bAnd(oddK 11 7 4, bAnd(oddK 13 5 4,
    bAnd(oddK 15 3 4, bAnd(oddK 22 5 17, bAnd(oddK 24 11 17, bAnd(oddK 26 11 17,
    oddK 28 3 17)))))))) = true := by
  quickRfl

theorem k_conj : bAnd(conjK 7 8 4 4, bAnd(conjK 9 10 4 6, bAnd(conjK 11 12 4 14,
    bAnd(conjK 13 14 4 14, bAnd(conjK 15 16 4 10, bAnd(conjK 22 23 17 4, bAnd(conjK 24 25 17 8,
    bAnd(conjK 26 27 17 8, conjK 28 29 17 2)))))))) = true := by
  quickRfl

@[expose] noncomputable def ucovK (i t : Nat) : Bool :=
  strictB (pc (pc (F 0) (F t)) (I 0)) (fun y => bIf(atK MN.R1.cnt MN.R1.T MN.Uin1 i y, true,
    atK MN.R2.cnt MN.R2.T MN.Uin2 i y))

theorem k_ucov : bAnd(ucovK 0 4, ucovK 1 17) = true := by quickRfl

@[expose] noncomputable def scovK (i : Nat) : Bool :=
  strictB (MN.SY.T i) (fun y => bIf(involK y, bIf(atK MN.R1.cnt MN.R1.T MN.SYin1 i y, true,
    atK MN.R2.cnt MN.R2.T MN.SYin2 i y), true))

@[expose] noncomputable def sel3511 (y : Nat) : Bool :=
  strictB (pc y y) (fun s2 => strictB (pc y s2) (fun s3 => strictB (pc y s3) (fun s4 =>
  strictB (pc y s4) (fun s5 => strictB (pc y s5) (fun s6 => strictB (pc y s6) (fun s7 =>
  strictB (pc y s7) (fun s8 => strictB (pc y s8) (fun s9 => strictB (pc y s9) (fun s10 =>
  strictB (pc y s10) (fun s11 => bAnd(bIf(Nat.beq y idK, false, true),
    bIf(Nat.beq s3 idK, true, bIf(Nat.beq s5 idK, true, Nat.beq s11 idK)))))))))))))

@[expose] noncomputable def sel2K (i : Nat) : Bool :=
  strictB (MN.K2.T i) (fun y => bIf(sel3511 y, bIf(atK MN.Q2a.cnt MN.Q2a.T MN.K2in2a i y, true,
    bIf(atK MN.Q2b.cnt MN.Q2b.T MN.K2in2b i y, true, bIf(atK MN.Q2c.cnt MN.Q2c.T MN.K2in2c i y,
      true, atK MN.Q2d.cnt MN.Q2d.T MN.K2in2d i y))), true))

@[expose] noncomputable def sel357 (y : Nat) : Bool :=
  strictB (pc y y) (fun s2 => strictB (pc y s2) (fun s3 => strictB (pc y s3) (fun s4 =>
  strictB (pc y s4) (fun s5 => strictB (pc y s5) (fun s6 => strictB (pc y s6) (fun s7 =>
    bAnd(bIf(Nat.beq y idK, false, true),
      bIf(Nat.beq s3 idK, true, bIf(Nat.beq s5 idK, true, Nat.beq s7 idK)))))))))

@[expose] noncomputable def sel1K (i : Nat) : Bool :=
  strictB (MN.K1.T i) (fun y => bIf(sel357 y, bIf(atK MN.Q1a.cnt MN.Q1a.T MN.K1in1a i y, true,
    bIf(atK MN.Q1b.cnt MN.Q1b.T MN.K1in1b i y, true, bIf(atK MN.Q1c.cnt MN.Q1c.T MN.K1in1c i y,
      true, bIf(atK MN.Q1d.cnt MN.Q1d.T MN.K1in1d i y, true,
        atK MN.Q1e.cnt MN.Q1e.T MN.K1in1e i y)))), true))

end CertificateChecks.KernelSpor.MNd

end


module

public import Certificates.Kernel.Sporadic.OddCore.J2Cn
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2Cn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 315 9 (mask 9) p q

@[expose] noncomputable def idK : Nat := pidn 315 9

@[expose] noncomputable def F (k : Nat) : Nat := J2CentT.F k

@[expose] noncomputable def I (k : Nat) : Nat := J2CentI k

@[expose] noncomputable def sK (G : Nat) : Bool :=
  siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) J2P.LR
    J2P.TRI J2P.BP 3 0 G

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

theorem k_base : bAnd(szOK 315 9, bAnd(canonK 315 9 (mask 9) (315 * 9) idK,
    bAnd(CFSG.KS.Prim.idK 315 9 (mask 9),
    bAnd(allN 42 (fun k => bAnd(canonK 315 9 (mask 9) (315 * 9) (F k),
      canonK 315 9 (mask 9) (315 * 9) (I k))),
    allN 2 (fun j => bAnd(canonK 315 9 (mask 9) (315 * 9) (J2P.S j),
      canonK 315 9 (mask 9) (315 * 9) (J2P.SI j))))))) = true := by
  quickRfl

theorem k_bindO : bAnd(allN 2 (fun j => bAnd(Nat.beq (J2R1.G j) (J2P.S j),
      Nat.beq (J2R1.GI j) (J2P.SI j))),
    bAnd(allN 2 (fun j => bAnd(Nat.beq (J2R2.G j) (J2P.S j),
      Nat.beq (J2R2.GI j) (J2P.SI j))),
    bAnd(allN 2 (fun j => bAnd(Nat.beq (J2R3.G j) (J2P.S j),
      Nat.beq (J2R3.GI j) (J2P.SI j))),
    bAnd(Nat.beq J2R1.R (F 9), bAnd(Nat.beq J2R2.R (F 17), Nat.beq J2R3.R (F 31)))))) = true := by
  quickRfl

theorem k_bindM : bAnd(allN 8 (fun j => bAnd(Nat.beq (J2SY.G j) idK,
      Nat.beq (J2SY.GI j) (F (Nat.succ j)))),
    bAnd(allN 3 (fun j => bAnd(Nat.beq (J2K1.G j) idK, Nat.beq (J2K1.GI j) (F (Nat.add 10 j)))),
    bAnd(allN 2 (fun j => bAnd(Nat.beq (J2E2a.G j) idK, Nat.beq (J2E2a.GI j) (F (Nat.add 24 j)))),
    allN 2 (fun j => bAnd(Nat.beq (J2E2b.G j) idK, Nat.beq (J2E2b.GI j) (F (Nat.add 27 j))))))) =
    true := by
  quickRfl

theorem k_bindQ : bAnd(allN 3 (fun j => bAnd(Nat.beq (J2Q1a.G j) (F (Nat.add 10 j)),
      bAnd(Nat.beq (J2Q1a.GI j) (I (Nat.add 10 j)), bAnd(Nat.beq (J2Q1b.G j) (F (Nat.add 10 j)),
      Nat.beq (J2Q1b.GI j) (I (Nat.add 10 j)))))),
    bAnd(allN 5 (fun j => bAnd(Nat.beq (J2Q2a.G j) (F (Nat.add 18 j)),
      bAnd(Nat.beq (J2Q2a.GI j) (I (Nat.add 18 j)), bAnd(Nat.beq (J2Q2b.G j) (F (Nat.add 18 j)),
      bAnd(Nat.beq (J2Q2b.GI j) (I (Nat.add 18 j)), bAnd(Nat.beq (J2Q2c.G j) (F (Nat.add 18 j)),
      Nat.beq (J2Q2c.GI j) (I (Nat.add 18 j)))))))),
    bAnd(allN 4 (fun j => bAnd(Nat.beq (J2Q3a.G j) (F (Nat.add 32 j)),
      bAnd(Nat.beq (J2Q3a.GI j) (I (Nat.add 32 j)), bAnd(Nat.beq (J2Q3b.G j) (F (Nat.add 32 j)),
      bAnd(Nat.beq (J2Q3b.GI j) (I (Nat.add 32 j)), bAnd(Nat.beq (J2Q3c.G j) (F (Nat.add 32 j)),
      Nat.beq (J2Q3c.GI j) (I (Nat.add 32 j)))))))),
    bAnd(Nat.beq J2Q1a.R (F 13), bAnd(Nat.beq J2Q1b.R (F 15), bAnd(Nat.beq J2Q2a.R (F 23),
    bAnd(Nat.beq J2Q2b.R (F 26), bAnd(Nat.beq J2Q2c.R (F 29), bAnd(Nat.beq J2Q3a.R (F 36),
    bAnd(Nat.beq J2Q3b.R (F 38), Nat.beq J2Q3c.R (F 40))))))))))) = true := by
  quickRfl

theorem k_heads : bAnd(penumHdK J2R1.R J2R1.cnt 3000 J2R1.T J2R1.PL,
    bAnd(penumHdK J2R2.R J2R2.cnt 3000 J2R2.T J2R2.PL,
    bAnd(penumHdK J2R3.R J2R3.cnt 3000 J2R3.T J2R3.PL,
    bAnd(penumHdK idK J2SY.cnt 3000 J2SY.T J2SY.PL, bAnd(penumHdK idK J2K1.cnt 3000 J2K1.T J2K1.PL,
    bAnd(penumHdK J2Q1a.R J2Q1a.cnt 3000 J2Q1a.T J2Q1a.PL,
    bAnd(penumHdK J2Q1b.R J2Q1b.cnt 3000 J2Q1b.T J2Q1b.PL,
    bAnd(penumHdK J2Q2a.R J2Q2a.cnt 3000 J2Q2a.T J2Q2a.PL,
    bAnd(penumHdK J2Q2b.R J2Q2b.cnt 3000 J2Q2b.T J2Q2b.PL,
    bAnd(penumHdK J2Q2c.R J2Q2c.cnt 3000 J2Q2c.T J2Q2c.PL,
    bAnd(penumHdK J2Q3a.R J2Q3a.cnt 3000 J2Q3a.T J2Q3a.PL,
    bAnd(penumHdK J2Q3b.R J2Q3b.cnt 3000 J2Q3b.T J2Q3b.PL,
    bAnd(penumHdK J2Q3c.R J2Q3c.cnt 3000 J2Q3c.T J2Q3c.PL,
    bAnd(penumHdK idK J2E2a.cnt 3000 J2E2a.T J2E2a.PL,
    bAnd(penumHdK idK J2E2b.cnt 3000 J2E2b.T J2E2b.PL,
    bAnd(penumHdK idK J2C1.cnt 3000 J2C1.T J2C1.PL,
    penumHdK idK J2C2.cnt 3000 J2C2.T J2C2.PL)))))))))))))))) = true := by
  quickRfl

theorem k_sizes : bAnd(Nat.beq J2R1.cnt 1800, bAnd(Nat.beq J2R2.cnt 2520, bAnd(Nat.beq J2R3.cnt 315,
    bAnd(Nat.beq J2SY.cnt 256, bAnd(Nat.beq J2K1.cnt 336, bAnd(Nat.beq J2Q1a.cnt 48,
    bAnd(Nat.beq J2Q1b.cnt 56, bAnd(Nat.beq J2Q2a.cnt 12, bAnd(Nat.beq J2Q2b.cnt 12,
    bAnd(Nat.beq J2Q2c.cnt 20, bAnd(Nat.beq J2Q3a.cnt 80, bAnd(Nat.beq J2Q3b.cnt 192,
    bAnd(Nat.beq J2Q3c.cnt 192, bAnd(Nat.beq J2E2a.cnt 60, Nat.beq J2E2b.cnt 60)))))))))))))) =
    true := by
  quickRfl

theorem k_u : bAnd(involK (F 0), bAnd(bIf(sK (F 0), false, true),
    allN 2 (fun j => bAnd(sK (J2P.S j),
      sK (pc (pc (F 0) (J2P.S j)) (I 0)))))) = true := by
  quickRfl

theorem k_syl : allN 8 (fun j => bIf(sK (F (Nat.succ j)), true, sK (pc (F (Nat.succ j)) (F 0)))) =
    true := by
  quickRfl

theorem k_reps : bAnd(involK (F 9), bAnd(involK (F 17), bAnd(involK (F 31),
    bAnd(bIf(sK (F 9), false, true), bAnd(sK (pc (F 9) (F 0)), bAnd(sK (F 17), sK (F 31))))))) =
    true := by
  quickRfl

theorem k_cg : bAnd(allN 3 (fun j => bAnd(sK (F (Nat.add 10 j)), commK (F (Nat.add 10 j)) (F 9))),
    bAnd(allN 5 (fun j => bAnd(sK (F (Nat.add 18 j)), commK (F (Nat.add 18 j)) (F 17))),
    allN 4 (fun j => bAnd(sK (F (Nat.add 32 j)), commK (F (Nat.add 32 j)) (F 31))))) = true := by
  quickRfl

@[expose] noncomputable def oddK (r p t : Nat) : Bool :=
  bAnd(sK (F r), bAnd(commK (F r) (F t), bAnd(isId p (F r), notId 1 (F r))))

@[expose] noncomputable def conjK (h t : Nat) : Bool :=
  bAnd(sK (F h), commK (F h) (F t))

theorem k_odd : bAnd(oddK 13 7 9, bAnd(oddK 15 3 9, bAnd(oddK 23 5 17, bAnd(oddK 26 5 17,
    bAnd(oddK 29 3 17, bAnd(oddK 36 3 31, bAnd(oddK 38 5 31, oddK 40 5 31))))))) = true := by
  quickRfl

theorem k_conj : bAnd(conjK 14 9, bAnd(conjK 16 9, bAnd(conjK 30 17, bAnd(conjK 37 31,
    bAnd(conjK 39 31, conjK 41 31))))) = true := by
  quickRfl

theorem k_ord : bAnd(bAnd(isId 4 (cw (F 13) (F 14) (I 14)), bAnd(notId 2 (cw (F 13) (F 14) (I 14)),
      notId 1 (cw (F 13) (F 14) (I 14)))),
    bAnd(bAnd(isId 4 (cw (F 15) (F 16) (I 16)), bAnd(notId 2 (cw (F 15) (F 16) (I 16)),
      notId 1 (cw (F 15) (F 16) (I 16)))),
    bAnd(bAnd(isId 2 (cw (F 29) (F 30) (I 30)), notId 1 (cw (F 29) (F 30) (I 30))),
    bAnd(bAnd(isId 6 (cw (F 36) (F 37) (I 37)), bAnd(notId 3 (cw (F 36) (F 37) (I 37)),
      bAnd(notId 2 (cw (F 36) (F 37) (I 37)), notId 1 (cw (F 36) (F 37) (I 37))))),
    bAnd(bAnd(isId 4 (cw (F 38) (F 39) (I 39)), bAnd(notId 2 (cw (F 38) (F 39) (I 39)),
      notId 1 (cw (F 38) (F 39) (I 39)))),
    bAnd(isId 4 (cw (F 40) (F 41) (I 41)), bAnd(notId 2 (cw (F 40) (F 41) (I 41)),
      notId 1 (cw (F 40) (F 41) (I 41))))))))) = true := by
  quickRfl

theorem k_norm : bAnd(atK J2Q2a.cnt J2Q2a.T J2Nin2a 0 (F 24),
    bAnd(atK J2Q2a.cnt J2Q2a.T J2Nin2a 1 (F 25),
    bAnd(atK J2Q2b.cnt J2Q2b.T J2Nin2b 0 (F 27), bAnd(atK J2Q2b.cnt J2Q2b.T J2Nin2b 1 (F 28),
    bAnd(Nat.blt (r32 J2EInv 0) J2E2a.cnt, bAnd(involK (J2E2a.T (r32 J2EInv 0)),
    bAnd(Nat.blt (r32 J2EInv 1) J2E2b.cnt, involK (J2E2b.T (r32 J2EInv 1))))))))) = true := by
  quickRfl

@[expose] noncomputable def ucovK (i t : Nat) : Bool :=
  strictB (pc (pc (F 0) (F t)) (I 0)) (fun y => bIf(atK J2R1.cnt J2R1.T J2Uin1 i y, true,
    bIf(atK J2R2.cnt J2R2.T J2Uin2 i y, true, atK J2R3.cnt J2R3.T J2Uin3 i y)))

theorem k_ucov : bAnd(ucovK 0 9, bAnd(ucovK 1 17, ucovK 2 31)) = true := by quickRfl

@[expose] noncomputable def selK (p₁ p₂ y : Nat) : Bool :=
  bAnd(bIf(Nat.beq y idK, false, true), bIf(isId p₁ y, true, isId p₂ y))

@[expose] noncomputable def sel1K (i : Nat) : Bool :=
  strictB (J2K1.T i) (fun y => bIf(selK 3 7 y, bIf(atK J2Q1a.cnt J2Q1a.T J2K1in1a i y, true,
    atK J2Q1b.cnt J2Q1b.T J2K1in1b i y), true))

@[expose] noncomputable def sel2K (i : Nat) : Bool :=
  strictB (J2C1.T i) (fun y => bIf(selK 3 5 y, bIf(atK J2Q2a.cnt J2Q2a.T J2C1in2a i y, true,
    bIf(atK J2Q2b.cnt J2Q2b.T J2C1in2b i y, true, atK J2Q2c.cnt J2Q2c.T J2C1in2c i y)), true))

theorem k_sel1 : allN J2K1.cnt sel1K = true := by quickRfl

theorem k_sel2 : allN J2C1.cnt sel2K = true := by quickRfl

end CertificateChecks.KernelSpor.J2Cn

end

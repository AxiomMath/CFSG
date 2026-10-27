module

public import Certificates.Kernel.HS3850.D23005
public import Certificates.Kernel.HS3850.Small
public import Certificates.Kernel.LocalQT.Tc.Gen
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KD.LQT.C4126

@[expose] noncomputable def lc4 (l : Nat) : Nat := HC.F (Nat.add (nat_lit 35) l)

@[expose] noncomputable def lc4i (l : Nat) : Nat := pinvS 3850 12 (mask 12) (lc4 l)

@[expose] noncomputable def ckC (s : Nat) : Bool :=
  penumSlK 3850 12 (mask 12) (3850 * 12) false EC.G EC.GI 4 EC.cnt EC.T EC.PL EC.POS EC.SRT EC.SRI
    (Nat.mul s (nat_lit 32)) (nat_lit 32)

@[expose] noncomputable def commQ (x : Nat) : Bool :=
  allN 4 (fun j => Nat.beq (pc x (EQ.G j)) (pc (EQ.G j) x))

@[expose] def centIdx : List Nat :=
  [0, 181, 244, 265, 1066, 1098, 1139, 1192, 1377, 1577, 1770, 1788, 1845, 1877, 1901, 1907]

@[expose] noncomputable def ckZ (s : Nat) : Bool :=
  allN 32 (fun d => strictB (Nat.add (Nat.mul s (nat_lit 32)) d) (fun i =>
    bIf(Nat.blt i (nat_lit 1920), Bool.beq (commQ (EC.T i)) (centIdx.elem i), true)))

@[expose] noncomputable def inQ (x : Nat) : Bool := (allN 16 (fun q => (Nat.beq (EQ.T q) x).not)).not

theorem eq_ok : penumSlK 3850 12 (mask 12) (3850 * 12) false EQ.G EQ.GI 4 EQ.cnt EQ.T EQ.PL EQ.POS
    EQ.SRT EQ.SRI 0 16 = true := by
  quickRfl

theorem hd_ok : bAnd(Nat.beq EC.cnt 1920, bAnd(Nat.beq EQ.cnt 16,
    bAnd(penumHdK idn EC.cnt 1920 EC.T EC.PL, bAnd(penumHdK idn EQ.cnt 16 EQ.T EQ.PL,
    bAnd(allN 4 (fun l => bAnd(Nat.beq (EC.G l) (lc4 l),
      bAnd(canonK 3850 12 (mask 12) (3850 * 12) (lc4i l), Nat.beq (pc (lc4 l) (lc4i l)) idn))),
    bAnd(Nat.beq (EQ.G 0) (wfoldR lc4 [0, 1, 0, 3, 0, 2, 1, 3]),
    bAnd(Nat.beq (EQ.G 1) (wfoldR lc4 [0, 3, 0, 2, 1, 3, 0, 1]),
    bAnd(Nat.beq (EQ.G 2) (wfoldR lc4 [1, 1, 0, 2, 3, 0, 1, 3]),
      Nat.beq (EQ.G 3) (wfoldR lc4 [0, 1, 3, 1, 1, 0, 2, 3]))))))))) = true := by
  quickRfl

theorem norm_ok : allN 4 (fun j => allN 4 (fun i =>
    bAnd(inQ (pc (pc (lc4 j) (EQ.G i)) (lc4i j)), inQ (pc (pc (lc4i j) (EQ.G i)) (lc4 j))))) =
      true := by
  quickRfl

theorem cent_ok : Nat.beq (foldN 1920 (fun x c => nIf(centIdx.elem x, Nat.succ c, c)) 0) 16 =
    true := by
  quickRfl

end CFSG.KD.HS3850

end

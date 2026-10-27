module

public import Certificates.Kernel.LocalQT.Base.C4143D
public import CFSG.Quasithin.Background.A312SporRuInputs
public import Certificates.Data.Kernel.LocalQT.PcW

public section

namespace CFSG.KD.Ru7130

open CFSG.KC.Enum CFSG.KC.LQT.PcW

@[expose] noncomputable def I : Nat := pidn (nat_lit 4060) (nat_lit 12)

@[expose] noncomputable def Lab (l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), pcS 4060 12 4095 I (CFSG.KD.LQT.C4143.TF (nat_lit 0)),
    pcS 4060 12 4095 I (CFSG.KD.LQT.C4143.TF (nat_lit 1)))

@[expose] def mw2 : List Nat :=
  [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0]

@[expose] noncomputable def M : Nat := wordPB 4060 12 4095 Lab mw2 I

@[expose] noncomputable def Lc (l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), pcS 4060 12 4095 I (CFSG.KD.LQT.C4143.TF (nat_lit 163)),
  nIf(Nat.beq l (nat_lit 1), pcS 4060 12 4095 I (CFSG.KD.LQT.C4143.TF (nat_lit 172)),
  nIf(Nat.beq l (nat_lit 2), pcS 4060 12 4095 I (CFSG.KD.LQT.C4143.TF (nat_lit 185)), M)))

@[expose] noncomputable def Ls : List Nat := [Lc 0, Lc 1, Lc 2, Lc 3]

@[expose] noncomputable def Vs : List Nat :=
  CFSG.Quasithin.A312S.Ru.ruVWords.map fun v => wordPB 4060 12 4095 Lc v I

end CFSG.KD.Ru7130

end

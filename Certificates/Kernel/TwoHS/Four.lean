module

public import Certificates.Kernel.HS3850.Fours
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl2
meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl2
meta import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.CosetTableShort
meta import CFSG.Certificates.CosetTableShort

public section

set_option maxRecDepth 400000
set_option Elab.async false

#ks_chars CFSG.KD.TwoHS.RT CFSG.EvenSporadicStandard.TwoHS.harRHex
#kmisc_hexflat CFSG.KD.TwoHS.RT CFSG.EvenSporadicStandard.TwoHS.harRHex 3 3850 12 14

#kc_repo #kc_json_gz CFSG.KD.TwoHS "Certificates/Kernel/TwoHS/data/rtw.json.gz" 411
  7263853080282896874 (rtW : List (List Nat))

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KD.LQT.C4126 CFSG.KD.LQT.HN
open CFSG.KS.MulH

@[expose] noncomputable def pinv (p : Nat) : Nat := pinvS 3850 12 (mask 12) p

@[expose] noncomputable def invK (p : Nat) : Bool :=
  bAnd(canonK 3850 12 (mask 12) (3850 * 12) p, bAnd(canonK 3850 12 (mask 12) (3850 * 12) (pinv p),
    invEqK 3850 12 (mask 12) (3850 * 12) p (pinv p)))

@[expose] noncomputable def inPK (k : Nat) : Bool :=
  bAnd(Nat.beq (RT.F k) (wfoldR ls8 (rtW.getD k [])), invK (RT.F k))

@[expose] noncomputable def conjK (c r x : Nat) : Bool := Nat.beq (pc (pc c r) (pinv c)) x

@[expose] noncomputable def lB (z y l : Nat) : Nat := nIf(Nat.blt l (nat_lit 2), z, y)

@[expose] noncomputable def wB (z y : Nat) (wd : List Nat) : Nat :=
  wfoldK 3850 12 (mask 12) (lB z y) wd idn

@[expose] noncomputable def commK (z y : Nat) (p : List Nat × List Nat) (t : Nat) : Bool :=
  strictB (wB z y p.1) (fun a => strictB (wB z y p.2) (fun b =>
    bAnd(invK a, bAnd(invK b, Nat.beq (pc (pc a b) (pc (pinv a) (pinv b))) t))))

@[expose] noncomputable def fourCK (c : Nat) : Bool :=
  strictB (Nat.mul (nat_lit 7) c) (fun o => strictB (HC.F (Nat.add (nat_lit 21) (Nat.mul 13 c)))
  (fun r => strictB (RT.F o) (fun x => strictB (RT.F (Nat.add o 3)) (fun z =>
  strictB (RT.F (Nat.add o 4)) (fun y =>
    bAnd(invK r, bAnd(invK x, bAnd(allN 6 (fun j => inPK (Nat.add o (Nat.succ j))),
    bAnd(conjK (RT.F (Nat.add o 1)) (HC.F 12) x, bAnd(Nat.beq (pc x r) (pc r x),
    bAnd(conjK (RT.F (Nat.add o 2)) r (pc x r),
    bAnd(Nat.beq (pc z r) (pc r z), bAnd(Nat.beq (pc y r) (pc r y),
    bAnd(commK z y ((CFSG.EvenSporadicStandard.TwoHS.harBPairs c).getD 0 ([], [])) z,
    bAnd(commK z y ((CFSG.EvenSporadicStandard.TwoHS.harBPairs c).getD 1 ([], [])) y,
    bAnd(conjK (RT.F (Nat.add o 5)) (HC.F 5) z,
      conjK (RT.F (Nat.add o 6)) r (pc r z)))))))))))))))))

theorem four0 : fourCK 0 = true := by quickRfl

theorem four1 : fourCK 1 = true := by quickRfl

end CFSG.KD.TwoHS

end

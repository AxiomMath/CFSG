module

public import Certificates.Kernel.Fi23P.KDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23P

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KD.Fi23K CFSG.Monster.Existence.Fi23Sp8.Native

@[expose] noncomputable def stabK (c : Nat) (pr : Nat × Nat) : List Int :=
  invWord (pathF rootsA[c]! 100 (XK pr.2 pr.1)) ++ [((pr.2 + 1 : Nat) : Int)] ++
    pathF rootsA[c]! 100 pr.1

@[expose] noncomputable def regW (t : Nat) : List Nat :=
  (List.range (tb L 10 (2 * t + 1))).map fun i => tb L 9 (tb L 10 (2 * t) + i)

@[expose] def cntW (c : Nat) : Nat := if c = 0 then 7 else if c = 1 then 4 else 3

set_option Elab.async false

theorem stab_ok0 : ((stabPairs 0).map (stabK 0)).all (fun w =>
    w.all sLetterOK && wK w rootsA[0]! == rootsA[0]!) = true := by quickRfl
theorem stab_ok1 : ((stabPairs 1).map (stabK 1)).all (fun w =>
    w.all sLetterOK && wK w rootsA[1]! == rootsA[1]!) = true := by quickRfl
theorem stab_ok2 : ((stabPairs 2).map (stabK 2)).all (fun w =>
    w.all sLetterOK && wK w rootsA[2]! == rootsA[2]!) = true := by quickRfl

theorem regs_ok0 : (((stabPairs 0).map (stabK 0)).map (fun w => w.map zIdx) ==
    (List.range (cntW 0)).map fun j => regW (baseP 0 + j)) = true := by quickRfl
theorem regs_ok1 : (((stabPairs 1).map (stabK 1)).map (fun w => w.map zIdx) ==
    (List.range (cntW 1)).map fun j => regW (baseP 1 + j)) = true := by quickRfl
theorem regs_ok2 : (((stabPairs 2).map (stabK 2)).map (fun w => w.map zIdx) ==
    (List.range (cntW 2)).map fun j => regW (baseP 2 + j)) = true := by quickRfl

end CFSG.KD.Fi23P

end

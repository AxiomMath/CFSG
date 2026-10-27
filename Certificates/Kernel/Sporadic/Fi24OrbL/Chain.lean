module

public import Certificates.Kernel.Sporadic.Fi24Net.Data
public import Certificates.Data.Kernel.Spor.Fi24ThreeO
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Fi24OrbL

open CFSG.KC.Fi24ThreeO CFSG.KD.Fi24Net

@[expose] def lv : Nat → List Nat
  | 0 => List.range 26
  | 1 => (List.range 22).map (· + 4)
  | 2 => (List.range 18).map (· + 8)
  | 3 => (List.range 14).map (· + 12)
  | 4 => (List.range 10).map (· + 16)
  | 5 => [24, 25]
  | _ => []

@[expose] def bp : Nat → Nat
  | 0 => 0
  | 1 => 305530
  | 2 => 5604
  | 3 => 221549
  | 4 => 266275
  | _ => 186844

@[expose] def sz : Nat → Nat
  | 0 => 306936
  | 1 => 275264
  | 2 => 218400
  | 3 => 93312
  | 4 => 243
  | _ => 3

@[expose] def rd : Nat → Nat
  | 0 => 6
  | 1 => 6
  | 2 => 7
  | 3 => 8
  | 4 => 4
  | _ => 1

@[expose] noncomputable def o (i : Nat) : Bool := orbOK NW (lv i) (rd i) (bp i) (sz i)

@[expose] noncomputable def oSub : Bool := orbOK NW (lv 1) (nat_lit 5) (nat_lit 1) (nat_lit 31671)

namespace Ck

theorem o0 : o 0 = true := by quickRfl
theorem o1 : o 1 = true := by quickRfl
theorem o2 : o 2 = true := by quickRfl
theorem o3 : o 3 = true := by quickRfl
theorem o4 : o 4 = true := by quickRfl
theorem o5 : o 5 = true := by quickRfl
theorem oS : oSub = true := by quickRfl

end Ck

end CFSG.KD.Fi24OrbL

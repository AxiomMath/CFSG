module

public meta import CFSG.Certificates.Kernel.Common.Eval

public section

namespace CFSG.KC.M22Out24790Gen

open CFSG.KC.Eval

meta def natV : Val → Nat
  | .nat n => n
  | _ => 0

meta def listV : Val → List Val
  | .list xs => xs.toList
  | _ => []

meta def stepTW : Step := fun vs =>
  match vs[0]?, vs[1]? with
  | some T, some W =>
    let tp := (listV T).foldr
      (fun t r => (listV t).foldr (fun x a => natV x + 32 * a) 0 + 2 ^ 110 * r) 0
    let wp := (listV W).foldr
      (fun w r => (listV w).foldr (fun i a => natV i + 2 * a) 1 + 2 ^ 17 * r) 0
    .ok #[(`TP, .nat tp), (`WP, .nat wp)]
  | _, _ => .error "stepTW: two arguments"

meta def tabV (v : Val) : Array Nat := ((listV v).map natV).toArray

meta def tmulV (s t : Array Nat) : Array Nat := t.map fun j => s.getD j 0

meta def stepCG : Step := fun vs =>
  match vs[0]?, vs[1]?, vs[2]? with
  | some T, some U, some IT =>
    let L := ((listV T ++ listV U).map tabV).toArray
    let I := (listV IT).toArray.map tabV
    let gaps (t : Array Nat) : Array Val := Id.run do
      let mut out : Array Val := #[]
      let mut last := 0
      for i in [0:L.size] do
        let x := L[i]!
        if tmulV x t == tmulV t x then
          out := out.push (.nat (i - last))
          last := i + 1
      return out
    .ok #[(`CG, .list (#[0, 12, 195, 196, 197].map fun r => .list (gaps I[r]!)))]
  | _, _, _ => .error "stepCG: three arguments"

end CFSG.KC.M22Out24790Gen

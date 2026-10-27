module

public import CFSG.Certificates.Kernel.Spor.HexNumsSound
public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Spor.RawSound

open Lean Elab Command

open CFSG.KC.Tab in
elab "#ks_hexnums " pre:ident sId:ident dd:num ww:num : command => do
  let P := pre.getId
  let d := dd.getNat
  let w := ww.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let env ← getEnv
  let s ← match (env.find? sN).bind ConstantInfo.value? with
    | some (.lit (.strVal s)) => pure s
    | _ => liftTermElabM <| unsafe evalConst String sN
  let hv := fun (c : Char) =>
    if '0' ≤ c ∧ c ≤ '9' then c.toNat - 48 else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 87 else 16
  let mut vals : Array Nat := #[]
  let mut t := 0
  let mut v := 0
  for c in s.toList do
    let h := hv c
    if h < 16 then
      if t + 1 == d then
        vals := vals.push (v * 16 + h)
        t := 0
        v := 0
      else
        t := t + 1
        v := v * 16 + h
  let mut F := 0
  for i in [0:vals.size] do
    F := F ||| (vals[i]! <<< (w * i))
  let N := vals.size
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `F) natT (lit F)
    let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkAppN (mkConst ``CFSG.KS.HexNums.hexNumsK)
        #[mkConst (P ++ `chars), lit d, lit w, lit N, mkConst (P ++ `F)])
      (mkConst ``Bool.true)
    CFSG.KC.addThmDecl <| { name := P ++ `ok, levelParams := [], type := ty, value := reflBoolTrue }

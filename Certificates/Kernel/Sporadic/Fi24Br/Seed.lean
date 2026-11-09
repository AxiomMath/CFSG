module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Loop
public meta import CFSG.Certificates.Kernel.Common.StrChunks
public import Certificates.Data.Kernel.Spor.BytesF
public import Certificates.Data.CFSGNative.Fi24.Data
public import Certificates.Kernel.Sporadic.Fi24Br.Data
public import CFSG.Certificates.Kernel.Common.StrChunks
public meta import Lean

public section

set_option maxRecDepth 10000000
set_option maxHeartbeats 0

#str_chunks CFSG.KD.BrFi24.SA CFSG.Sporadic.Fi24.Native.seedA 1048576 10000000 2048

#str_chunks CFSG.KD.BrFi24.SB CFSG.Sporadic.Fi24.Native.seedB 1048576 10000000 2048

open Lean Elab Command in
elab "#chars_suffixes " pre:ident k:num : command => liftCoreM <| withOptions (Elab.async.set · false) do
  let P := pre.getId
  let k := k.getNat
  let env ← getEnv
  let lty := mkApp (mkConst ``List [0]) (mkConst ``Char)
  let mut cur := mkConst (P ++ `chars)
  for _ in [0:4] do
    if let .const n _ := cur then
      if let some (.defnInfo d) := env.find? n then cur := d.value
  let mut m := 0
  let mut done := false
  while !done do
    let mut t := cur
    let mut i := 0
    while i < k && t.isAppOfArity ``List.cons 3 do
      t := t.appArg!; i := i + 1
    if i < k || !t.isAppOfArity ``List.cons 3 then done := true
    else
      m := m + 1
      addDecl (forceExpose := true) <| .defnDecl
        { name := P ++ Name.mkSimple s!"T{m}", levelParams := [], type := lty, value := t,
          hints := .regular 0, safety := .safe }
      let src := if m == 1 then mkConst (P ++ `chars) else mkConst (P ++ Name.mkSimple s!"T{m - 1}")
      let dr := mkApp3 (mkConst ``List.drop [0]) (mkConst ``Char) (mkRawNatLit k) src
      addDecl <| .thmDecl
        { name := P ++ Name.mkSimple s!"drop{m - 1}", levelParams := [],
          type := mkApp3 (mkConst ``Eq [1]) lty dr (mkConst (P ++ Name.mkSimple s!"T{m}")),
          value := mkApp2 (mkConst ``Eq.refl [1]) lty (mkConst (P ++ Name.mkSimple s!"T{m}")) }
      cur := t
  if m == 0 then throwError "#chars_suffixes: {P}.chars is shorter than {k}"

#chars_suffixes CFSG.KD.BrFi24.SA 65536

#chars_suffixes CFSG.KD.BrFi24.SB 65536

namespace CFSG.KD.BrFi24

open CFSG.KS.Bytes

@[expose] noncomputable def segE (F : Nat → Nat) (lb len e : Nat) (cs : List Char) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i e)
    (fun ch _ ih i => (fun c => bAnd(Nat.blt c (nat_lit 128), bAnd(Nat.blt i len,
        bAnd(Nat.beq c (fld(F (Nat.div i lb), Nat.mul (nat_lit 8) (Nat.mod i lb), nat_lit 255)),
          CFSG.KC.M1F2.strictB (Nat.succ i) ih))))
      (Char.toNat ch))
    cs

theorem bAnd_mono {x p q : Bool} (h : Bool.rec (motive := fun _ => Bool) false p x = true)
    (hpq : p = true → q = true) : Bool.rec (motive := fun _ => Bool) false q x = true := by
  cases x
  · exact absurd h Bool.false_ne_true
  · exact hpq h

theorem runF_append {F : Nat → Nat} {lb len e : Nat} {b : List Char} :
    ∀ {a : List Char} {i : Nat}, segE F lb len e a i = true → runF F lb len b e = true →
      runF F lb len (a ++ b) i = true
  | [], i, h1, h2 => by
    rw [Nat.eq_of_beq_eq_true h1]
    exact h2
  | _ :: a, _, h1, h2 =>
    bAnd_mono h1 fun h => bAnd_mono h fun h' => bAnd_mono h' fun h'' => runF_append (a := a) h'' h2

theorem runF_split (n : Nat) {F : Nat → Nat} {lb len e i : Nat} {l : List Char}
    (h1 : segE F lb len e (l.take n) i = true) (h2 : runF F lb len (l.drop n) e = true) :
    runF F lb len l i = true := by
  have h := runF_append h1 h2
  rwa [List.take_append_drop] at h

theorem runF_split' (n : Nat) {F : Nat → Nat} {lb len e i : Nat} {l l' : List Char}
    (h1 : segE F lb len e (l.take n) i = true) (hd : l.drop n = l') (h2 : runF F lb len l' e = true) :
    runF F lb len l i = true := by
  subst hd
  exact runF_split n h1 h2

theorem seed1_c0 :
    segE P1 256 617792 65536 (List.take 65536 SA.chars) 0 = true := by
  quickRfl

theorem seed1_c1 :
    segE P1 256 617792 131072 (List.take 65536 SA.T1) 65536 = true := by
  quickRfl

theorem seed1_c2 :
    segE P1 256 617792 196608 (List.take 65536 SA.T2) 131072 = true := by
  quickRfl

theorem seed1_c3 :
    segE P1 256 617792 262144 (List.take 65536 SA.T3) 196608 = true := by
  quickRfl

theorem seed1_c4 :
    segE P1 256 617792 327680 (List.take 65536 SA.T4) 262144 = true := by
  quickRfl

theorem seed1_c5 :
    segE P1 256 617792 393216 (List.take 65536 SA.T5) 327680 = true := by
  quickRfl

theorem seed1_c6 :
    segE P1 256 617792 458752 (List.take 65536 SA.T6) 393216 = true := by
  quickRfl

theorem seed1_c7 :
    segE P1 256 617792 524288 (List.take 65536 SA.T7) 458752 = true := by
  quickRfl

theorem seed1_c8 :
    segE P1 256 617792 589824 (List.take 65536 SA.T8) 524288 = true := by
  quickRfl

theorem seed1_c9 : runF P1 256 617792 SA.T9 589824 = true := by
  quickRfl

theorem seed1_run : runF P1 256 617792 SA.chars 0 = true :=
  runF_split' 65536 seed1_c0 SA.drop0 <|
  runF_split' 65536 seed1_c1 SA.drop1 <|
  runF_split' 65536 seed1_c2 SA.drop2 <|
  runF_split' 65536 seed1_c3 SA.drop3 <|
  runF_split' 65536 seed1_c4 SA.drop4 <|
  runF_split' 65536 seed1_c5 SA.drop5 <|
  runF_split' 65536 seed1_c6 SA.drop6 <|
  runF_split' 65536 seed1_c7 SA.drop7 <|
  runF_split' 65536 seed1_c8 SA.drop8 <|
  seed1_c9

theorem seed2_c0 :
    segE P2 256 617792 65536 (List.take 65536 SB.chars) 0 = true := by
  quickRfl

theorem seed2_c1 :
    segE P2 256 617792 131072 (List.take 65536 SB.T1) 65536 = true := by
  quickRfl

theorem seed2_c2 :
    segE P2 256 617792 196608 (List.take 65536 SB.T2) 131072 = true := by
  quickRfl

theorem seed2_c3 :
    segE P2 256 617792 262144 (List.take 65536 SB.T3) 196608 = true := by
  quickRfl

theorem seed2_c4 :
    segE P2 256 617792 327680 (List.take 65536 SB.T4) 262144 = true := by
  quickRfl

theorem seed2_c5 :
    segE P2 256 617792 393216 (List.take 65536 SB.T5) 327680 = true := by
  quickRfl

theorem seed2_c6 :
    segE P2 256 617792 458752 (List.take 65536 SB.T6) 393216 = true := by
  quickRfl

theorem seed2_c7 :
    segE P2 256 617792 524288 (List.take 65536 SB.T7) 458752 = true := by
  quickRfl

theorem seed2_c8 :
    segE P2 256 617792 589824 (List.take 65536 SB.T8) 524288 = true := by
  quickRfl

theorem seed2_c9 : runF P2 256 617792 SB.T9 589824 = true := by
  quickRfl

theorem seed2_run : runF P2 256 617792 SB.chars 0 = true :=
  runF_split' 65536 seed2_c0 SB.drop0 <|
  runF_split' 65536 seed2_c1 SB.drop1 <|
  runF_split' 65536 seed2_c2 SB.drop2 <|
  runF_split' 65536 seed2_c3 SB.drop3 <|
  runF_split' 65536 seed2_c4 SB.drop4 <|
  runF_split' 65536 seed2_c5 SB.drop5 <|
  runF_split' 65536 seed2_c6 SB.drop6 <|
  runF_split' 65536 seed2_c7 SB.drop7 <|
  runF_split' 65536 seed2_c8 SB.drop8 <|
  seed2_c9

end CFSG.KD.BrFi24

end

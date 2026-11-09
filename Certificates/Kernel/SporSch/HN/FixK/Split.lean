module

public import Certificates.Kernel.SporSch.HN.FixK.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

namespace CFSG.KD.HNXK

open CFSG.KC.LL.HNX CFSG.KD.LgHNX

@[expose] noncomputable def fixPart (G lo n v : Nat) : Bool :=
  Nat.beq (fixSum TX CM3 M G lo n) v

private theorem fx_strictN (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem fixSum_succ (T : Nat → Nat) (CM3 M G lo n : Nat) :
    fixSum T CM3 M G lo (n + 1) =
      fixSum T CM3 M G lo n + fixLeaf T 464 CM3 M [G] (lo + n) (CFSG.KS.SporSch.hnxC (lo + n)) := by
  show CFSG.KC.Loop.strictN (fixSum T CM3 M G lo n) (fun a => Nat.add a
      (fixLeaf T (nat_lit 464) CM3 M [G] (Nat.add lo n) (CFSG.KS.SporSch.hnxC (Nat.add lo n)))) = _
  rw [fx_strictN]
  rfl

theorem fixSum_append (T : Nat → Nat) (CM3 M G lo a : Nat) : ∀ b,
    fixSum T CM3 M G lo (a + b) = fixSum T CM3 M G lo a + fixSum T CM3 M G (lo + a) b
  | 0 => rfl
  | b + 1 => by
    rw [← Nat.add_assoc, fixSum_succ, fixSum_append T CM3 M G lo a b, fixSum_succ]
    simp only [Nat.add_assoc]

theorem fixPart_add {G lo a b va vb : Nat} (ha : fixPart G lo a va = true)
    (hb : fixPart G (lo + a) b vb = true) : fixPart G lo (a + b) (va + vb) = true := by
  have h1 : fixSum TX CM3 M G lo a = va := Nat.eq_of_beq_eq_true ha
  have h2 : fixSum TX CM3 M G (lo + a) b = vb := Nat.eq_of_beq_eq_true hb
  show Nat.beq (fixSum TX CM3 M G lo (a + b)) (va + vb) = true
  rw [fixSum_append, h1, h2]
  exact Nat.beq_refl _

theorem fixOk_of8 (G : Nat) (V : Nat → Nat) (m k n0 n1 n2 n3 n4 n5 n6 n7
    v0 v1 v2 v3 v4 v5 v6 v7 : Nat)
    (h0 : fixPart G (2227 * k) n0 v0 = true)
    (h1 : fixPart G (2227 * k + n0) n1 v1 = true)
    (h2 : fixPart G (2227 * k + (n0 + n1)) n2 v2 = true)
    (h3 : fixPart G (2227 * k + (n0 + n1 + n2)) n3 v3 = true)
    (h4 : fixPart G (2227 * k + (n0 + n1 + n2 + n3)) n4 v4 = true)
    (h5 : fixPart G (2227 * k + (n0 + n1 + n2 + n3 + n4)) n5 v5 = true)
    (h6 : fixPart G (2227 * k + (n0 + n1 + n2 + n3 + n4 + n5)) n6 v6 = true)
    (h7 : fixPart G (2227 * k + (n0 + n1 + n2 + n3 + n4 + n5 + n6)) n7 v7 = true)
    (hn : n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 = fixLen k)
    (hv : v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 = V (8 * m + k)) :
    fixOk G V m k = true := by
  have h := fixPart_add (fixPart_add (fixPart_add (fixPart_add (fixPart_add (fixPart_add
    (fixPart_add h0 h1) h2) h3) h4) h5) h6) h7
  rw [hn, hv] at h
  exact h

end CFSG.KD.HNXK

namespace CFSG.KD.HNXK.FixGen

open CFSG.KC.Tab

meta def isTrueB (b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)

meta def reflN (n : Nat) : Expr := mkApp2 (mkConst ``Eq.refl [1]) natT (lit n)

end CFSG.KD.HNXK.FixGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KD.HNXK.FixGen in
elab "#kss_fix " pre:ident fId:ident gId:ident vId:ident mm:num k0:num cc:num
    "[" vs:num,* "]" : command => do
  let P := pre.getId
  let m := mm.getNat
  let kz := k0.getNat
  let c := cc.getNat
  let vals := vs.getElems.map (·.getNat)
  unless vals.size == 8 * c do
    throwError "#kss_fix: expected {8 * c} counts, got {vals.size}"
  let fN ← liftCoreM <| realizeGlobalConstNoOverload fId
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let vN ← liftCoreM <| realizeGlobalConstNoOverload vId
  let fE := mkConst fN
  let gE := mkConst gN
  liftCoreM <| withOptions (Elab.async.set · false) do
    for i in [0:c] do
      let k := kz + i
      let len := if k < 7 then 2227 else 2224
      let b := fun j => len * j / 8
      let mut qs : Array Expr := #[]
      for j in [0:8] do
        let nm := P ++ Name.mkSimple s!"q{i}_{j}"
        let ty := isTrueB (mkAppN (mkConst ``CFSG.KD.HNXK.fixPart)
          #[gE, lit (2227 * k + b j), lit (b (j + 1) - b j), lit vals[8 * i + j]!])
        CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := reflBoolTrue }
        qs := qs.push (mkConst nm)
      let ns := (List.range 8).toArray.map fun j => lit (b (j + 1) - b j)
      let vv := (List.range 8).toArray.map fun j => lit vals[8 * i + j]!
      let tot := (List.range 8).foldl (fun s j => s + vals[8 * i + j]!) 0
      let pf := mkAppN (mkConst ``CFSG.KD.HNXK.fixOk_of8)
        (#[gE, mkConst vN, lit m, lit k] ++ ns ++ vv ++ qs ++ #[reflN len, reflN tot])
      let cn := P ++ Name.mkSimple s!"c{i}"
      let cty := isTrueB (mkApp fE (lit i))
      CFSG.KC.addThmDecl <| { name := cn, levelParams := [], type := cty, value := pf }
    let pE := mkLambda `i .default natT (isTrueB (mkApp fE (mkBVar 0)))
    let v := forallChain pE c fun i => mkConst (P ++ Name.mkSimple s!"c{i}")
    let ty := mkForall `i .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit c])
      (isTrueB (mkApp fE (mkBVar 1))))
    CFSG.KC.addThmDecl <| { name := P ++ `all, levelParams := [], type := ty, value := v }

end

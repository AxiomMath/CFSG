module

public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.Misc.KernelRfl
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public import CFSG.Certificates.Kernel.Common.Tab
public import Std.Tactic.BVDecide.Normalize.Prop

open Lean Elab Command CFSG.KC.Tab

public section

namespace CFSG.KS.FLGen

meta def letName (P : Name) (l : Int) : Name :=
  let h := if 0 < l then l.toNat - 1 else (-l).toNat - 1
  P ++ (if 0 < l then (if h == 0 then `A else if h == 1 then `B else Name.mkSimple s!"T{h}")
    else Name.mkSimple s!"U{h}")

end CFSG.KS.FLGen

elab "#kon_flists " rd:ident pre:ident out:ident wId:ident lo:num hi:num : command => do
  let RD ← liftCoreM <| realizeGlobalConstNoOverload rd
  let wN ← liftCoreM <| realizeGlobalConstNoOverload wId
  let words ← liftTermElabM <| unsafe evalConst (Array (List Int)) wN
  let fT := mkForall `i .default natT natT
  withSync do
    for j in [lo.getNat:hi.getNat] do
      let lst := words[j]!.foldr (fun l acc => mkApp3 (mkConst ``List.cons [0]) fT
        (mkApp (mkConst RD) (mkConst (CFSG.KS.FLGen.letName pre.getId l))) acc)
        (mkApp (mkConst ``List.nil [0]) fT)
      addDef (out.getId.appendAfter (toString j)) (mkApp (mkConst ``List [0]) fT) lst

elab "#kon_nests " rd:ident pre:ident out:ident wId:ident lo:num hi:num : command => do
  let RD ← liftCoreM <| realizeGlobalConstNoOverload rd
  let wN ← liftCoreM <| realizeGlobalConstNoOverload wId
  let words ← liftTermElabM <| unsafe evalConst (Array (List Int)) wN
  withSync do
    for j in [lo.getNat:hi.getNat] do
      let body := words[j]!.foldr (fun l acc =>
        mkApp2 (mkConst RD) (mkConst (CFSG.KS.FLGen.letName pre.getId l)) acc) (mkBVar 0)
      addDef (out.getId.appendAfter (toString j)) (mkForall `i .default natT natT)
        (mkLambda `x .default natT body)

namespace CFSG.KS.FLGen

open CFSG.KC.Enum

@[expose] noncomputable def traceR (L : List (Nat → Nat)) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun f _ ih => f ih) L

theorem traceR_map {α : Type} (g : α → Nat → Nat) : ∀ (L : List α) (x : Nat),
    traceR (L.map g) x = L.foldr g x
  | [], _ => rfl
  | a :: L, x => by
    change g a (traceR (L.map g) x) = g a (L.foldr g x)
    rw [traceR_map g L x]

theorem bAnd_iff {a b : Bool} : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := by
  cases a <;> simp

theorem allBlk_spec {b : Nat} {f : Nat → Bool} :
    ∀ {len : Nat}, allBlk b f len = true → ∀ l < len, f (Nat.add b l) = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | len + 1, h, l, hl => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
      at h
    obtain ⟨h1, h2⟩ := bAnd_iff.1 h
    rcases Nat.lt_or_ge l len with hl' | hl'
    · exact allBlk_spec h2 l hl'
    · obtain rfl : l = len := by omega
      exact h1

theorem allBlk_of {b : Nat} {f : Nat → Bool} : ∀ {len : Nat},
    (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
    rw [h len (Nat.lt_succ_self len), allBlk_of (fun l hl => h l (Nat.lt_succ_of_lt hl))]

end CFSG.KS.FLGen

end

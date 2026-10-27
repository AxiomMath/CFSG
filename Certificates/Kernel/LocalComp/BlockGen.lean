module

public import Certificates.Kernel.LocalComp.Co3BfsLemmas
public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Co3BfsSound
public import CFSG.Certificates.Kernel.FendelSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound

open Lean Elab Command

public section

namespace CFSG.KC.Co3Bfs

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def guardF (n : Nat) (f : Nat → Bool) (j : Nat) : Bool :=
  bIf(Nat.blt j n, f j, true)

theorem cover_of_blocks {f : Nat → Bool} {n B nb : Nat} (hB : 0 < B) (hn : n ≤ B * nb)
    (h : ∀ k < nb, allFrom (B * k) B (guardF n f) = true) : ∀ j < n, f j = true := by
  intro j hj
  have := blocks hB h j (by omega)
  unfold guardF at this
  have hb : Nat.blt j n = true := Nat.ble_eq_true_of_le hj
  rwa [hb] at this

end CFSG.KC.Co3Bfs

namespace CFSG.KC.BlockGen

open CFSG.KC.Tab CFSG.KS.RawGen

elab "#lc_blocks " pre:ident fId:ident nN:num bN:num : command => do
  let P := pre.getId
  let n := nN.getNat
  let B := bN.getNat
  let fN ← liftCoreM <| realizeGlobalConstNoOverload fId
  let nb := (n + B - 1) / B
  let gE := mkApp2 (mkConst ``CFSG.KC.Co3Bfs.guardF) (lit n) (mkConst fN)
  let bodyT := fun (kE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KC.Co3Bfs.allFrom)
    #[mulE (lit B) kE, lit B, gE])
  liftCoreM <| withOptions (Elab.async.set · false) do
    let bName := fun (k : Nat) => P ++ Name.mkSimple ("b" ++ toString k)
    for k in [0:nb] do
      let nm := bName k
      let ty := bodyT (lit k)
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := reflBoolTrue }
    let PE := mkLambda `k .default natT (bodyT (mkBVar 0))
    let pf := forallChain PE nb fun k => mkConst (bName k)
    let allT := mkForall `k .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit nb])
      (bodyT (mkBVar 1)))
    CFSG.KC.addThmDecl <| { name := P ++ `all, levelParams := [], type := allT, value := pf }
    addDef (P ++ `nb) natT (lit nb)

end CFSG.KC.BlockGen

end

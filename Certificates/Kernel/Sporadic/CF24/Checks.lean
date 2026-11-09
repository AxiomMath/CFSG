module

public import Certificates.Kernel.Sporadic.CF24.Data
public import Certificates.Kernel.Sporadic.OddCore.Suz23000K
public import Certificates.Data.Kernel.Spor.CF24K
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.GSThmBCatalog7CF24
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.BfsPinBaseSound
public meta import Lean

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.CF24

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.CF24 CFSG.KC.Misc.ArrEnum
open CertificateChecks.KernelSpor.Suz23000 CFSG.ComponentClassification.GSThmB.CF24

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pv" => pinvS 1782 11 (mask 11)
local notation "wk" => wordK 1782 11 (mask 11) (pidn 1782 11)

@[expose] noncomputable def BF (h : Nat) : Nat := nIf(Nat.beq h 0, B0, B1)

@[expose] noncomputable def BIF (h : Nat) : Nat := nIf(Nat.beq h 0, B0I, B1I)

@[expose] noncomputable def SGF (h : Nat) : Nat := sel7 SG0 SG1 SG2 SG3 SG4 SG5 SG6 h

@[expose] noncomputable def SGIF (h : Nat) : Nat := sel7 SGI0 SGI1 SGI2 SGI3 SGI4 SGI5 SGI6 h

@[expose] noncomputable def LF (j : Nat) : Nat := sel5 L0 L1 L2 L3 L4 j

@[expose] noncomputable def LIF (j : Nat) : Nat := sel5 LI0 LI1 LI2 LI3 LI4 j

theorem permGH : allN 7 (fun k => permB 1782 11 (GH (Nat.succ k))) = true := by
  quickRfl

theorem permB01 : bAnd(permB 1782 11 B0, bAnd(permB 1782 11 B1,
    bAnd(Nat.beq (pv B0) B0I, Nat.beq (pv B1) B1I))) = true := by
  quickRfl

theorem all7_of {f : Nat → Bool} (h0 : f 0 = true) (h1 : f 1 = true) (h2 : f 2 = true)
    (h3 : f 3 = true) (h4 : f 4 = true) (h5 : f 5 = true) (h6 : f 6 = true) :
    ∀ i < 7, f i = true := by
  intro i hi
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6
  | _ + 7, _ => omega

theorem sgK_0 : Nat.beq (wk BF BIF (nthW IW.W 0)) (SGF 0) = true := by
  quickRfl

theorem sgK_1 : Nat.beq (wk BF BIF (nthW IW.W 1)) (SGF 1) = true := by
  quickRfl

theorem sgK_2 : Nat.beq (wk BF BIF (nthW IW.W 2)) (SGF 2) = true := by
  quickRfl

theorem sgK_3 : Nat.beq (wk BF BIF (nthW IW.W 3)) (SGF 3) = true := by
  quickRfl

theorem sgK_4 : Nat.beq (wk BF BIF (nthW IW.W 4)) (SGF 4) = true := by
  quickRfl

theorem sgK_5 : Nat.beq (wk BF BIF (nthW IW.W 5)) (SGF 5) = true := by
  quickRfl

theorem sgK_6 : Nat.beq (wk BF BIF (nthW IW.W 6)) (SGF 6) = true := by
  quickRfl

theorem sgK : allN 7 (fun h => Nat.beq (wk BF BIF (nthW IW.W h)) (SGF h)) = true :=
  CFSG.KC.BfsPin.allN_intro (all7_of sgK_0 sgK_1 sgK_2 sgK_3 sgK_4 sgK_5 sgK_6)

theorem sgiK : allN 7 (fun h => Nat.beq (pv (SGF h)) (SGIF h)) = true := by
  quickRfl

theorem lK : allN 5 (fun j => Nat.beq (pc (pc (pc (GH 2) (GH (Nat.add j 3))) (pv (GH 2)))
    (pv (GH (Nat.add j 3)))) (LF j)) = true := by
  quickRfl

theorem liK : allN 5 (fun j => Nat.beq (pv (LF j)) (LIF j)) = true := by
  quickRfl

theorem xK : Nat.beq (wk SGF SGIF (codesZ cf24XCodes)) XK = true := by
  quickRfl

theorem listRec_append {α β : Type} (b : β) (f : α → β → β) : ∀ u v : List α,
    List.rec (motive := fun _ => β) b (fun z _ ih => f z ih) (u ++ v) =
      List.rec (motive := fun _ => β) (List.rec (motive := fun _ => β) b (fun z _ ih => f z ih) v)
        (fun z _ ih => f z ih) u
  | [], _ => rfl
  | z :: u, v => congrArg (f z) (listRec_append b f u v)

theorem wordK_append (n w m base : Nat) (S SI : Nat → Nat) (u v : List Int) :
    wordK n w m base S SI (u ++ v) = wordK n w m (wordK n w m base S SI v) S SI u := by
  unfold wordK
  exact listRec_append _ _ u v

theorem codesZ_append : ∀ a b : List Nat, codesZ (a ++ b) = codesZ a ++ codesZ b
  | [], _ => rfl
  | c :: a, b => (congrArg (List.cons (zc c)) (codesZ_append a b) :)

theorem beq_wordK_append {n w m base : Nat} {S SI : Nat → Nat} {a b : List Nat} {M Z : Nat}
    (h1 : Nat.beq (wordK n w m base S SI (codesZ b)) M = true)
    (h2 : Nat.beq (wordK n w m M S SI (codesZ a)) Z = true) :
    Nat.beq (wordK n w m base S SI (codesZ (a ++ b))) Z = true := by
  rw [codesZ_append, wordK_append, Nat.eq_of_beq_eq_true h1]
  exact h2

end CertificateChecks.KernelSpor.CF24

meta def cf24YChunks : Array (List Nat) := #[
    [13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9,
      7, 5, 3, 1, 3, 7, 13, 11, 3, 1, 5, 8, 2, 13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5,
      7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1, 3, 7, 13, 11, 3, 1, 5, 3,
      9, 13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3,
      5, 7, 9, 7, 5, 3, 1, 3, 7, 13, 11, 3, 1, 5, 8, 2, 13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1,
      3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1, 3, 7, 13, 11, 3,
      1, 5, 3, 9, 13, 3, 13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7,
      9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1, 3, 7, 13, 11, 3, 1, 5, 2, 12, 13, 7, 3, 1, 5, 7,
      3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1, 3,
      7, 13, 11, 3],
    [1, 5, 13, 3, 4, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2,
      10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 5, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4,
      6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2,
      6, 12, 4, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2,
      10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 5, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4,
      6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2,
      6, 12, 10, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2,
      10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 11, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4,
      6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2,
      6, 12],
    [10, 4, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6,
      4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 5, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8,
      6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6,
      12, 4, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10,
      6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 5, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6,
      8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6,
      12, 10, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2,
      10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 11, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4,
      6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2,
      6, 12, 10, 2, 12],
    [4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2,
      0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 13, 3, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4,
      2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 2,
      12, 8, 2, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2,
      10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 3, 9, 4, 0, 2, 10, 12, 6, 2, 0, 2,
      4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0,
      2, 6, 12, 8, 2, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2,
      12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 3, 9, 4, 0, 2, 10, 12, 6, 2,
      0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6,
      4, 0, 2],
    [6, 12, 4, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10,
      6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 5, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6,
      8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6,
      12, 4, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10,
      6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 5, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6,
      8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6,
      12, 10, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2,
      10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 11, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4,
      6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2,
      6, 12, 10, 4],
    [4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2,
      0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 5, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2,
      6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 4, 4,
      0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6,
      2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 5, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4,
      2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 10,
      4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6, 4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4,
      6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12, 11, 4, 0, 2, 10, 12, 6, 2, 0, 2, 4, 6, 8, 6,
      4, 2, 6, 4, 6, 8, 6, 4, 2, 12, 2, 10, 6, 4, 6, 2, 0, 2, 0, 4, 2, 6, 4, 0, 2, 6, 12,
      10, 13, 7, 3, 1],
    [5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1,
      3, 7, 13, 11, 3, 1, 5, 8, 2, 13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13,
      3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1, 3, 7, 13, 11, 3, 1, 5, 3, 9, 13, 7, 3,
      1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5,
      3, 1, 3, 7, 13, 11, 3, 1, 5, 8, 2, 13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11,
      3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1, 3, 7, 13, 11, 3, 1, 5, 3, 9, 13,
      3, 13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1, 3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3,
      5, 7, 9, 7, 5, 3, 1, 3, 7, 13, 11, 3, 1, 5, 2, 12, 13, 7, 3, 1, 5, 7, 3, 5, 1, 3, 1,
      3, 7, 5, 7, 11, 3, 13, 3, 5, 7, 9, 7, 5, 7, 3, 5, 7, 9, 7, 5, 3, 1, 3, 7, 13, 11, 3,
      1, 5, 13, 3]]

open Lean Elab Command in
elab "#cf24_ystates" : command => liftCoreM <| withOptions (Elab.async.set · false) do
  let P := `CertificateChecks.KernelSpor.CF24
  let env ← getEnv
  let natOf (n : Name) : CoreM Nat := do
    match env.find? n with
    | some (.defnInfo d) => match d.value with
      | .lit (.natVal v) => pure v
      | _ => throwError "{n} is not a literal"
    | _ => throwError "{n} is not a definition"
  let unpack (x : Nat) : Array Nat := (Array.range 1782).map fun i => (x >>> (11 * i)) &&& 2047
  let pack (a : Array Nat) : Nat := Id.run do
    let mut acc := 0
    for i in [0:a.size] do acc := (acc <<< 11) ||| a[a.size - 1 - i]!
    return acc
  let mut gens : Array (Array Nat) := #[]
  let mut invs : Array (Array Nat) := #[]
  for i in [0:7] do
    gens := gens.push (unpack (← natOf (P ++ Name.mkSimple s!"SG{i}")))
    invs := invs.push (unpack (← natOf (P ++ Name.mkSimple s!"SGI{i}")))
  let chunks := cf24YChunks
  let natT := mkConst ``Nat
  for k in [0:7] do
    let l := chunks[k]!.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natT (mkNatLit x) acc)
      (mkApp (mkConst ``List.nil [0]) natT)
    addDecl (forceExpose := true) <| .defnDecl
      { name := P ++ Name.mkSimple s!"YA{k}", levelParams := [],
        type := mkApp (mkConst ``List [0]) natT, value := l, hints := .regular 0, safety := .safe }
  let mut T : Array Nat := Array.range 1782
  for k' in [0:7] do
    let k := 6 - k'
    for c in chunks[k]!.reverse do
      let L := if c % 2 == 0 then gens[c / 2]! else invs[c / 2]!
      T := T.map fun x => L[x]!
    if k ≥ 1 then
      addDecl (forceExpose := true) <| .defnDecl
        { name := P ++ Name.mkSimple s!"YS{k}", levelParams := [], type := mkConst ``Nat,
          value := mkRawNatLit (pack T), hints := .regular 0, safety := .safe }
  unless pack T == (← natOf (P ++ `YK)) do throwError "the recorded word does not give YK"

#cf24_ystates

namespace CertificateChecks.KernelSpor.CF24

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.CF24 CFSG.KC.Misc.ArrEnum
open CertificateChecks.KernelSpor.Suz23000 CFSG.ComponentClassification.GSThmB.CF24

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pv" => pinvS 1782 11 (mask 11)
local notation "wk" => wordK 1782 11 (mask 11) (pidn 1782 11)

theorem yK_6 : Nat.beq (wordK 1782 11 (mask 11) (pidn 1782 11) SGF SGIF (codesZ YA6)) YS6 = true := by
  quickRfl

theorem yK_5 : Nat.beq (wordK 1782 11 (mask 11) YS6 SGF SGIF (codesZ YA5)) YS5 = true := by
  quickRfl

theorem yK_4 : Nat.beq (wordK 1782 11 (mask 11) YS5 SGF SGIF (codesZ YA4)) YS4 = true := by
  quickRfl

theorem yK_3 : Nat.beq (wordK 1782 11 (mask 11) YS4 SGF SGIF (codesZ YA3)) YS3 = true := by
  quickRfl

theorem yK_2 : Nat.beq (wordK 1782 11 (mask 11) YS3 SGF SGIF (codesZ YA2)) YS2 = true := by
  quickRfl

theorem yK_1 : Nat.beq (wordK 1782 11 (mask 11) YS2 SGF SGIF (codesZ YA1)) YS1 = true := by
  quickRfl

theorem yK_0 : Nat.beq (wordK 1782 11 (mask 11) YS1 SGF SGIF (codesZ YA0)) YK = true := by
  quickRfl

theorem yK : Nat.beq (wk SGF SGIF (codesZ cf24YCodes)) YK = true := by
  rw [show cf24YCodes = YA0 ++ (YA1 ++ (YA2 ++ (YA3 ++ (YA4 ++ (YA5 ++ YA6))))) from rfl]
  exact beq_wordK_append (beq_wordK_append (beq_wordK_append (beq_wordK_append (beq_wordK_append (beq_wordK_append yK_6 yK_5) yK_4) yK_3) yK_2) yK_1) yK_0

theorem xyK : bAnd(Nat.beq (wk LF LIF cf24XP) XK, bAnd(Nat.beq (wk LF LIF cf24YP) YK,
    Nat.beq (pc XK YK) (pc YK XK))) = true := by
  quickRfl

theorem omK : Nat.beq (maskL cf24O1) OM = true := by
  quickRfl

theorem oK : allN 5 (fun j => allN 1782 (fun x =>
    Nat.beq (pg 1 (mask 1) OM (pg 11 (mask 11) (LF j) x)) (pg 1 (mask 1) OM x))) = true := by
  quickRfl

theorem bK : allN 5 (fun j => Nat.beq (pc BK (LF j)) (pc (LF j) BK)) = true := by
  quickRfl

theorem ptK : bAnd(Nat.beq (pg 1 (mask 1) OM 6) 1,
    bAnd(Nat.beq (pg 1 (mask 1) OM (pg 11 (mask 11) (SuzTP 0) 6)) 0,
    bAnd(Nat.beq (pg 1 (mask 1) OM (pg 11 (mask 11) BK 6)) 0,
    Nat.beq (pg 1 (mask 1) OM (pg 11 (mask 11) (pc (SuzTP 0) BK) 6)) 0))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.CF24

end

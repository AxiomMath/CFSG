module

public meta import Lean
public meta import Certificates.Kernel.LocalQT.Cmd
public import Certificates.Data.Kernel.LocalQT.Sec
public import Certificates.Kernel.LocalQT.Cmd

public section

namespace CFSG.KC.LQT

open CFSG.KC.Ord

@[expose] noncomputable def decStep (c : Lay) (M : Nat) (ch : Char)
    (ih : Nat → Nat → Nat → Nat → Bool) : Nat → Nat → Nat → Nat → Bool :=
  fun ph i j acc => strictB (Char.toNat ch) fun n =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (ih (nat_lit 0) i j acc) (ih (nat_lit 1) i j acc)
          (Nat.beq n (nat_lit 10)))
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (strictB (Nat.add acc (Nat.shiftLeft (Nat.mod (digitV n) c.p) (Nat.mul c.w j)))
              fun a => strictB (Nat.succ j) fun j1 =>
                Bool.rec (motive := fun _ => Bool) (ih (nat_lit 1) i j1 a)
                  (andB (Nat.beq (rowsOf c.S i (nat_lit 1) M) a)
                    (strictB (Nat.succ i) fun i1 => ih (nat_lit 1) i1 (nat_lit 0) (nat_lit 0)))
                  (Nat.beq j1 c.d))
            (ih (nat_lit 1) i j acc) (Nat.ble c.d i))
          (ih (nat_lit 1) i j acc) (isWs n))
        (Nat.beq ph (nat_lit 1))

@[expose] noncomputable def decK (c : Lay) (M : Nat) (k : Nat → Nat → Nat → Nat → Bool)
    (l : List Char) : Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool) k
    (fun ch _ ih => decStep c M ch ih) l

@[expose] noncomputable def decFin (c : Lay) (M : Nat) : Nat → Nat → Nat → Nat → Bool :=
  fun _ i _ acc => Nat.beq (Nat.shiftRight M (Nat.mul c.S i)) acc

theorem decOK_eq_decK (c : Lay) (M : Nat) (l : List Char) :
    decOK c M l = decK c M (decFin c M) l (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) :=
  rfl

theorem decK_append (c : Lay) (M : Nat) (k : Nat → Nat → Nat → Nat → Bool) :
    ∀ (a b : List Char), decK c M k (a ++ b) = decK c M (decK c M k b) a
  | [], _ => rfl
  | ch :: a, b => (congrArg (decStep c M ch) (decK_append c M k a b) :)

theorem decK_split (c : Lay) (M : Nat) (k : Nat → Nat → Nat → Nat → Bool) (n : Nat)
    (l : List Char) (ph i j acc ph' i' j' acc' : Nat)
    (h1 : ∀ k' : Nat → Nat → Nat → Nat → Bool,
      decK c M k' (List.take n l) ph i j acc = k' ph' i' j' acc')
    (h2 : decK c M k (List.drop n l) ph' i' j' acc' = true) :
    decK c M k l ph i j acc = true := by
  have e : decK c M k l = decK c M k (List.take n l ++ List.drop n l) := by
    rw [List.take_append_drop]
  rw [e, decK_append, h1]
  exact h2

theorem decK_split' (c : Lay) (M : Nat) (k : Nat → Nat → Nat → Nat → Bool) (n : Nat)
    (l l' : List Char) (ph i j acc ph' i' j' acc' : Nat)
    (h1 : ∀ k' : Nat → Nat → Nat → Nat → Bool,
      decK c M k' (List.take n l) ph i j acc = k' ph' i' j' acc')
    (hd : List.drop n l = l') (h2 : decK c M k l' ph' i' j' acc' = true) :
    decK c M k l ph i j acc = true := by
  subst hd
  exact decK_split c M k n l ph i j acc ph' i' j' acc' h1 h2

end CFSG.KC.LQT

end

public meta section

namespace CFSG.KC.LQT.Cmd

open Lean Elab Command Meta

meta def sliceLen : Nat := 65536

meta def decState (c : LayV) (ch : Char) (s : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  let (ph, i, j, acc) := s
  let n := ch.toNat
  if ph != 1 then (if n == 10 then (1, i, j, acc) else (0, i, j, acc))
  else if n == 32 || (9 ≤ n && n ≤ 13) then (1, i, j, acc)
  else if c.d ≤ i then (1, i, j, acc)
  else
    let dg := if 48 ≤ n && n ≤ 57 then n - 48 else 0
    let a := acc + ((dg % c.p) <<< (c.w * j))
    if j + 1 == c.d then (1, i + 1, 0, 0) else (1, i, j + 1, a)

meta def stE (s : Nat × Nat × Nat × Nat) : Array Expr :=
  let (ph, i, j, acc) := s
  #[lit ph, lit i, lit j, lit acc]

open CFSG.KC.LQT in
elab "#lqt_seed_dec " seed:ident p:num d:num : command => withSync do
  let seed := seed.getId
  let (p, d) := (p.getNat, d.getNat)
  let root := seedRoot seed
  let (s, sufs) ← addCharsCut (root ++ `L) seed sliceLen
  let c := layOf p d
  let R := seedDecRoot seed p d
  addDef (R ++ `lay) (mkConst ``CFSG.KC.LQT.Lay) c.expr
  let Mv := c.decode s
  addDef (R ++ `M) natE (lit Mv)
  let lay := mkConst (R ++ `lay)
  let M := mkConst (R ++ `M)
  let charT := mkConst ``Char
  let lc := mkApp (mkConst ``List [0]) charT
  let kT := mkForall `ph .default natE <| mkForall `i .default natE <|
    mkForall `j .default natE <| mkForall `acc .default natE boolE
  let chars := s.toList.toArray
  let nS := sufs.size
  let Ds : Array Expr := (Array.range nS).map fun m =>
    if m == 0 then mkConst (root ++ `L) else mkConst (root ++ Name.mkSimple s!"T{m}")
  for m in [1:nS] do
    addDef (root ++ Name.mkSimple s!"T{m}") lc sufs[m]!
  for m in [0:nS - 1] do
    let dr := mkApp3 (mkConst ``List.drop [0]) charT (lit sliceLen) Ds[m]!
    addThm (root ++ Name.mkSimple s!"drop{m}") (mkApp3 (mkConst ``Eq [1]) lc dr Ds[m + 1]!)
      (mkApp2 (mkConst ``Eq.refl [1]) lc Ds[m + 1]!)
  let mut sts : Array (Nat × Nat × Nat × Nat) := #[(0, 0, 0, 0)]
  let mut st := (0, 0, 0, 0)
  for m in [0:nS] do
    for q in [m * sliceLen:min chars.size ((m + 1) * sliceLen)] do
      st := decState c chars[q]! st
    sts := sts.push st
  let fin := mkApp2 (mkConst ``decFin) lay M
  for m in [0:nS - 1] do
    let sl := mkApp3 (mkConst ``List.take [0]) charT (lit sliceLen) Ds[m]!
    let rhs := mkAppN (.bvar 0) (stE sts[m + 1]!)
    let lhs := mkAppN (mkConst ``decK) (#[lay, M, .bvar 0, sl] ++ stE sts[m]!)
    let ty := mkForall `k .default kT (mkApp3 (mkConst ``Eq [1]) boolE lhs rhs)
    let pf := mkLambda `k .default kT (mkApp2 (mkConst ``Eq.refl [1]) boolE rhs)
    addThm (R ++ Name.mkSimple s!"c{m}") ty pf
  let last := nS - 1
  addTrue (R ++ Name.mkSimple s!"c{last}")
    (mkAppN (mkConst ``decK) (#[lay, M, fin, Ds[last]!] ++ stE sts[last]!))
  let mut pf := mkConst (R ++ Name.mkSimple s!"c{last}")
  for m' in [0:nS - 1] do
    let m := nS - 2 - m'
    pf := mkAppN (mkConst ``decK_split')
      (#[lay, M, fin, lit sliceLen, Ds[m]!, Ds[m + 1]!] ++ stE sts[m]! ++ stE sts[m + 1]! ++
        #[mkConst (R ++ Name.mkSimple s!"c{m}"), mkConst (root ++ Name.mkSimple s!"drop{m}"), pf])
  let L := mkConst (root ++ `L)
  let okTy := eqTrue (mkApp3 (mkConst ``decOK) lay M L)
  let k0 := mkAppN (mkConst ``decK) #[lay, M, fin, L, lit 0, lit 0, lit 0, lit 0]
  addThm (R ++ `ok) okTy (mkAppN (mkConst ``Eq.trans [1])
    #[boolE, mkApp3 (mkConst ``decOK) lay M L, k0, mkConst ``Bool.true,
      mkApp3 (mkConst ``decOK_eq_decK) lay M L, pf])

end CFSG.KC.LQT.Cmd

end

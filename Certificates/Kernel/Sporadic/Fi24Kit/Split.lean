module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Spor.Fi24FixP
public import Certificates.Data.Kernel.Spor.Fi24ThreeO
public import Certificates.Data.Kernel.Spor.Fi24PairK

open Lean Elab Command in
elab "#kn_val " n:ident " := " t:term : command => do
  let e ← liftTermElabM do
    let e ← Term.elabTerm t (some (mkConst ``Nat))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  liftCoreM <| withOptions (Elab.async.set · false) do
    match Lean.Kernel.whnf (← getEnv) {} e with
    | .ok (.lit (.natVal v)) =>
      addDecl (forceExpose := true) <| .defnDecl
        { name := n.getId, levelParams := [], type := mkConst ``Nat, value := mkRawNatLit v,
          hints := .regular 0, safety := .safe }
    | .ok r => throwError "#kn_val: the kernel stopped at {r}"
    | .error _ => throwError "#kn_val: kernel error"

public section

namespace CFSG.KD.Fi24Kit.Split

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24FixP

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem eq_of_beq {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

@[expose] noncomputable def fxRest (F : Nat → Nat) (P0 s k m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) s
    (fun j acc => strictN acc (fun a => fixStep F P0 (Nat.add k j) a)) m

theorem fixAcc_add (F : Nat → Nat) (P0 k : Nat) :
    ∀ m, fixAcc F P0 (Nat.add k m) = fxRest F P0 (fixAcc F P0 k) k m
  | 0 => rfl
  | m + 1 => by
    change strictN (fixAcc F P0 (Nat.add k m)) (fun a => fixStep F P0 (Nat.add k m) a) =
      strictN (fxRest F P0 (fixAcc F P0 k) k m) (fun a => fixStep F P0 (Nat.add k m) a)
    rw [fixAcc_add F P0 k m]

theorem fixAcc_first {F : Nat → Nat} {P0 m B : Nat} (h : Nat.beq (fixAcc F P0 m) B = true) :
    fixAcc F P0 m = B := eq_of_beq h

theorem fixAcc_step {F : Nat → Nat} {P0 k m n A B : Nat} (hA : fixAcc F P0 k = A)
    (hB : Nat.beq (fxRest F P0 A k m) B = true) (hn : Nat.add k m = n) : fixAcc F P0 n = B := by
  subst hn
  rw [fixAcc_add, hA]
  exact eq_of_beq hB

theorem fixS_of {F : Nat → Nat} {Q0 V : Nat} (h0 : Nat.beq (F (idPl19 (nat_lit 0))) Q0 = true)
    (h : fixAcc F Q0 (nat_lit 19) = V) : fixS F = V := by
  unfold fixS
  rw [strictN_eq, eq_of_beq h0, h]

@[expose] noncomputable def itG (G : Nat → Nat) (d S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S (fun _ ih => strictN ih G) d

theorem iterW_itG (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ws : List (List Nat)) (d S : Nat) :
    Fi24ThreeO.iterW NW NT ws d S = itG (Fi24ThreeO.stepW NW NT ws) d S := rfl

theorem iterK_itG (NW : Nat → Nat → Nat) (ws : List (List Int)) (d S : Nat) :
    Fi24PairK.iterW NW ws d S = itG (Fi24PairK.stepW NW ws) d S := rfl

theorem itG_add (G : Nat → Nat) (S a : Nat) : ∀ b, itG G (Nat.add a b) S = itG G b (itG G a S)
  | 0 => rfl
  | b + 1 => by
    change strictN (itG G (Nat.add a b) S) G = strictN (itG G b (itG G a S)) G
    rw [itG_add G S a b]

theorem itG_first {G : Nat → Nat} {S m B : Nat} (h : Nat.beq (itG G m S) B = true) : itG G m S = B :=
  eq_of_beq h

theorem itG_step {G : Nat → Nat} {S a b n A B : Nat} (hA : itG G a S = A)
    (hB : Nat.beq (itG G b A) B = true) (hn : Nat.add a b = n) : itG G n S = B := by
  subst hn
  rw [itG_add, hA]
  exact eq_of_beq hB

open CFSG.KC.MonsterConv.Perm in
@[expose] noncomputable def pkAcc (F : Nat → Nat) (P0 n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) P0
    (fun k acc => strictN acc (fun a => Nat.lor a (Nat.shiftLeft
      (Nat.xor (F (Nat.xor (idPl19 (Nat.succ k)) (idPl19 (nat_lit 0)))) P0)
      (Nat.mul (Nat.succ k) (nat_lit 524288))))) n

@[expose] noncomputable def pkRest (F : Nat → Nat) (P0 s k m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) s
    (fun j acc => strictN acc (fun a => Nat.lor a (Nat.shiftLeft
      (Nat.xor (F (Nat.xor (idPl19 (Nat.succ (Nat.add k j))) (idPl19 (nat_lit 0)))) P0)
      (Nat.mul (Nat.succ (Nat.add k j)) (nat_lit 524288))))) m

theorem pk19_eq (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cs : List Nat) :
    Fi24ThreeO.pk19 NW NT cs = strictN (Fi24ThreeO.wkC NW NT cs (idPl19 (nat_lit 0)))
      (fun P0 => pkAcc (Fi24ThreeO.wkC NW NT cs) P0 (nat_lit 18)) := rfl

theorem pkAcc_add (F : Nat → Nat) (P0 k : Nat) :
    ∀ m, pkAcc F P0 (Nat.add k m) = pkRest F P0 (pkAcc F P0 k) k m
  | 0 => rfl
  | m + 1 => by
    change strictN (pkAcc F P0 (Nat.add k m)) (fun a => Nat.lor a (Nat.shiftLeft
        (Nat.xor (F (Nat.xor (idPl19 (Nat.succ (Nat.add k m))) (idPl19 (nat_lit 0)))) P0)
        (Nat.mul (Nat.succ (Nat.add k m)) (nat_lit 524288)))) =
      strictN (pkRest F P0 (pkAcc F P0 k) k m) (fun a => Nat.lor a (Nat.shiftLeft
        (Nat.xor (F (Nat.xor (idPl19 (Nat.succ (Nat.add k m))) (idPl19 (nat_lit 0)))) P0)
        (Nat.mul (Nat.succ (Nat.add k m)) (nat_lit 524288))))
    rw [pkAcc_add F P0 k m]

theorem pkAcc_first {F : Nat → Nat} {P0 m B : Nat} (h : Nat.beq (pkAcc F P0 m) B = true) :
    pkAcc F P0 m = B := eq_of_beq h

theorem pkAcc_step {F : Nat → Nat} {P0 k m n A B : Nat} (hA : pkAcc F P0 k = A)
    (hB : Nat.beq (pkRest F P0 A k m) B = true) (hn : Nat.add k m = n) : pkAcc F P0 n = B := by
  subst hn
  rw [pkAcc_add, hA]
  exact eq_of_beq hB

theorem pk19_of {NW : Nat → Nat → Nat} {NT : Nat → Nat} {cs : List Nat} {Q0 V : Nat}
    (h0 : Nat.beq (Fi24ThreeO.wkC NW NT cs (idPl19 (nat_lit 0))) Q0 = true)
    (h : pkAcc (Fi24ThreeO.wkC NW NT cs) Q0 (nat_lit 18) = V) : Fi24ThreeO.pk19 NW NT cs = V := by
  rw [pk19_eq, strictN_eq, eq_of_beq h0, h]

theorem letB_eq (v : Nat) (k : Nat → Bool) : CFSG.KC.LceS.letB v k = k v := by cases v <;> rfl

theorem andB_of {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true := by
  rw [ha, hb]; rfl

theorem covW_of {NW : Nat → Nat → Nat} {NT : Nat → Nat} {ws : List (List Nat)} {d S F T : Nat}
    (hT : itG (Fi24ThreeO.stepW NW NT ws) d S = T)
    (h : Nat.beq (Nat.land (Nat.lor T F) Fi24Net.ptsM) Fi24Net.ptsM = true) :
    Fi24ThreeO.covW NW NT ws d S F = true := by
  unfold Fi24ThreeO.covW
  rw [iterW_itG, hT]
  exact h

theorem fixOK_eq (A : Nat → Nat → Nat) (w : List Nat) (c : Nat) :
    fixOK A w c = Nat.beq (popcount (fixS (walkP A w)) (nat_lit 524288)) c := rfl

theorem offOK_eq (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cg cs : List Nat) (S : Nat) :
    Fi24ThreeO.offOK NW NT cg cs S = Nat.beq (Nat.land (Nat.land S Fi24Net.ptsM)
      (Fi24ThreeO.offS NW NT cg cs)) (Nat.land S Fi24Net.ptsM) := rfl

theorem offS_eq (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cg cs : List Nat) :
    Fi24ThreeO.offS NW NT cg cs = strictN (Fi24ThreeO.pk19 NW NT cg) (fun G =>
      Nat.land (Nat.land Fi24Net.ptsM (Fi24ThreeO.diffP G (Fi24ThreeO.pk19 NW NT [])))
        (Nat.land (Fi24ThreeO.diffP G (Fi24ThreeO.pk19 NW NT cs))
          (Fi24ThreeO.diffP G (Fi24ThreeO.pk19 NW NT (cs ++ cs))))) := rfl

@[expose] noncomputable def chunkC (n c : Nat) : Nat :=
  Nat.land (Nat.shiftRight n (Nat.shiftLeft c (nat_lit 12)))
    (Nat.sub (Nat.pow (nat_lit 2) (nat_lit 4096)) (nat_lit 1))

@[expose] noncomputable def bitC (n i : Nat) : Nat :=
  strictN (Nat.shiftRight i (nat_lit 12)) (fun c =>
    Nat.land (Nat.shiftRight (chunkC n c) (Nat.land i (nat_lit 4095))) (nat_lit 1))

set_option exponentiation.threshold 5000 in
set_option simprocs false in
theorem bitN_eq_bitC : Fi24ThreeO.bitN = bitC := by
  funext n i
  unfold Fi24ThreeO.bitN bitC chunkC
  rw [strictN_eq]
  change n >>> i &&& (2 ^ 1 - 1) =
    ((n >>> ((i >>> 12) <<< 12)) &&& (2 ^ 4096 - 1)) >>> (i &&& (2 ^ 12 - 1)) &&& (2 ^ 1 - 1)
  have hq : (i >>> 12) <<< 12 = i / 4096 * 4096 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] <;> rfl
  rw [Nat.and_two_pow_sub_one_eq_mod i 12, hq, show (2 : Nat) ^ 12 = 4096 from rfl]
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases ht : t < 1
  · have t0 : t = 0 := by omega
    subst t0
    have e : i / 4096 * 4096 + (i % 4096 + 0) = i + 0 := by omega
    have e2 : i % 4096 < 4096 := Nat.mod_lt i (by omega)
    rw [e]
    simp [e2]
  · simp [ht]

end CFSG.KD.Fi24Kit.Split

end

open Lean Elab Command

elab "#kn_fixS " pre:ident " (" F:term ") " per:num : command => do
  let per := per.getNat
  let nm := fun (s : String) => mkIdent (pre.getId ++ Name.mkSimple s)
  let lit := fun (k : Nat) => Syntax.mkNumLit (toString k)
  let mut ks : Array Nat := #[]
  let mut k := 0
  while k < 19 do
    k := min 19 (k + per)
    ks := ks.push k
  elabCommand (← `(command| #kn_val $(nm "Q0") := ($F) (CFSG.KC.Fi24FixP.idPl19 (nat_lit 0))))
  elabCommand (← `(command| theorem $(nm "p0") :
      Nat.beq (($F) (CFSG.KC.Fi24FixP.idPl19 (nat_lit 0))) $(nm "Q0") = true := by quickRfl))
  let k1 := ks[0]!
  elabCommand (← `(command| #kn_val $(nm "A1") :=
      CFSG.KC.Fi24FixP.fixAcc ($F) $(nm "Q0") (nat_lit $(lit k1))))
  elabCommand (← `(command| theorem $(nm "p1") :
      Nat.beq (CFSG.KC.Fi24FixP.fixAcc ($F) $(nm "Q0") (nat_lit $(lit k1))) $(nm "A1") = true := by
        quickRfl))
  let mut prf ← `(CFSG.KD.Fi24Kit.Split.fixAcc_first $(nm "p1"))
  for j in [1:ks.size] do
    let kp := ks[j - 1]!
    let m := ks[j]! - kp
    let a := nm s!"A{j}"
    let b := nm s!"A{j + 1}"
    let p := nm s!"p{j + 1}"
    elabCommand (← `(command| #kn_val $b :=
        CFSG.KD.Fi24Kit.Split.fxRest ($F) $(nm "Q0") $a (nat_lit $(lit kp)) (nat_lit $(lit m))))
    elabCommand (← `(command| theorem $p :
        Nat.beq (CFSG.KD.Fi24Kit.Split.fxRest ($F) $(nm "Q0") $a (nat_lit $(lit kp))
          (nat_lit $(lit m))) $b = true := by quickRfl))
    prf ← `(CFSG.KD.Fi24Kit.Split.fixAcc_step (n := nat_lit $(lit ks[j]!)) $prf $p rfl)
  let last := nm s!"A{ks.size}"
  elabCommand (← `(command| theorem $(nm "eq") : CFSG.KC.Fi24FixP.fixS ($F) = $last :=
      CFSG.KD.Fi24Kit.Split.fixS_of $(nm "p0") $prf))

elab "#kn_iter " pre:ident " (" G:term ") " " (" S:term ") " " (" d:term ") " n:num per:num :
    command => do
  let n := n.getNat
  let per := per.getNat
  let nm := fun (s : String) => mkIdent (pre.getId ++ Name.mkSimple s)
  let lit := fun (k : Nat) => Syntax.mkNumLit (toString k)
  let mut ks : Array Nat := #[]
  let mut k := 0
  while k < n do
    k := min n (k + per)
    ks := ks.push k
  let k1 := ks[0]!
  elabCommand (← `(command| #kn_val $(nm "S1") :=
      CFSG.KD.Fi24Kit.Split.itG ($G) (nat_lit $(lit k1)) ($S)))
  elabCommand (← `(command| theorem $(nm "p1") :
      Nat.beq (CFSG.KD.Fi24Kit.Split.itG ($G) (nat_lit $(lit k1)) ($S)) $(nm "S1") = true := by
        quickRfl))
  let mut prf ← `(CFSG.KD.Fi24Kit.Split.itG_first $(nm "p1"))
  for j in [1:ks.size] do
    let m := ks[j]! - ks[j - 1]!
    let a := nm s!"S{j}"
    let b := nm s!"S{j + 1}"
    let p := nm s!"p{j + 1}"
    elabCommand (← `(command| #kn_val $b := CFSG.KD.Fi24Kit.Split.itG ($G) (nat_lit $(lit m)) $a))
    elabCommand (← `(command| theorem $p :
        Nat.beq (CFSG.KD.Fi24Kit.Split.itG ($G) (nat_lit $(lit m)) $a) $b = true := by quickRfl))
    if j + 1 == ks.size then
      prf ← `(CFSG.KD.Fi24Kit.Split.itG_step (n := $d) $prf $p rfl)
    else
      prf ← `(CFSG.KD.Fi24Kit.Split.itG_step (n := nat_lit $(lit ks[j]!)) $prf $p rfl)
  let last := nm s!"S{ks.size}"
  if ks.size == 1 then
    elabCommand (← `(command| theorem $(nm "eq") :
        CFSG.KD.Fi24Kit.Split.itG ($G) ($d) ($S) = $last := $prf))
  else
    elabCommand (← `(command| theorem $(nm "eq") :
        CFSG.KD.Fi24Kit.Split.itG ($G) ($d) ($S) = $last := $prf))

elab "#kn_pk19 " pre:ident " (" NW:term ") " " (" NT:term ") " " (" cs:term ") " per:num :
    command => do
  let per := per.getNat
  let nm := fun (s : String) => mkIdent (pre.getId ++ Name.mkSimple s)
  let lit := fun (k : Nat) => Syntax.mkNumLit (toString k)
  let F ← `(CFSG.KC.Fi24ThreeO.wkC ($NW) ($NT) ($cs))
  let mut ks : Array Nat := #[]
  let mut k := 0
  while k < 18 do
    k := min 18 (k + per)
    ks := ks.push k
  elabCommand (← `(command| #kn_val $(nm "Q0") := ($F) (CFSG.KC.Fi24FixP.idPl19 (nat_lit 0))))
  elabCommand (← `(command| theorem $(nm "p0") :
      Nat.beq (($F) (CFSG.KC.Fi24FixP.idPl19 (nat_lit 0))) $(nm "Q0") = true := by quickRfl))
  let k1 := ks[0]!
  elabCommand (← `(command| #kn_val $(nm "A1") :=
      CFSG.KD.Fi24Kit.Split.pkAcc ($F) $(nm "Q0") (nat_lit $(lit k1))))
  elabCommand (← `(command| theorem $(nm "p1") :
      Nat.beq (CFSG.KD.Fi24Kit.Split.pkAcc ($F) $(nm "Q0") (nat_lit $(lit k1))) $(nm "A1") = true := by
        quickRfl))
  let mut prf ← `(CFSG.KD.Fi24Kit.Split.pkAcc_first $(nm "p1"))
  for j in [1:ks.size] do
    let kp := ks[j - 1]!
    let m := ks[j]! - kp
    let a := nm s!"A{j}"
    let b := nm s!"A{j + 1}"
    let p := nm s!"p{j + 1}"
    elabCommand (← `(command| #kn_val $b :=
        CFSG.KD.Fi24Kit.Split.pkRest ($F) $(nm "Q0") $a (nat_lit $(lit kp)) (nat_lit $(lit m))))
    elabCommand (← `(command| theorem $p :
        Nat.beq (CFSG.KD.Fi24Kit.Split.pkRest ($F) $(nm "Q0") $a (nat_lit $(lit kp))
          (nat_lit $(lit m))) $b = true := by quickRfl))
    prf ← `(CFSG.KD.Fi24Kit.Split.pkAcc_step (n := nat_lit $(lit ks[j]!)) $prf $p rfl)
  let last := nm s!"A{ks.size}"
  elabCommand (← `(command| theorem $(nm "eq") :
      CFSG.KC.Fi24ThreeO.pk19 ($NW) ($NT) ($cs) = $last :=
      CFSG.KD.Fi24Kit.Split.pk19_of $(nm "p0") $prf))

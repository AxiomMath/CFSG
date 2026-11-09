module

public import Certificates.Data.Kernel.EvenSporP12.Defs
public import CFSG.Certificates.Kernel.Common.NatBuckets

public section

namespace CFSG.KC.EvenSporP12

open CFSG.EvenSporadicStandard.M12Std.SolomonK.P12 CFSG.KC.NatBuckets

@[expose] noncomputable def digK (P i : Nat) : Nat := Nat.land (Nat.shiftRight P (4 * i)) 15

theorem dig_eq : dig = digK := by
  funext P i
  unfold dig digK
  rw [show (16 : Nat) ^ i = 2 ^ (4 * i) by rw [Nat.pow_mul], ← Nat.shiftRight_eq_div_pow,
    show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem decLtN (a b : Nat) : decide (a < b) = Nat.blt a b := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]

theorem decLeN (a b : Nat) : decide (a ≤ b) = Nat.ble a b := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.ble_eq]

theorem containsN_eq (l : List Nat) (x : Nat) : l.contains x = memN l x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.contains_cons, ih, memN, memN, List.any_cons, beqN]

@[expose] noncomputable def encK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.add x (Nat.mul 16 ih)) l

theorem encL_eq : encL = encK := by
  funext l
  induction l with
  | nil => rfl
  | cons x l ih => rw [encL, ih]; rfl

@[expose] noncomputable def pmulKK (n P Q : Nat) : Nat := encK ((List.range n).map fun i => digK P (digK Q i))

@[expose] noncomputable def commKK (n P Q : Nat) : Bool :=
  (List.range n).all fun i => Nat.beq (digK P (digK Q i)) (digK Q (digK P i))

@[expose] noncomputable def sqKK (n P : Nat) : Bool := (List.range n).all fun i => Nat.beq (digK P (digK P i)) i

@[expose] noncomputable def wordKK (n : Nat) (G : List Nat) (w : List Nat) : Nat :=
  w.foldr (fun l acc => pmulKK n (G.getD l 0) acc) (pidK n)

@[expose] noncomputable def stepKK (n : Nat) (G : List Nat) (x : Nat) (w : List Nat)
    (acc : List (Nat × List Nat)) (k : Nat) : List (Nat × List Nat) :=
  let y := pmulKK n x (G.getD k 0)
  cond (acc.any (fun e => Nat.beq e.1 y)) acc (acc ++ [(y, w ++ [k])])

@[expose] noncomputable def goKK (n : Nat) (G : List Nat) : Nat → Nat → List (Nat × List Nat) →
    List (Nat × List Nat)
  | 0, _, acc => acc
  | fuel + 1, i, acc =>
    cond (Nat.blt i acc.length)
      (goKK n G fuel (i + 1) ((List.range G.length).foldl
        (stepKK n G (acc.getD i (0, [])).1 (acc.getD i (0, [])).2) acc))
      acc

@[expose] noncomputable def wordsOfKK (n : Nat) (G : List Nat) : List (List Nat) :=
  (goKK n G 2000 0 [(pidK n, [])]).map (·.2)

@[expose] noncomputable def allDistinctKK : List Nat → Bool
  | [] => true
  | x :: xs => !memN xs x && allDistinctKK xs

@[expose] noncomputable def enumOKKK (n : Nat) (G : List Nat) (L : List (List Nat)) : Bool :=
  let vals := L.map (wordKK n G)
  L.all (fun w => w.all (Nat.blt · G.length)) && L.contains [] &&
    (List.range G.length).all
      (fun k => vals.all fun v => memN vals (pmulKK n v (G.getD k 0))) &&
    allDistinctKK vals

@[expose] noncomputable def elemAbOKKK (n : Nat) (EG : List Nat) : Bool :=
  EG.all (sqKK n) && EG.all fun x => EG.all fun y => commKK n x y

@[expose] noncomputable def tripleKK (n : Nat) (Cx : List Nat) : List Nat :=
  Cx.filter fun y => sqKK n y && Nat.ble 64 (Cx.filter (commKK n y)).length

@[expose] noncomputable def countAtKK (n : Nat) (PV : List Nat) (x : Nat) : Bool :=
  Nat.blt (tripleKK n (PV.filter (commKK n x))).length 64

@[expose] noncomputable def countOKKK (n : Nat) (PV EV : List Nat) : Bool :=
  PV.all fun x => Nat.beq x (pidK n) || !sqKK n x || memN EV x || countAtKK n PV x

@[expose] noncomputable def order8OKKK (n : Nat) (G : List Nat) (w : List Nat) : Bool :=
  let g := wordKK n G w
  let g2 := pmulKK n g g
  let g4 := pmulKK n g2 g2
  let g8 := pmulKK n g4 g4
  w.all (Nat.blt · G.length) && !Nat.beq g4 (pidK n) && Nat.beq g8 (pidK n)

@[expose] noncomputable def normOKKK (n : Nat) (EV EG : List Nat) (c : Nat) : Bool :=
  Nat.beq (pmulKK n c (pmulKK n c c)) (pidK n) &&
    EG.all fun u => memN EV (pmulKK n (pmulKK n c u) (pmulKK n c c))

@[expose] noncomputable def p12CheckKK (n : Nat) : Bool :=
  let PG := (pGenSw.map (swapsArr n)).map enc
  let EG := (eGenSw.map (swapsArr n)).map enc
  let CG := (cGenSw.map (swapsArr n)).map enc
  let PW := wordsOfKK n PG
  let EW := wordsOfKK n EG
  let CW := wordsOfKK n CG
  let PV := PW.map (wordKK n PG)
  let EV := EW.map (wordKK n EG)
  pGenSw.all (swapsOK n) && eGenSw.all (swapsOK n) && cGenSw.all (swapsOK n) &&
    enumOKKK n PG PW && Nat.beq PW.length 512 && enumOKKK n EG EW && Nat.beq EW.length 64 &&
    enumOKKK n CG CW && Nat.beq CW.length 9 && elemAbOKKK n EG && EG.all (memN PV ·) &&
    order8OKKK n PG gWord && countOKKK n PV EV && CG.all (normOKKK n EV EG)

theorem pmulK_eq : pmulK = pmulKK := by
  funext n P Q
  unfold pmulK pmulKK
  rw [dig_eq, encL_eq]

theorem commK_eq : commK = commKK := by
  funext n P Q
  unfold commK commKK
  rw [dig_eq]
  simp only [beqN]

theorem sqK_eq : sqK = sqKK := by
  funext n P
  unfold sqK sqKK
  rw [dig_eq]
  simp only [beqN]

theorem wordK_eq : wordK = wordKK := by
  funext n G w
  unfold wordK wordKK
  rw [pmulK_eq]

theorem stepK_eq : stepK = stepKK := by
  funext n G x w acc k
  unfold stepK stepKK
  rw [pmulK_eq]
  simp only [beqN, cond_eq_ite]

theorem goK_eq (n : Nat) (G : List Nat) : ∀ fuel i acc, goK n G fuel i acc = goKK n G fuel i acc
  | 0, _, _ => by simp [goK, goKK]
  | fuel + 1, i, acc => by
    rw [goK, goKK, stepK_eq, goK_eq n G fuel, ← decLtN, cond_eq_ite]
    simp only [decide_eq_true_eq]

theorem wordsOfK_eq : wordsOfK = wordsOfKK := by
  funext n G
  unfold wordsOfK wordsOfKK
  rw [goK_eq]

theorem allDistinctK_eq : ∀ l, allDistinctK l = allDistinctKK l
  | [] => rfl
  | x :: xs => by rw [allDistinctK, allDistinctKK, containsN_eq, allDistinctK_eq xs]

theorem enumOKK_eq : enumOKK = enumOKKK := by
  funext n G L
  unfold enumOKK enumOKKK
  simp only [wordK_eq, pmulK_eq, containsN_eq, decLtN, allDistinctK_eq]

theorem elemAbOKK_eq : elemAbOKK = elemAbOKKK := by
  funext n EG
  unfold elemAbOKK elemAbOKKK
  rw [sqK_eq, commK_eq]

theorem countOKK_eq : countOKK = countOKKK := by
  funext n PV EV
  unfold countOKK countOKKK countAtK countAtKK tripleK tripleKK
  simp only [sqK_eq, commK_eq, containsN_eq, beqN, decLtN, decLeN]

theorem order8OKK_eq : order8OKK = order8OKKK := by
  funext n G w
  unfold order8OKK order8OKKK
  simp only [wordK_eq, pmulK_eq, beqN, decLtN, bne]

theorem normOKK_eq : normOKK = normOKKK := by
  funext n EV EG c
  unfold normOKK normOKKK
  simp only [pmulK_eq, beqN, containsN_eq]

theorem p12CheckK_eq (n : Nat) : p12CheckK n = p12CheckKK n := by
  unfold p12CheckK p12CheckKK
  simp only [wordsOfK_eq, wordK_eq, enumOKK_eq, elemAbOKK_eq, order8OKK_eq, countOKK_eq,
    normOKK_eq, containsN_eq, beqN]

@[expose] noncomputable def stepKB (n : Nat) (G : List Nat) (x : Nat) (w : List Nat)
    (st : List (Nat × List Nat) × List (List Nat)) (k : Nat) :
    List (Nat × List Nat) × List (List Nat) :=
  let y := pmulKK n x (G.getD k 0)
  cond (memB st.2 y) st (st.1 ++ [(y, w ++ [k])], insB st.2 y)

@[expose] noncomputable def goKB (n : Nat) (G : List Nat) : Nat → Nat → List (Nat × List Nat) × List (List Nat) →
    List (Nat × List Nat) × List (List Nat)
  | 0, _, st => st
  | fuel + 1, i, st =>
    cond (Nat.blt i st.1.length)
      (goKB n G fuel (i + 1) ((List.range G.length).foldl
        (stepKB n G (st.1.getD i (0, [])).1 (st.1.getD i (0, [])).2) st))
      st

def InvB (st : List (Nat × List Nat) × List (List Nat)) : Prop :=
  st.2.length = 37 ∧ ∀ z, memB st.2 z = st.1.any (fun e => Nat.beq e.1 z)

theorem stepKB_inv {n : Nat} {G : List Nat} {x : Nat} {w : List Nat}
    {st : List (Nat × List Nat) × List (List Nat)} (hI : InvB st) (k : Nat) :
    (stepKB n G x w st k).1 = stepKK n G x w st.1 k ∧ InvB (stepKB n G x w st k) := by
  simp only [stepKB, stepKK]
  have e : st.1.any (fun e => Nat.beq e.1 (pmulKK n x (G.getD k 0))) =
      memB st.2 (pmulKK n x (G.getD k 0)) := (hI.2 _).symm
  rw [e]
  cases memB st.2 (pmulKK n x (G.getD k 0))
  · rw [cond_false, cond_false]
    refine ⟨rfl, ?_, fun z => ?_⟩
    · show (insB st.2 _).length = 37
      rw [insB_length, hI.1]
    · show memB (insB st.2 _) z = (st.1 ++ [_]).any _
      rw [memB_insB hI.1, hI.2, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
        beq_comm' z, Bool.or_comm]
  · rw [cond_true, cond_true]
    exact ⟨rfl, hI⟩

theorem foldl_inv {n : Nat} {G : List Nat} {x : Nat} {w : List Nat} : ∀ (gs : List Nat)
    (st : List (Nat × List Nat) × List (List Nat)), InvB st →
    (gs.foldl (stepKB n G x w) st).1 = gs.foldl (stepKK n G x w) st.1 ∧
      InvB (gs.foldl (stepKB n G x w) st)
  | [], _, hI => ⟨rfl, hI⟩
  | k :: gs, st, hI => by
    obtain ⟨h1, h2⟩ := stepKB_inv (n := n) (G := G) (x := x) (w := w) hI k
    rw [List.foldl_cons, List.foldl_cons, ← h1]
    exact foldl_inv gs _ h2

theorem goKB_inv (n : Nat) (G : List Nat) : ∀ (fuel i : Nat)
    (st : List (Nat × List Nat) × List (List Nat)), InvB st →
    (goKB n G fuel i st).1 = goKK n G fuel i st.1
  | 0, _, _, _ => rfl
  | fuel + 1, i, st, hI => by
    rw [goKB, goKK]
    cases Nat.blt i st.1.length
    · rfl
    · obtain ⟨h1, h2⟩ := foldl_inv (n := n) (G := G) (x := (st.1.getD i (0, [])).1)
        (w := (st.1.getD i (0, [])).2) (List.range G.length) st hI
      show (goKB n G fuel (i + 1) _).1 = goKK n G fuel (i + 1) _
      rw [goKB_inv n G fuel (i + 1) _ h2, h1]

theorem invB_init (p : Nat) : InvB ([(p, [])], insB (List.replicate 37 []) p) := by
  refine ⟨by rw [insB_length, List.length_replicate], fun z => ?_⟩
  rw [memB_insB (List.length_replicate ..), memB_replicate, Bool.or_false, List.any_cons,
    List.any_nil, Bool.or_false, beq_comm']

@[expose] noncomputable def wordsOfKB (n : Nat) (G : List Nat) : List (List Nat) :=
  (goKB n G 2000 0 ([(pidK n, [])], insB (List.replicate 37 []) (pidK n))).1.map (·.2)

theorem wordsOfKK_eq : wordsOfKK = wordsOfKB := by
  funext n G
  unfold wordsOfKK wordsOfKB
  rw [goKB_inv n G 2000 0 _ (invB_init _)]

@[expose] noncomputable def enumOKKB (n : Nat) (G : List Nat) (L : List (List Nat)) : Bool :=
  let vals := L.map (wordKK n G)
  L.all (fun w => w.all (Nat.blt · G.length)) && L.contains [] &&
    (List.range G.length).all
      (fun k => vals.all fun v => memB (bucketsOf vals) (pmulKK n v (G.getD k 0))) &&
    allDistinctKK vals

theorem enumOKKK_eq : enumOKKK = enumOKKB := by
  funext n G L
  unfold enumOKKK enumOKKB
  simp only [← memN_eq_memB]

@[expose] noncomputable def p12CheckKB (n : Nat) : Bool :=
  let PG := (pGenSw.map (swapsArr n)).map enc
  let EG := (eGenSw.map (swapsArr n)).map enc
  let CG := (cGenSw.map (swapsArr n)).map enc
  let PW := wordsOfKB n PG
  let EW := wordsOfKB n EG
  let CW := wordsOfKB n CG
  let PV := PW.map (wordKK n PG)
  let EV := EW.map (wordKK n EG)
  pGenSw.all (swapsOK n) && eGenSw.all (swapsOK n) && cGenSw.all (swapsOK n) &&
    enumOKKB n PG PW && Nat.beq PW.length 512 && enumOKKB n EG EW && Nat.beq EW.length 64 &&
    enumOKKB n CG CW && Nat.beq CW.length 9 && elemAbOKKK n EG && EG.all (memN PV ·) &&
    order8OKKK n PG gWord && countOKKK n PV EV && CG.all (normOKKK n EV EG)

theorem p12CheckK_eqB (n : Nat) : p12CheckK n = p12CheckKB n := by
  rw [p12CheckK_eq]
  unfold p12CheckKK p12CheckKB
  rw [wordsOfKK_eq, enumOKKK_eq]

theorem all_take_drop {α : Type} (g : α → Bool) (l : List α) (k : Nat) :
    l.all g = ((l.take k).all g && (l.drop k).all g) := by
  rw [← List.all_append, List.take_append_drop]

@[expose] noncomputable def p12A (n : Nat) : Bool :=
  let PG := (pGenSw.map (swapsArr n)).map enc
  let EG := (eGenSw.map (swapsArr n)).map enc
  let CG := (cGenSw.map (swapsArr n)).map enc
  let PW := wordsOfKB n PG
  let EW := wordsOfKB n EG
  let CW := wordsOfKB n CG
  let PV := PW.map (wordKK n PG)
  pGenSw.all (swapsOK n) && eGenSw.all (swapsOK n) && cGenSw.all (swapsOK n) &&
    enumOKKB n PG PW && Nat.beq PW.length 512 && enumOKKB n EG EW && Nat.beq EW.length 64 &&
    enumOKKB n CG CW && Nat.beq CW.length 9 && elemAbOKKK n EG && EG.all (memN PV ·) &&
    order8OKKK n PG gWord

@[expose] noncomputable def p12B (n : Nat) : Bool :=
  let PG := (pGenSw.map (swapsArr n)).map enc
  let EG := (eGenSw.map (swapsArr n)).map enc
  let PV := (wordsOfKB n PG).map (wordKK n PG)
  let EV := (wordsOfKB n EG).map (wordKK n EG)
  (PV.take 256).all fun x =>
    Nat.beq x (pidK n) || !sqKK n x || memN EV x || countAtKK n PV x

@[expose] noncomputable def p12C (n : Nat) : Bool :=
  let PG := (pGenSw.map (swapsArr n)).map enc
  let EG := (eGenSw.map (swapsArr n)).map enc
  let CG := (cGenSw.map (swapsArr n)).map enc
  let PV := (wordsOfKB n PG).map (wordKK n PG)
  let EV := (wordsOfKB n EG).map (wordKK n EG)
  ((PV.drop 256).all fun x =>
    Nat.beq x (pidK n) || !sqKK n x || memN EV x || countAtKK n PV x) &&
    CG.all (normOKKK n EV EG)

theorem p12CheckKB_eq (n : Nat) : p12CheckKB n = (p12A n && p12B n && p12C n) := by
  simp only [p12CheckKB, p12A, p12B, p12C, countOKKK]
  rw [all_take_drop _ ((wordsOfKB n ((pGenSw.map (swapsArr n)).map enc)).map
    (wordKK n ((pGenSw.map (swapsArr n)).map enc))) 256]
  simp only [Bool.and_assoc]

end CFSG.KC.EvenSporP12

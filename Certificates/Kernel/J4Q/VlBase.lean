module

public import Certificates.Kernel.J4Q.C4007
public import Certificates.Kernel.J4Q.MaskU
public import Certificates.Kernel.J4Q.EtaMats
public import Certificates.Kernel.J4Q.VlData
public import Certificates.Kernel.J4Q.VlGD
public import Certificates.Kernel.J4Q.D4K
public import Certificates.Kernel.J4Q.VlK
public import CFSG.Certificates.Kernel.J4Q.RepVlTree
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Sporadic.J4.QT2

@[expose] noncomputable def vlTrip (k : Nat) : List Nat × Nat × Int :=
  (iTS k, if k < 192 then 0 else iPar k, if k < 192 then 0 else letters.getD (iLab k) 0)

theorem vlTree_eq : vlInvTree.toList = (List.range 43264).map vlTrip := by
  unfold vlInvTree
  exact vlTree_sound (s := 192) (PAR := iPar) (LAB := iLab) (TT := iTT) seeds_eq
    (by decide) (fun i hi j hj h => iTS_inj hi hj h) iset_tree iset_clos iset_ord iset_first (by decide)

theorem vlInv_size : vlInvTree.size = 43264 := by
  have h := congrArg List.length vlTree_eq
  simpa using h

theorem vlInv_get {k : Nat} (hk : k < 43264) : vlInvTree[k]! = vlTrip k := by
  have hs := vlInv_size
  rw [getElem!_pos vlInvTree k (by omega), ← Array.getElem_toList]
  have h := congrArg (fun l => l[k]?) vlTree_eq
  simp only [List.getElem?_map, List.getElem?_range hk, Option.map_some] at h
  rw [← Option.some_inj, ← h]
  simp [hs, hk]

theorem vlNodeOf_eq {k : Nat} (hk : k < 43264) : vlNodeOf (iTS k) = k := by
  have hd : (((List.range 43264).map vlTrip).map Prod.fst).Nodup := by
    rw [List.map_map]
    refine List.Nodup.map_on (fun i hi j hj h => iTS_inj (List.mem_range.1 hi) (List.mem_range.1 hj) h)
      List.nodup_range
  have h := vlNodeMap_sound vlTree_eq hd (k := k) (by simp [hk])
  simp only [List.getElem_map, List.getElem_range, vlTrip] at h
  unfold vlNodeOf
  rw [h]
  rfl

@[expose] noncomputable def seedK (s : List Nat) : Nat :=
  ((List.range 1024).find? fun e => mkTL.getD e [] == s).getD 0

@[expose] noncomputable def kelK (e : Nat) : List Int := (pcSeq e).flatMap fun i => mkKW.getD i []

@[expose] noncomputable def liftW : Nat → Nat → List Int
  | 0, _ => []
  | f + 1, k => if k < 192 then kelK (seedK (iTS k)) else
      letters.getD (iLab k) 0 :: (liftW f (iPar k) ++ [-(letters.getD (iLab k) 0)])

theorem find_congr {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
    rw [List.find?_cons, List.find?_cons, h x List.mem_cons_self,
      find_congr fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem seedIdx_eq (s : List Nat) : vlSeedIdx s = seedK s := by
  unfold vlSeedIdx seedK
  refine congrArg (Option.getD · 0) (find_congr fun e he => ?_)
  have he' := List.mem_range.1 he
  have h := congrArg (fun l => l.getD e []) tabL_eq
  simp only [tabL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range he',
    Option.map_some, Option.getD_some] at h
  rw [h, List.getD_eq_getElem?_getD]

theorem kel_eq (e : Nat) : vlKelWord e = kelK e := by
  unfold vlKelWord kelK
  rw [kWords_eq]

theorem letters_ne {i : Nat} (hi : i < 6) : letters.getD i 0 ≠ 0 := by
  rcases i with _ | _ | _ | _ | _ | _ | i
  all_goals first | decide | omega

theorem lift_eq : ∀ (f k : Nat), k < 43264 → vlLiftAux vlInvTree f k = liftW f k
  | 0, _, _ => rfl
  | f + 1, k, hk => by
    rw [vlLiftAux, vlInv_get hk]
    by_cases h : k < 192
    · simp [vlTrip, h, liftW, seedIdx_eq, kel_eq]
    · obtain ⟨hp, hl, -⟩ := iset_tree k (by omega) hk
      have hne : (letters.getD (iLab k) 0 == 0) = false := by
        have := letters_ne hl
        simpa using this
      simp only [vlTrip, h, ↓reduceIte, liftW, hne, Bool.false_eq_true]
      rw [lift_eq f (iPar k) (by omega)]

theorem vlLiftWord_eq {k : Nat} (hk : k < 43264) : vlLiftWord (iTS k) = liftW 200 k := by
  unfold vlLiftWord
  rw [vlNodeOf_eq hk, lift_eq 200 k hk]

theorem vlTables_chk : ((VGL.flatten.filter (· != idT)) ==
    (List.range 75).map fun j => iTS (getN 0 VLI j)) = true := by quickRfl

theorem vlTables_eq : vlTables = (List.range 75).map fun j => iTS (getN 0 VLI j) := by
  unfold vlTables
  rw [vGroups_eq]
  exact beq_iff_eq.1 vlTables_chk

theorem vli_chk : allR 75 (fun j => Nat.blt (getN 0 VLI j) 43264) = true := by quickRfl

theorem vli_lt {j : Nat} (hj : j < 75) : getN 0 VLI j < 43264 := lt_of_blt (allR_spec vli_chk j hj)

@[expose] noncomputable def vlJK (j : Nat) : Bool :=
  (fun w => andB (andB (w.all fun l => letters.contains l) (wordT w == iTS (getN 0 VLI j)))
    (Nat.beq (getN one VLS j) (wordJ c rm one G5 G5i w))) (liftW 200 (getN 0 VLI j))

@[expose] noncomputable def etaCK (c' : Nat) : Bool :=
  allR 64 fun j => Nat.beq (CFSG.KD.ETA.EF (Nat.add (Nat.mul 64 c') j)) (etaK c rm one Us (Nat.add (Nat.mul 64 c') j))

@[expose] noncomputable def QL : List (Nat × Nat) :=
  (List.range 75).flatMap fun j => (getL VLEL j).map fun e => (j, e)

@[expose] noncomputable def tKp (p : Nat) : Nat := (fun q => tK q.1 q.2) (QL.getD p (0, 0))

@[expose] noncomputable def gK (t : Nat) : List Nat :=
  (fun t1 => (fun t2 => d4SK t t1 t2 (cjK t2)) (cjK t1)) (cjK t)

@[expose] noncomputable def grpK (h : Nat) : List Nat :=
  (List.range 16).map fun m => CFSG.KD.VG.GDF (Nat.add (Nat.mul 16 h) m)

@[expose] noncomputable def distK (G : List Nat) : Bool :=
  allR 16 fun i => allR i fun j => notB (Nat.beq (getN one G i) (getN one G j))

@[expose] noncomputable def pairAtK (p : Nat) : Bool :=
  (fun t => (fun G => (fun h n => andB (distK G) (andB (Nat.blt h 132)
    (andB (G.all fun x => (grpK h).any (Nat.beq x))
      (andB (Nat.ble n 132) (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.blt h n) (andB (Nat.beq (getN 0 VLC (Nat.succ p)) n) ((grpK h).any (Nat.beq t))))
        (andB (Nat.beq h n) (andB (Nat.beq (getN 0 VLC (Nat.succ p)) (Nat.succ n))
          (andB (notB ((List.range n).any fun h' => (grpK h').any (Nat.beq t))) (G == grpK n))))
        (Nat.beq (getN 0 VLN p) 1)))))) (getN 0 VLH p) (getN 0 VLC p)) (gK t)) (tKp p)

@[expose] noncomputable def pairK (q : Nat) : Bool := allR 10 fun i => pairAtK (Nat.add (Nat.mul 10 q) i)

@[expose] noncomputable def pairH (h q : Nat) : Bool := pairK (Nat.add (Nat.mul 99 h) q)

@[expose] noncomputable def pair0 (q : Nat) : Bool := pairH 0 q

@[expose] noncomputable def pair1 (q : Nat) : Bool := pairH 1 q

end CertificateChecks.KernelJ4Q

end

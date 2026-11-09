module

public import Certificates.Data.Kernel.M24G.TrioSexts
public import Certificates.Kernel.M24G.TSData
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.SextData
public import Certificates.Data.Kernel.M24G.StmtB
import CFSG.Certificates.Kernel.M24G.StmtBSound
import CFSG.Certificates.Kernel.M24G.ListsSound
public import Certificates.Data.Kernel.M24G.Lists
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KC.M24G.TSC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

@[expose] def elemB (o : Nat) : List Nat → Bool
  | [] => false
  | x :: l => Nat.beq x o || elemB o l

theorem contains_eq_elemB (o : Nat) : ∀ l : List Nat, l.contains o = elemB o l
  | [] => rfl
  | x :: l => by
    have hb : (o == x) = Nat.beq x o := by
      rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
      exact eq_comm
    rw [List.contains_cons, elemB, contains_eq_elemB o l, hb]

private theorem ascL_of_pairwise : ∀ l : List Nat, l.Pairwise (· < ·) → ascL l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    simp only [ascL, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, ascL_of_pairwise (b :: l) h.of_cons⟩

theorem decide_pairwise_eq_ascL (l : List Nat) : decide (l.Pairwise (· < ·)) = ascL l := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact ⟨ascL_of_pairwise l, ascL_pairwise l⟩

@[expose] def tsRowsOKT (TL : List (Nat × Nat × Nat)) (OT : IxTree (List Nat))
    (TS : List (List Nat)) : Bool :=
  TL.length == 3795 && TS.length == 3795 && (TL.zip TS).all fun x =>
    x.2.length == 7 && ascL x.2 &&
      x.2.all fun q => decide (q < 1771) && (Native.octsT x.1).all fun o => elemB o (getT OT q)

private theorem getT_map_octsS (SL : List (List Nat)) (q : Nat) :
    getT (treeOf (SL.map Native.octsS)) q = Native.octsS (SL.getD q default) := by
  rw [getT_treeOf, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases SL[q]? <;> rfl

theorem tsRowsOK_eqT (TL : List (Nat × Nat × Nat)) (SL TS : List (List Nat)) :
    tsRowsOK TL SL TS = tsRowsOKT TL (treeOf (SL.map Native.octsS)) TS := by
  simp only [tsRowsOK, tsRowOK, tsRowsOKT, getT_map_octsS, Native.trioIn, contains_eq_elemB,
    decide_pairwise_eq_ascL]

theorem rows : tsRowsOK TL SL TS = true := by
  rw [tsRowsOK_eqT]
  quickRfl

end CFSG.KC.M24G.TSC

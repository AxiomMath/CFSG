module

public import Certificates.Data.Kernel.M24G.C311
public import Certificates.Data.Kernel.M24G.Lists
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.TSData
public import Certificates.Kernel.M24G.DualData
public import Certificates.Kernel.M24G.C311Data
public import Certificates.Data.Kernel.M24G.StmtB
import CFSG.Certificates.Kernel.M24G.StmtBSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.SliceGlue

set_option maxRecDepth 100000

public section

namespace CFSG.KC.M24G.C311C

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

set_option maxHeartbeats 0 in
theorem lu_ts : allIdx (fun i x => x.contains 0 == DualD.LU.contains i) TS 0 = true := by
  decide +kernel

theorem ts_length : TS.length = 3795 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ru_ok : DualD.LU.all (fun a => TS.toArray[a]! == tabRow DualD.LU C311D.RU a) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ds_ok : discsOvalsT DualD.LU (tabLU DualD.LU DualD.TU) = C311D.DS := by
  decide +kernel

theorem ds_len : C311D.DS.length = 21 := by decide +kernel

theorem a_ok_p0 : (SliceGlue.slice (TL.zip TS) (0 * 480) 480).all
    (c311A C311D.DS (tabRow DualD.LU C311D.RU) (tabLU DualD.LU DualD.TU)) = true := by
  quickRfl

theorem a_ok_p1 : (SliceGlue.slice (TL.zip TS) (1 * 480) 480).all
    (c311A C311D.DS (tabRow DualD.LU C311D.RU) (tabLU DualD.LU DualD.TU)) = true := by
  quickRfl

theorem a_ok_p2 : (SliceGlue.slice (TL.zip TS) (2 * 480) 480).all
    (c311A C311D.DS (tabRow DualD.LU C311D.RU) (tabLU DualD.LU DualD.TU)) = true := by
  quickRfl

theorem a_ok_p3 : (SliceGlue.slice (TL.zip TS) (3 * 480) 480).all
    (c311A C311D.DS (tabRow DualD.LU C311D.RU) (tabLU DualD.LU DualD.TU)) = true := by
  quickRfl

theorem a_ok_p4 : (SliceGlue.slice (TL.zip TS) (4 * 480) 480).all
    (c311A C311D.DS (tabRow DualD.LU C311D.RU) (tabLU DualD.LU DualD.TU)) = true := by
  quickRfl

theorem a_ok_p5 : (SliceGlue.slice (TL.zip TS) (5 * 480) 480).all
    (c311A C311D.DS (tabRow DualD.LU C311D.RU) (tabLU DualD.LU DualD.TU)) = true := by
  quickRfl

theorem a_ok_p6 : (SliceGlue.slice (TL.zip TS) (6 * 480) 480).all
    (c311A C311D.DS (tabRow DualD.LU C311D.RU) (tabLU DualD.LU DualD.TU)) = true := by
  quickRfl

theorem a_ok_p7 : (SliceGlue.slice (TL.zip TS) (7 * 480) 480).all
    (c311A C311D.DS (tabRow DualD.LU C311D.RU) (tabLU DualD.LU DualD.TU)) = true := by
  quickRfl

theorem a_ok : (TL.zip TS).all (c311A C311D.DS (tabRow DualD.LU C311D.RU)
    (tabLU DualD.LU DualD.TU)) = true :=
  SliceGlue.all_of_slices _ 480 8 _ (Nat.le_of_ble_eq_true (by quickRfl)) fun j hj => match j, hj with
    | 0, _ => a_ok_p0
    | 1, _ => a_ok_p1
    | 2, _ => a_ok_p2
    | 3, _ => a_ok_p3
    | 4, _ => a_ok_p4
    | 5, _ => a_ok_p5
    | 6, _ => a_ok_p6
    | 7, _ => a_ok_p7
    | _ + 8, h => absurd h (by omega)

@[expose] def nbOKT (T : IxTree (List Nat)) (d : Nat) (N : List Nat) (M : Nat) : Bool :=
  N.all (fun k => decide (k < 3795) && (k == d || (getT T d).any fun q => (getT T k).contains q)) &&
    N.foldr (fun k a => rowMask (getT T k) ||| a) 0 == M

@[expose] def nbsOKT (T : IxTree (List Nat)) (LU : List Nat) (NB : List (List Nat))
    (MS : List Nat) : Bool :=
  (LU.zip (NB.zip MS)).all fun x => nbOKT T x.1 x.2.1 x.2.2

private theorem getDnil_T (L : List (List Nat)) (i : Nat) : L.getD i [] = getT (treeOf L) i :=
  (getT_treeOf L i).symm

theorem nbsOK_eqT (TS : List (List Nat)) (LU : List Nat) (NB : List (List Nat)) (MS : List Nat) :
    nbsOK TS LU NB MS = nbsOKT (treeOf TS) LU NB MS := by
  simp only [nbsOK, nbOK, orRows, nbsOKT, nbOKT, getDnil_T]

set_option maxHeartbeats 0 in
theorem nb_ok : nbsOK TS DualD.LU C311D.NB C311D.MS = true := by
  rw [nbsOK_eqT]
  quickRfl

set_option maxHeartbeats 0 in
theorem b_ok : c311B C311D.DS (fun d => (tabNM DualD.LU C311D.NB C311D.MS d).2) = true := by
  decide +kernel

end CFSG.KC.M24G.C311C

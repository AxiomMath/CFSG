module

public import CFSG.Quasithin.H13.LocDblJ2CheckInputs
public import Certificates.Kernel.He589203.Q

public section

namespace CFSG.KD.J27031

open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.J2Cert
open CFSG.QuasithinUnique.K1.SporadicPerm (slpTabsA j2Prog)
open CFSG.KD.He589203 (lowB rowsOf cntOf orbOrder)

@[expose] def B3 : List Nat := [0, 4, 3]

@[expose] def D3 : DcData :=
  let e := bfsEnumL 315 B3 RT 200
  { j2D with
    B := B3
    rpar := e.1
    rlab := e.2
    Vs := vData.map fun V =>
      let e := bfsEnumL 315 B3 (RT ++ (V.1.map (tabW 315 AB)).toArray) (V.2 + 10)
      (V.1, e.1, e.2, V.2) }

@[expose] def sigOf (n r : Nat) (rows : Array (List Nat)) : Array Nat :=
  let keys := rows.map (keyNat n r)
  (Array.range rows.size).qsort fun a b => keys[a]! < keys[b]!

@[expose] def skOf (n r : Nat) (rows : Array (List Nat)) : Array Nat :=
  (sigOf n r rows).map fun i => keyNat n r rows[i]!

@[expose] def recOf (n : Nat) (B : List Nat) (G : Array (Array Nat)) (par lab : Array Nat)
    (sk : Array Nat) : Array (Array Nat) :=
  let r := B.length
  let rows := rowsOf B G par lab
  let keys := rows.map (keyNat n r)
  let M : Std.HashMap Nat Nat :=
    Std.HashMap.ofList ((List.range rows.size).map fun k => (keys[k]!, k))
  let sig := sigOf n r rows
  let sinv := invTab sig
  let cnt := cntOf par
  (Array.range rows.size).map fun k =>
    rows[k]!.toArray ++ #[par[k]!, lab[k]!, cnt[k]!, sig[k]!, sinv[k]!, lowB sk keys[k]! 0 sk.size] ++
      ((Array.range G.size).map fun t => M.getD (keyNat n r (rows[k]!.map (img (G[t]!)))) 0)

@[expose] def slp : Array (Array Nat) := slpTabsA ta tb j2Prog

@[expose] def perms : Array (Array Nat) :=
  let Q := orbOrder 315 RT
  #[invTab ta, invTab tb] ++ RT.map invTab ++ #[orbitLabels 315 RT, Q, invTab Q]

@[expose] def xtabs : Array (Array Nat) :=
  let D := D3
  (Array.range D.reps.size).map D.X ++ (Array.range D.reps.size).map D.Xi

@[expose] def recR : Array (Array Nat) := recOf 315 B3 RT D3.rpar D3.rlab #[]

@[expose] def skR : Array Nat := skOf 315 3 (rowsOf B3 RT D3.rpar D3.rlab)

@[expose] def recV : Array (Array (Array Nat)) :=
  let D := D3
  let V0 := D.Vs.headD ([], #[], #[], 0)
  let sk0 := skOf D.n 3 (rowsOf D.B (D.VG V0.1) V0.2.1 V0.2.2.1)
  (D.Vs.map fun V => recOf D.n D.B (D.VG V.1) V.2.1 V.2.2.1 sk0).toArray

@[expose] def recV0 : Array (Array Nat) := recV[0]!

@[expose] def recV1 : Array (Array Nat) := recV[1]!

@[expose] def cks (i j : Nat) : Array Nat :=
  let D := D3
  (conjKeys D.n D.B D.RT D.rpar D.rlab D.NR (D.Xi i) (D.X j)).toArray

@[expose] def hpos : Array (Array Nat) :=
  let D := D3
  let c := (Array.range D.reps.size).map fun j => cks j j
  (Array.range D.NR).map fun k => c.map fun ks => lowB skR ks[k]! 0 skR.size

@[expose] def invs : Array Nat :=
  let D := D3
  (Array.range D.reps.size).map fun j => dcInv D.n D.lb (D.X j)

@[expose] def prs : List (Nat × Nat) :=
  let m := D3.reps.size
  (List.range m).flatMap fun i => ((List.range m).filter fun j => i < j && invs[i]! == invs[j]!).map
    fun j => (i, j)

@[expose] def hposN : Array (Array Nat) :=
  (prs.map fun p => (cks p.1 p.2).map fun x => lowB skR x 0 skR.size).toArray

@[expose] def pidx : Array (Array Nat) :=
  #[(Array.range (63 * 63)).map fun x => (prs.idxOf? (x / 63, x % 63)).getD 0]

@[expose] def ih : Array (Array Nat) :=
  let D := D3
  #[invs, (Array.range D.reps.size).map fun j => hitCount D.rSet (cks j j).toList]

end CFSG.KD.J27031

end

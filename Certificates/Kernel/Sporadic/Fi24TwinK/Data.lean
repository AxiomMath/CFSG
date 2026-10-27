module

import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
public import Certificates.Kernel.Sporadic.Fi24Kit.Data
public import Certificates.Data.Kernel.Spor.Fi24TwinK

#kc_repo #kc_json_gz CFSG.KD.Fi24TwinK "Certificates/Kernel/Sporadic/Fi24TwinK/data/twin.json.gz" 67763 10588073203583119968 (m0 : Nat) (F0 : Nat) (hc0 : List (List Nat)) (hd0 : Nat) (bw0 : List (List Nat)) (bp0 : List Nat) (cd0 : List (Nat × Nat)) (lt0 : List Nat) (xt0 : List (List Nat)) (gw0 : List (List Nat)) (nw0 : List (List (List Nat))) (ab0 : Bool) (gt0 : List (List Nat)) (m1 : Nat) (F1 : Nat) (hc1 : List (List Nat)) (hd1 : Nat) (bw1 : List (List Nat)) (bp1 : List Nat) (cd1 : List (Nat × Nat)) (lt1 : List Nat) (xt1 : List (List Nat)) (gw1 : List (List Nat)) (nw1 : List (List (List Nat))) (ab1 : Bool) (gt1 : List (List Nat)) (m2 : Nat) (F2 : Nat) (hc2 : List (List Nat)) (hd2 : Nat) (bw2 : List (List Nat)) (bp2 : List Nat) (cd2 : List (Nat × Nat)) (lt2 : List Nat) (xt2 : List (List Nat)) (gw2 : List (List Nat)) (nw2 : List (List (List Nat))) (ab2 : Bool) (gt2 : List (List Nat))

public section

namespace CFSG.KD.Fi24TwinK

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO CFSG.KC.Fi24TwinK CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

@[expose] noncomputable def OL : Nat → Nat := CFSG.KD.Fi24Orb.OL

@[expose] noncomputable def wr (r : Nat) : List Nat :=
  nthL [] [[14, 16, 16, 14, 16, 16], [16, 19], [16]] r

@[expose] noncomputable def m (r : Nat) : Nat := nthL 0 [m0, m1, m2] r

@[expose] noncomputable def F (r : Nat) : Nat := nthL 0 [F0, F1, F2] r

@[expose] noncomputable def hc (r : Nat) : List (List Nat) := nthL [] [hc0, hc1, hc2] r

@[expose] noncomputable def hd (r : Nat) : Nat := nthL 0 [hd0, hd1, hd2] r

@[expose] noncomputable def bw (r : Nat) : List (List Nat) := nthL [] [bw0, bw1, bw2] r

@[expose] noncomputable def bp (r : Nat) : List Nat := nthL [] [bp0, bp1, bp2] r

@[expose] noncomputable def cd (r : Nat) : List (Nat × Nat) := nthL [] [cd0, cd1, cd2] r

@[expose] noncomputable def lt (r : Nat) : List Nat := nthL [] [lt0, lt1, lt2] r

@[expose] noncomputable def xt (r : Nat) : List (List Nat) := nthL [] [xt0, xt1, xt2] r

@[expose] noncomputable def gw (r : Nat) : List (List Nat) := nthL [] [gw0, gw1, gw2] r

@[expose] noncomputable def nw (r : Nat) : List (List (List Nat)) := nthL [] [nw0, nw1, nw2] r

@[expose] noncomputable def ab (r : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) ab2 ab1 (Nat.beq r 1)) ab0
    (Nat.beq r 0)

@[expose] noncomputable def gt (r : Nat) : List (List Nat) := nthL [] [gt0, gt1, gt2] r

@[expose] noncomputable def lw (r : Nat) : List (List Nat) := hc r ++ bw r

@[expose] noncomputable def c0 (r : Nat) : List (Nat × Nat) :=
  (0, nthL 0 (lt r) 0) ::
    List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => List.nil)
      (fun b _ ih k => (b, nthL 0 (lt r) (Nat.add (lenL (hc r)) k)) :: ih (Nat.succ k)) (bp r) 0

@[expose] noncomputable def cl (r : Nat) : List (Nat × Nat) := cBuild (m r) (c0 r) (cd r)

@[expose] noncomputable def fs (r : Nat) : Bool := fsOK NW NT (wr r) (m r) (F r)

@[expose] noncomputable def tb (r j : Nat) : Bool :=
  tabOK NW NT (m r) (F r) (dW (nthL [] (lw r) j)) (nthL 0 (lt r) j)

@[expose] noncomputable def pp (r : Nat) : Bool :=
  letB (plF (m r) (F r)) (fun P =>
    andB (allL (fun W => Nat.beq (bitN P (ptC NW NT W 0)) 1) (hc r))
    (andB (allI (fun k b => andB (Nat.blt b (m r)) (Nat.beq (pt (F r) b) (ptC NW NT (nthL [] (bw r) k) 0)))
        (bp r) 0)
    (andB (eqL (nthL [1] (hc r) 0) [])
    (andB (Nat.beq (lenL (lt r)) (lenL (lw r)))
    (andB (Nat.beq (lenL (nw r)) (lenL (hc r)))
    (andB (cdOK (Nat.succ (lenL (bp r))) (cd r))
    (andB (allL (fun u => allL (fun l => Nat.blt l (lenL (lt r))) u) (gw r))
      (allI (fun k b => eqL (nthL [] (gw r) k) [0, Nat.add (lenL (hc r)) k]) (bp r) 0))))))))

@[expose] noncomputable def cv (r : Nat) : Bool :=
  covW NW NT (List.map dW (hc r)) (hd r) (nat_lit 1) (Nat.xor ptsM (plF (m r) (F r)))

@[expose] noncomputable def ro (r : Nat) : Bool :=
  (fun C => allL (fun e => rowOK (m r) (nthP C 0).2 e.1 e.2) (List.tail C)) (cl r)

@[expose] noncomputable def k2 (r : Nat) : Bool := k2OK NW NT (m r) (F r) (xt r) (cl r)

@[expose] noncomputable def nm (r : Nat) : Bool := nmChk (m r) (lt r) (gw r) (nw r)

@[expose] noncomputable def c2 (r : Nat) : Bool := c2Chk (m r) (lt r) (gw r) (ab r)

@[expose] noncomputable def cj (r : Nat) : Bool := gtOK NW NT (F r) (cl r) (gt r)

@[expose] noncomputable def ev : List Nat := [8, 10, 12, 14, 16, 18, 20, 22, 24]

@[expose] noncomputable def evf : Bool :=
  allL (fun l => andB (Nat.beq (letN NW l 0) 0) (Nat.beq (letN NW l 305530) 305530)) ev

@[expose] noncomputable def tbA (j : Nat) : Bool := tb 0 j

@[expose] noncomputable def tbB (j : Nat) : Bool := tb 1 j

@[expose] noncomputable def tbC (j : Nat) : Bool := tb 2 j

end CFSG.KD.Fi24TwinK

end

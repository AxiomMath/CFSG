module

import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
public import Certificates.Kernel.Sporadic.Fi24Kit.Data
public import Certificates.Data.Kernel.Spor.Fi24ThreeO

#kc_repo #kc_json_gz CFSG.KD.Fi24ThreeO "Certificates/Kernel/Sporadic/Fi24ThreeO/data/three.json.gz" 111113 14396093497518190497(tw0 : List (List Nat)) (gq0 : List (Nat × List Nat)) (gp0 : List (List Nat × List Nat)) (en0 : List Nat) (ep0 : List (Nat × Nat × Nat)) (tw1 : List (List Nat)) (gq1 : List (Nat × List Nat)) (gp1 : List (List Nat × List Nat)) (en1 : List Nat) (ep1 : List (Nat × Nat × Nat)) (tw2 : List (List Nat)) (gq2 : List (Nat × List Nat)) (gp2 : List (List Nat × List Nat)) (en2 : List Nat) (ep2 : List (Nat × Nat × Nat)) (tw3 : List (List Nat)) (gq3 : List (Nat × List Nat)) (gp3 : List (List Nat × List Nat)) (en3 : List Nat) (ep3 : List (Nat × Nat × Nat)) (hr : List Nat) (hd : Nat) (lk : List Nat) (sw : List (List Nat)) (cd : Nat) (cr : List (Nat × Nat × Nat × Nat)) (bk : List Nat) (bl : List Nat) (fb : List (Nat × Nat))
#kc_repo #kc_ktree_gz CFSG.KD.Fi24ThreeO PQT "Certificates/Kernel/Sporadic/Fi24ThreeO/data/pq.bin.gz" 65536 1 65536 1665215730234253558

public section

namespace CFSG.KD.Fi24ThreeO

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

@[expose] noncomputable def OL : Nat → Nat := CFSG.KD.Fi24Orb.OL

@[expose] noncomputable def nthD {α : Type} (d : α) (l : List α) (i : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun a _ ih j => Nat.rec (motive := fun _ => α) a (fun k _ => ih k) j) l i

@[expose] noncomputable def wr (r : Nat) : List Nat :=
  nthD [] [[18], [16, 19], [14, 16, 16, 14, 16, 16], [16]] r

@[expose] noncomputable def yr (r : Nat) : Nat := nIf(Nat.beq r (nat_lit 2), nat_lit 14069, nat_lit 221549)

@[expose] noncomputable def tw (r : Nat) : List (List Nat) := nthD [] [tw0, tw1, tw2, tw3] r

@[expose] noncomputable def gq (r : Nat) : List (Nat × List Nat) := nthD [] [gq0, gq1, gq2, gq3] r

@[expose] noncomputable def gp (r : Nat) : List (List Nat × List Nat) := nthD [] [gp0, gp1, gp2, gp3] r

@[expose] noncomputable def en (r : Nat) : List Nat := nthD [] [en0, en1, en2, en3] r

@[expose] noncomputable def ep (r : Nat) : List (Nat × Nat × Nat) := nthD [] [ep0, ep1, ep2, ep3] r

@[expose] noncomputable def fx (r : Nat) : Bool :=
  andB (allL (fun b => Nat.beq (ptC NW NT (wr r) b) b) [nat_lit 0, nat_lit 305530, nat_lit 5604, yr r])
    (notB (Nat.beq (ptC NW NT (wr r) (nat_lit 1)) (nat_lit 1)))

@[expose] noncomputable def cu (r : Nat) : Bool := cubeOK NW NT (wr r)

@[expose] noncomputable def sp (r : Nat) : Bool := sepOK NW NT OL (wr r) (tw r) (gq r)

@[expose] noncomputable def gn (r : Nat) : Bool := gensOK NW NT OL (wr r) (gp r) (en r) (ep r)

@[expose] noncomputable def lv3 : List Nat := [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

@[expose] noncomputable def lv : Bool := orbOK NW lv3 (nat_lit 5) (nat_lit 14069) (nat_lit 1152)

@[expose] noncomputable def G1 : List Nat :=
  [25, 16, 25, 17, 13, 14, 24, 12, 16, 11, 20, 13, 10, 9, 4, 17, 6, 12, 8, 0, 22, 0, 19]

@[expose] noncomputable def eps : List (List Nat) := [
  [24, 19, 21, 19, 15, 24, 17, 13, 14, 14, 10, 21, 14, 20, 13],
  [25, 23, 17, 25, 12, 14, 16, 24, 14, 10, 15, 25, 12, 20],
  [16, 21, 18, 20, 12, 15, 19, 20, 15, 18, 10, 10, 19, 20, 14],
  [24, 17, 24, 15, 23, 19, 14, 22, 9, 9, 18, 15, 18],
  [25, 20, 19, 12, 14, 14, 14, 23, 13, 19, 8, 12, 17, 10, 24],
  [24, 20, 22, 20, 12, 17, 13, 14, 24, 17, 8, 8, 16, 18, 25]]

@[expose] noncomputable def xw : List Nat := G1 ++ (2 :: invC G1)

@[expose] noncomputable def hw : List (List Nat) := eps ++ [xw]

@[expose] noncomputable def epsW (i : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) (invC (nthD [] eps (Nat.sub i (nat_lit 6)))) (nthD [] eps i)
    (Nat.blt i (nat_lit 6))

@[expose] noncomputable def epsL (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun i _ ih => epsW i ++ ih) l

@[expose] noncomputable def swC : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) [xw] (fun l _ ih => epsL l :: ih) sw

@[expose] noncomputable def PQ : Nat := PQT (nat_lit 0)

@[expose] noncomputable def gfr (S : Nat) : Nat := wkC NW NT (invC G1) S

@[expose] noncomputable def sP (x : Nat) : Nat := letN NW (nat_lit 2) x

@[expose] noncomputable def inQ (x : Nat) : Bool := Nat.beq (clsK OL NT x (sP x)) (sP x)

@[expose] noncomputable def cuF : Bool := cubeOK NW NT [nat_lit 2]

@[expose] noncomputable def fpf : Bool := Nat.beq (fixC NW NT [nat_lit 2]) (nat_lit 0)

@[expose] noncomputable def base : List Nat := [0, 305530, 5604, 221549, 266275, 186844]

@[expose] noncomputable def hc (j : Nat) : Bool :=
  allL (fun b =>
    Nat.beq (ptC NW NT (invC G1 ++ (nthD [] eps j ++ (G1 ++ [nat_lit 2]))) b)
      (ptC NW NT (nat_lit 2 :: (invC G1 ++ (nthD [] eps j ++ G1))) b)) base

@[expose] noncomputable def hcov : Bool := covW NW NT hw hd (gfr (plOf hr)) (nat_lit 0)

@[expose] noncomputable def hq : Bool :=
  allI (fun i r => letB (nIf(Nat.blt i (nat_lit 3), nat_lit 1, nat_lit 0)) (fun b =>
    andB (Nat.beq (bitN PQ r) b) (bIf(Nat.beq b (nat_lit 1), inQ r, notB (inQ r))))) hr (nat_lit 0)

@[expose] noncomputable def lks : Bool :=
  andB (allI (fun i k => andB (Nat.beq (bitN PQ k) (nat_lit 1))
    (Nat.beq (uP NW OL NT k (nat_lit 12)) (nthD 0 hr (Nat.succ i)))) lk (nat_lit 0))
    (andB (Nat.beq (lenL lk) (nat_lit 2)) (Nat.beq (nthD 0 hr 0) (nat_lit 12)))

@[expose] noncomputable def qcl : Bool :=
  andB (Nat.beq (Nat.land PQ ptsM) PQ) (closW NW NT hw (gfr PQ))

@[expose] noncomputable def cst (j : Nat) : Bool :=
  letB (ptC NW NT (invC G1 ++ (nthD [] swC j ++ G1)) (nat_lit 12)) (fun y =>
    orB (Nat.beq y (nat_lit 12)) (orB (Nat.beq y (sP (nat_lit 12))) (Nat.beq y (sP (sP (nat_lit 12))))))

@[expose] noncomputable def crx : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun c _ ih => c.1 :: ih) cr

@[expose] noncomputable def cF : Nat :=
  Nat.lor (Nat.xor ptsM (Nat.land PQ ptsM)) (plOf [nat_lit 12, sP (nat_lit 12), sP (sP (nat_lit 12))])

@[expose] noncomputable def ccov : Bool := covW NW NT swC cd (gfr (Nat.lor (plOf crx) cF)) (gfr cF)

@[expose] noncomputable def ct (i : Nat) : Bool :=
  (fun c : Nat × Nat × Nat × Nat =>
    bIf(Nat.beq c.2.2.2 (nat_lit 306936),
      cycK (fun q => uP NW OL NT (nat_lit 12) (uP NW OL NT c.1 q)) c.2.1 c.2.2.1,
      andB (Nat.beq (bitN PQ c.2.2.2) (nat_lit 1))
        (cycK (fun q => uP NW OL NT (nat_lit 12) (uP NW OL NT c.1 (uP NW OL NT c.2.2.2
          (uP NW OL NT (nat_lit 12) (uP NW OL NT c.1 (uP NW OL NT c.2.2.2 q)))))) c.2.1 c.2.2.1)))
    (nthD (0, 0, 0, 0) cr i)

@[expose] noncomputable def uC (W : List Nat) : List Nat :=
  dW W ++ (dW (nat_lit 2 :: W) ++ dW (nat_lit 2 :: nat_lit 2 :: W))

@[expose] noncomputable def bg : Bool :=
  andB (Nat.beq (bitN PQ (ptC NW NT bk (nat_lit 0))) (nat_lit 1))
    (andB (Nat.beq (bitN PQ (ptC NW NT bl (nat_lit 0))) (nat_lit 1))
      (offOK NW NT (uC bk ++ uC bl) [nat_lit 2] PQ))

@[expose] noncomputable def bs (i : Nat) : Bool :=
  (fun e : Nat × Nat => andB (andB (Nat.beq (bitN PQ e.1) (nat_lit 1)) (Nat.beq (bitN PQ e.2) (nat_lit 1)))
    (Nat.beq (clsK OL NT e.1 e.2) (nthD 0 base i))) (nthD (0, 0) fb i)

end CFSG.KD.Fi24ThreeO

end

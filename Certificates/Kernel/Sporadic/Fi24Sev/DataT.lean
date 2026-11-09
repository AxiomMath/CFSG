module

public import Certificates.Kernel.Sporadic.Fi24Sev.Data
public import Certificates.Kernel.Sporadic.Fi24Net.PTabSound

public section

namespace CFSG.KD.Fi24Sev

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev CFSG.KD.Fi24Net

@[expose] noncomputable def apCT (NT : Nat → Nat) (c x : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 26), ptF NT x, letPT c x)

@[expose] noncomputable def ptCT (NT : Nat → Nat) (cs : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun c _ ih => strictN ih (apCT NT c)) cs

@[expose] noncomputable def refOKT (NT OL : Nat → Nat) (w : List Nat) (To q : Nat)
    (c : List (Nat × Nat) × Nat × Nat × Nat) : Bool :=
  letB (cfgP OL NT c.1 c.2.2.2
      (Nat.land To (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul c.2.2.2 (nat_lit 20))) (nat_lit 1))))
    (fun Zo => letB (cfgP OL NT c.1 c.2.2.2 (tupA (ptCT NT w) c.2.2.2 (nat_lit 0) q (nat_lit 0)))
      (fun Zq => andB (Nat.beq (getP Zq c.2.1) (getP Zq c.2.2.1))
        (notB (Nat.beq (getP Zo c.2.1) (getP Zo c.2.2.1)))))

@[expose] noncomputable def refsOKT (NT OL : Nat → Nat) (w : List Nat) (om : Nat)
    (reps : List Nat) (rf : List (List (Nat × Nat) × Nat × Nat × Nat)) : Bool :=
  letB (tupP (ptCT NT w) om) (fun To =>
    allI (fun i c => refOKT NT OL w To (nthD (nat_lit 0) reps i) c) rf (nat_lit 0))

@[expose] noncomputable def slOKT (NT : Nat → Nat) (sl : List (Nat × List Nat × List Nat)) : Bool :=
  allL (fun e => andB
      (allL (fun z => andB (Nat.ble (nat_lit 2) z) (orB (Nat.ble z (nat_lit 5))
        (andB (Nat.blt (Nat.sub (Nat.shiftRight z (nat_lit 1)) (nat_lit 3)) e.1)
          (hasU sl (Nat.sub (Nat.shiftRight z (nat_lit 1)) (nat_lit 3)))))) e.2.1)
      (allL (fun b => Nat.beq (ptCT NT (expU sl e.2.1) b) (ptCT NT e.2.2 b)) cb)) sl

@[expose] noncomputable def relOKT (NT : Nat → Nat) (w : List Nat) (hs : List (List Nat)) : Bool :=
  andB (allL (fun b => Nat.beq (itN (ptCT NT w) (nat_lit 7) b) b) cb)
    (allL (fun h => allL (fun b => Nat.beq (ptCT NT (h ++ w) b) (ptCT NT (w ++ h) b)) cb) hs)

theorem ptCT_eq : ptCT = ptC NW := by
  funext NT cs x
  unfold ptCT ptC apCT apC
  rw [letPT_eq]

theorem refOKT_eq : refOKT = refOK NW := by
  funext NT OL w To q c
  unfold refOKT refOK
  rw [ptCT_eq]

theorem refsOKT_eq : refsOKT = refsOK NW := by
  funext NT OL w om reps rf
  unfold refsOKT refsOK
  rw [ptCT_eq, refOKT_eq]

theorem relOKT_eq : relOKT = relOK NW := by
  funext NT w hs
  unfold relOKT relOK
  rw [ptCT_eq]

theorem slOKT_eq : slOKT = slOK NW := by
  funext NT sl
  unfold slOKT slOK
  rw [ptCT_eq]

end CFSG.KD.Fi24Sev

end

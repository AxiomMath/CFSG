module

public import Certificates.Kernel.HS799102.ClassData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

open CFSG.KC.PCent

theorem walkK_append (A : Nat → Nat → Nat) (g N root : Nat) (T : PTree Rec) :
    ∀ (l1 l2 : List Rec) (lo : Nat), walkK A g N root T (l1 ++ l2) lo =
      (walkK A g N root T l1 lo &&
        walkK A g N root T l2 (l1.foldl (fun _ r => Nat.add r.1 1) lo))
  | [], l2, lo => (Bool.true_and _).symm
  | r :: l1, l2, lo => by
    have ih := walkK_append A g N root T l1 l2 (Nat.add r.1 1)
    show (Nat.ble lo r.1 && recK A g N root r (getT T r.2.2.2) &&
        walkK A g N root T (l1 ++ l2) (Nat.add r.1 1)) =
      ((Nat.ble lo r.1 && recK A g N root r (getT T r.2.2.2) &&
        walkK A g N root T l1 (Nat.add r.1 1)) &&
        walkK A g N root T l2 (l1.foldl (fun _ r => Nat.add r.1 1) (Nat.add r.1 1)))
    simp only [ih, Bool.and_assoc]

theorem walkK_split (A : Nat → Nat → Nat) (g N root : Nat) (T : PTree Rec) (L : List Rec)
    (m lo : Nat) : walkK A g N root T L lo = (walkK A g N root T (L.take m) lo &&
      walkK A g N root T (L.drop m) ((L.take m).foldl (fun _ r => Nat.add r.1 1) lo)) := by
  have h := walkK_append A g N root T (L.take m) (L.drop m) lo
  rwa [List.take_append_drop] at h

@[expose] def nxt (l : List Rec) (lo : Nat) : Nat := l.foldl (fun _ r => Nat.add r.1 1) lo

theorem classK_of4 {n w : Nat} {G GI : Nat → Nat} {ngen v : Nat} {R : List Rec} (m : Nat)
    (hA : CFSG.KC.Enum.allN ngen (fun k => Nat.beq (GI k) (CFSG.KS.pinvS n w (CFSG.KS.mask w) (G k)))
      = true)
    (h0 : walkK (conjI n w G GI) ngen R.length v (treeOf R) (R.take m) (nat_lit 0) = true)
    (h1 : walkK (conjI n w G GI) ngen R.length v (treeOf R) ((R.drop m).take m)
      (nxt (R.take m) (nat_lit 0)) = true)
    (h2 : walkK (conjI n w G GI) ngen R.length v (treeOf R) (((R.drop m).drop m).take m)
      (nxt ((R.drop m).take m) (nxt (R.take m) (nat_lit 0))) = true)
    (h3 : walkK (conjI n w G GI) ngen R.length v (treeOf R) (((R.drop m).drop m).drop m)
      (nxt (((R.drop m).drop m).take m) (nxt ((R.drop m).take m) (nxt (R.take m) (nat_lit 0))))
        = true) :
    classK n w G GI ngen v R = true := by
  unfold classK orbRecK
  rw [hA, Bool.true_and, walkK_split _ _ _ _ _ R m, walkK_split _ _ _ _ _ (R.drop m) m,
    walkK_split _ _ _ _ _ ((R.drop m).drop m) m]
  simp only [nxt] at h1 h2 h3
  simp only [h0, h1, h2, h3, Bool.and_self]

theorem c3A : CFSG.KC.Enum.allN 4
    (fun k => Nat.beq (pGI k) (CFSG.KS.pinvS 100 7 (CFSG.KS.mask 7) (pG k))) = true := by quickRfl

theorem c3w0 : walkK (conjI 100 7 pG pGI) 4 R3.length (TH.F 4) (treeOf R3) (R3.take 3850)
    (nat_lit 0) = true := by
  quickRfl

theorem c3w1 : walkK (conjI 100 7 pG pGI) 4 R3.length (TH.F 4) (treeOf R3) ((R3.drop 3850).take 3850)
    (nxt (R3.take 3850) (nat_lit 0)) = true := by
  quickRfl

theorem c3w2 : walkK (conjI 100 7 pG pGI) 4 R3.length (TH.F 4) (treeOf R3)
    (((R3.drop 3850).drop 3850).take 3850)
    (nxt ((R3.drop 3850).take 3850) (nxt (R3.take 3850) (nat_lit 0))) = true := by
  quickRfl

theorem c3w3 : walkK (conjI 100 7 pG pGI) 4 R3.length (TH.F 4) (treeOf R3)
    (((R3.drop 3850).drop 3850).drop 3850)
    (nxt (((R3.drop 3850).drop 3850).take 3850) (nxt ((R3.drop 3850).take 3850)
      (nxt (R3.take 3850) (nat_lit 0)))) = true := by
  quickRfl

theorem ch799102_c3 : classK 100 7 pG pGI 4 (TH.F 4) R3 = true :=
  classK_of4 3850 c3A c3w0 c3w1 c3w2 c3w3

end CertificateChecks.KernelHS799102

end

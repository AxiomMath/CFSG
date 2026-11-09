module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Data.Kernel.SporCov.LaneKit
public import Certificates.Data.Kernel.SporCov.PcCl
public import CFSG.Certificates.Kernel.Orders.Mat
public import CFSG.Certificates.Kernel.Fam.HNSeed.Data.Sel

#kc_repo #kc_json CFSG.KD.SporCovLane.HN.D "Certificates/Kernel/SporCovLane/data/hn3.json"
  13737503 7960157270505975640
  (Ws : List (List Nat))
  (HA : List (List Nat)) (RlA : List (List Nat)) (TA : List Nat) (MA : List (List Nat))
  (YA : List (List Nat)) (HcA : List (List Nat)) (YcA : List (List Nat)) (KA : List Nat)
  (CA : List (List Nat)) (RA : List (List Nat))
  (HB : List (List Nat)) (RlB : List (List Nat)) (TB : List Nat) (MB : List (List Nat))
  (YB : List (List Nat)) (HcB : List (List Nat)) (YcB : List (List Nat)) (KB : List Nat)
  (CB : List (List Nat)) (RB : List (List Nat))
  (RT : List (List (List Nat × Nat)))
  (TT : List (List Nat × Nat × List (List Nat × Nat)))

set_option Elab.async false

public section

namespace CFSG.KD.SporCovLane.HN

open CFSG.KC.SporCov CFSG.KC.Ord

noncomputable abbrev mul : Nat → Nat → Nat :=
  mulR 5 13 1729 133 9 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H CFSG.KD.FamHNSeed.CM
    CFSG.KD.FamHNSeed.RM

@[expose] noncomputable def chk (mw : List Nat → Nat) : Bool :=
  pccOK (eqM mw) letT 3 4 4 2 2 D.HA D.RlA D.TA D.MA D.YA D.HcA D.YcA D.CA D.RA D.KA &&
    pccOK (eqM mw) letT 3 3 4 2 2 D.HB D.RlB D.TB D.MB D.YB D.HcB D.YcB D.CB D.RB D.KB &&
    !Nat.beq (Nat.mod (trR 13 1729 133 (mw D.TA)) 5) (Nat.mod (trR 13 1729 133 (mw D.TB)) 5)

namespace Rec

@[expose] def chainT (x : Nat) : List (List Nat × Nat) → List (List Nat × Nat × Nat)
  | [] => []
  | (w, y) :: r => (w, x, y) :: chainT y r

@[expose] def lastV (x : Nat) : List (List Nat × Nat) → Nat
  | [] => x
  | (_, y) :: r => lastV y r

@[expose] def lk (T : List (List Nat × Nat × List (List Nat × Nat))) (d : List Nat → Nat)
    (u : List Nat) : Nat :=
  match T with
  | [] => d u
  | t :: r => cond (u == t.1) t.2.1 (lk r d u)

@[expose] def tOK (one : Nat) (t : List Nat × Nat × List (List Nat × Nat)) : Bool :=
  (t.1 == t.2.2.flatMap Prod.fst) && Nat.beq (lastV one t.2.2) t.2.1

theorem strictN_eq (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem forceR_eq (x : Nat) (k : Nat → Bool) : forceR x k = k x := by
  cases x <;> rfl

theorem mwLn_append (mul : Nat → Nat → Nat) (lt : Nat → Nat) :
    ∀ (u v : List Nat) (x : Nat), mwLn mul lt (u ++ v) x = mwLn mul lt v (mwLn mul lt u x)
  | [], _, _ => rfl
  | c :: u, v, x => by
    change CFSG.KC.Loop.strictN (mul (lt c) x) (mwLn mul lt (u ++ v)) =
      mwLn mul lt v (CFSG.KC.Loop.strictN (mul (lt c) x) (mwLn mul lt u))
    rw [strictN_eq, strictN_eq]
    exact mwLn_append mul lt u v _

theorem chain_sound (mul : Nat → Nat → Nat) (lt : Nat → Nat) :
    ∀ (x : Nat) (L : List (List Nat × Nat)),
      (∀ c ∈ chainT x L, mwLn mul lt c.1 c.2.1 = c.2.2) →
      mwLn mul lt (L.flatMap Prod.fst) x = lastV x L
  | _, [], _ => rfl
  | x, (w, y) :: r, h => by
    rw [List.flatMap_cons, mwLn_append, h (w, x, y) (by simp [chainT])]
    exact chain_sound mul lt y r fun c hc => h c (by simp [chainT, hc])

theorem tab_sound (mul : Nat → Nat → Nat) (lt : Nat → Nat) (one : Nat)
    (T : List (List Nat × Nat × List (List Nat × Nat)))
    (hc : ∀ c ∈ T.flatMap fun t => chainT one t.2.2, mwLn mul lt c.1 c.2.1 = c.2.2)
    (ht : T.all (tOK one) = true) : ∀ t ∈ T, mwLn mul lt t.1 one = t.2.1 := by
  intro t htT
  have h1 := List.all_eq_true.1 ht t htT
  simp only [tOK, Bool.and_eq_true, beq_iff_eq] at h1
  rw [h1.1, chain_sound mul lt one _ fun c hc' => hc c (List.mem_flatMap.2 ⟨t, htT, hc'⟩)]
  exact Nat.eq_of_beq_eq_true h1.2

theorem lk_eq (T : List (List Nat × Nat × List (List Nat × Nat))) (d : List Nat → Nat)
    (h : ∀ t ∈ T, d t.1 = t.2.1) (u : List Nat) : lk T d u = d u := by
  induction T with
  | nil => rfl
  | cons t r ih =>
    unfold lk
    cases hu : (u == t.1)
    · exact ih fun s hs => h s (List.mem_cons_of_mem _ hs)
    · rw [beq_iff_eq] at hu
      rw [hu]
      exact (h t List.mem_cons_self).symm

theorem regR_eq (mul : Nat → Nat → Nat) (ONE A Ai B Bi : Nat) :
    ∀ (Ws : List (List Nat)) (k : List Nat → Bool),
      regR mul ONE A Ai B Bi Ws k = k (Ws.map fun w => mwLn mul (let4 A Ai B Bi) w ONE)
  | [], _ => rfl
  | w :: Ws, k => by
    change forceR (mwLn mul (let4 A Ai B Bi) w ONE)
      (fun x => regR mul ONE A Ai B Bi Ws fun xs => k (x :: xs)) = _
    rw [forceR_eq, regR_eq mul ONE A Ai B Bi Ws]
    rfl

theorem regs_sound (mul : Nat → Nat → Nat) (lt : Nat → Nat) (one : Nat)
    (R : List (List (List Nat × Nat)))
    (hc : ∀ c ∈ R.flatMap (chainT one), mwLn mul lt c.1 c.2.1 = c.2.2) :
    (R.map fun L => L.flatMap Prod.fst).map (fun w => mwLn mul lt w one) = R.map (lastV one) := by
  rw [List.map_map]
  exact List.map_congr_left fun L hL =>
    chain_sound mul lt one L fun c hc' => hc c (List.mem_flatMap.2 ⟨L, hL, hc'⟩)

theorem mem_of_lt {α : Type} {l : List α} {n : Nat} (hn : l.length = n) (d : α) {P : α → Prop}
    (h : ∀ i < n, P (l.getD i d)) : ∀ c ∈ l, P c := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have := h i (hn ▸ hi)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this

noncomputable abbrev A : Nat := CFSG.KD.FamHNSeed.RW 1

noncomputable abbrev B : Nat := CFSG.KD.FamHNSeed.RW 2

noncomputable abbrev Bi : Nat := mul B B

noncomputable abbrev ONE : Nat := CFSG.KD.FamHNSeed.ONE

@[expose] noncomputable def Rg : List Nat := D.RT.map (lastV ONE)

@[expose] noncomputable def CR : List (List Nat × Nat × Nat) := D.RT.flatMap (chainT ONE)

@[expose] noncomputable def CT : List (List Nat × Nat × Nat) :=
  D.TT.flatMap fun t => chainT ONE t.2.2

@[expose] noncomputable def cR (i : Nat) : Bool :=
  (fun c : List Nat × Nat × Nat => Nat.beq (mwLn mul (let4 A A B Bi) c.1 c.2.1) c.2.2)
    (CR.getD i ([], 0, 0))

@[expose] noncomputable def cT (i : Nat) : Bool :=
  (fun c : List Nat × Nat × Nat =>
    Nat.beq (mwLn mul (letLn A A B Bi ONE Rg) c.1 c.2.1) c.2.2) (CT.getD i ([], 0, 0))

theorem kitLn_of (mul : Nat → Nat → Nat) (ONE MA MAi MB MBi : Nat) (Ws : List (List Nat))
    (k : (List Nat → Nat) → Bool) (R : List Nat) (h1 : Nat.beq (mul MA MAi) ONE = true)
    (h2 : Nat.beq (mul MB MBi) ONE = true)
    (hR : Ws.map (fun w => mwLn mul (let4 MA MAi MB MBi) w ONE) = R)
    (hk : k (fun u => mwLn mul (letLn MA MAi MB MBi ONE R) u ONE) = true) :
    kitLn mul ONE MA MAi MB MBi Ws k = true := by
  unfold kitLn
  rw [forceR_eq, forceR_eq, forceR_eq, forceR_eq, h1, h2, Bool.true_and, Bool.true_and, regR_eq, hR]
  exact hk

theorem nR : CR.length = 39 := by decide +kernel

theorem nT : CT.length = 103 := by decide +kernel

theorem kAA : Nat.beq (mul A A) ONE = true := by quickRfl

theorem kBB : Nat.beq (mul B Bi) ONE = true := by quickRfl

theorem kWs : (D.Ws == D.RT.map fun L => L.flatMap Prod.fst) = true := by quickRfl

theorem kTT : D.TT.all (tOK ONE) = true := by quickRfl

#kc_each CFSG.KD.SporCovLane.HN.Rec r cR 0 39

#kc_each CFSG.KD.SporCovLane.HN.Rec t cT 0 103

#kc_forall_tree allR (fun i => cR i = true) 39 CFSG.KD.SporCovLane.HN.Rec.r

#kc_forall_tree allT (fun i => cT i = true) 103 CFSG.KD.SporCovLane.HN.Rec.t

theorem hR : ∀ c ∈ CR, mwLn mul (let4 A A B Bi) c.1 c.2.1 = c.2.2 :=
  mem_of_lt nR ([], 0, 0) fun i hi => by
    have h := allR i hi
    unfold cR at h
    exact Nat.eq_of_beq_eq_true h

theorem hT : ∀ c ∈ CT, mwLn mul (letLn A A B Bi ONE Rg) c.1 c.2.1 = c.2.2 :=
  mem_of_lt nT ([], 0, 0) fun i hi => by
    have h := allT i hi
    unfold cT at h
    exact Nat.eq_of_beq_eq_true h

theorem hRg : D.Ws.map (fun w => mwLn mul (let4 A A B Bi) w ONE) = Rg := by
  rw [beq_iff_eq.1 kWs]
  exact regs_sound mul _ ONE D.RT hR

theorem hTab : ∀ t ∈ D.TT, mwLn mul (letLn A A B Bi ONE Rg) t.1 ONE = t.2.1 :=
  tab_sound mul _ ONE D.TT hT kTT

theorem kChk : chk (lk D.TT fun u => mwLn mul (letLn A A B Bi ONE Rg) u ONE) = true := by
  quickRfl

theorem hChk : chk (fun u => mwLn mul (letLn A A B Bi ONE Rg) u ONE) = true := by
  have e : (fun u => mwLn mul (letLn A A B Bi ONE Rg) u ONE) =
      lk D.TT (fun u => mwLn mul (letLn A A B Bi ONE Rg) u ONE) :=
    funext fun u => (lk_eq D.TT (fun u => mwLn mul (letLn A A B Bi ONE Rg) u ONE) hTab u).symm
  rw [e]
  exact kChk

end Rec

namespace Ck

theorem ok : kitLn mul CFSG.KD.FamHNSeed.ONE (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 1)
    (CFSG.KD.FamHNSeed.RW 2) (mul (CFSG.KD.FamHNSeed.RW 2) (CFSG.KD.FamHNSeed.RW 2)) D.Ws chk =
      true :=
  Rec.kitLn_of mul Rec.ONE Rec.A Rec.A Rec.B Rec.Bi D.Ws chk Rec.Rg Rec.kAA Rec.kBB Rec.hRg
    Rec.hChk

end Ck

end CFSG.KD.SporCovLane.HN

end

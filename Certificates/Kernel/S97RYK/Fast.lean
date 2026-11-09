module

public import Certificates.Data.Kernel.S97RYK
public import CFSG.Certificates.Kernel.F2Orb24Sound

public section

namespace CFSG.KC.S97RYK

open CFSG.KC.Enum CFSG.KC.LQT.PW CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75.WCCheck
open CFSG.LargeExtraspecial.S11.PairCheck
open CFSG.KC.F2Orb24 (BT mem)

@[expose] noncomputable def memT (y : Nat) (E : List Nat) (T : BT) : Bool :=
  Bool.rec (motive := fun _ => Bool) (memK E y) (CFSG.KC.F2Orb24.memK (nat_lit 45) T y) (Nat.blt y (nat_lit 35184372088832))

@[expose] noncomputable def insT (y : Nat) (T : BT) : BT :=
  Bool.rec (motive := fun _ => BT) T (CFSG.KC.F2Orb24.insK (nat_lit 45) y T) (Nat.blt y (nat_lit 35184372088832))

@[expose] noncomputable def stepX2 (n x : Nat) (gs : List Nat) : List Nat → BT → List Nat →
    (List Nat → BT → List Nat → List Nat × BT) → List Nat × BT :=
  List.rec (motive := fun _ => List Nat → BT → List Nat → (List Nat → BT → List Nat → List Nat × BT) →
      List Nat × BT) (fun E T F k => k E T F)
    (fun s _ ih E T F k => strictK (mulK n x s) fun y =>
      bIfK (memT y E T) (ih E T F k) (ih (y :: E) (insT y T) (y :: F) k)) gs

@[expose] noncomputable def stepFr2 (n : Nat) (gs fr : List Nat) : List Nat → BT → List Nat →
    (List Nat → BT → List Nat → List Nat × BT) → List Nat × BT :=
  List.rec (motive := fun _ => List Nat → BT → List Nat → (List Nat → BT → List Nat → List Nat × BT) →
      List Nat × BT) (fun E T F k => k E T F)
    (fun x _ ih E T F k => stepX2 n x gs E T F fun E T F => ih E T F k) fr

@[expose] noncomputable def closeK2 (n : Nat) (gs : List Nat) (fuel : Nat) : List Nat → BT → List Nat → List Nat × BT :=
  Nat.rec (motive := fun _ => List Nat → BT → List Nat → List Nat × BT) (fun E T _ => (E, T))
    (fun _ ih E T fr => stepFr2 n gs fr E T [] fun E T F =>
      List.rec (motive := fun _ => List Nat × BT) (E, T) (fun _ _ _ => ih E T F) F) fuel

@[expose] def InvT (E : List Nat) (T : BT) : Prop := ∀ v < 2 ^ 45, mem 45 v T = memK E v

@[expose] def RelT (p : List Nat × BT) (l : List Nat) : Prop := p.1 = l ∧ InvT p.1 p.2

theorem strictK_eq2 {α : Type} (y : Nat) (k : Nat → α) : strictK y k = k y := by
  cases y <;> rfl

theorem bIfK_eqT {α : Type} (c : Bool) (t e : α) : bIfK c t e = if c = true then t else e := by
  cases c <;> rfl

theorem memK_consT (a : Nat) (E : List Nat) (y : Nat) : memK (a :: E) y = (Nat.beq a y || memK E y) := by
  show Bool.rec (motive := fun _ => Bool) (memK E y) true (Nat.beq a y) = _
  cases Nat.beq a y <;> rfl

theorem invT_nil : InvT [] .nil := fun v _ => CFSG.KS.F2Orb24.mem_nil 45 v

theorem memT_eq {E : List Nat} {T : BT} (h : InvT E T) (y : Nat) : memT y E T = memK E y := by
  unfold memT
  cases hb : Nat.blt y (nat_lit 35184372088832)
  · rfl
  · rw [CFSG.KS.F2Orb24.memK_eq]
    have hy : y < 35184372088832 := Eq.mp Nat.blt_eq hb
    exact h y hy

theorem invT_cons {E : List Nat} {T : BT} (h : InvT E T) (y : Nat) : InvT (y :: E) (insT y T) := by
  intro v hv
  rw [memK_consT]
  unfold insT
  cases hb : Nat.blt y (nat_lit 35184372088832)
  · have hy : ¬ y < 2 ^ 45 := by
      rw [show (2 : Nat) ^ 45 = 35184372088832 from rfl, ← Nat.blt_eq, hb]
      exact Bool.false_ne_true
    have : Nat.beq y v = false := by
      cases e : Nat.beq y v
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e ▸ hv) hy
    rw [this, Bool.false_or]
    exact h v hv
  · have hy : y < 2 ^ 45 := by
      rw [show (2 : Nat) ^ 45 = 35184372088832 from rfl, ← Nat.blt_eq]
      exact hb
    show mem 45 v (CFSG.KC.F2Orb24.insK 45 y T) = _
    rw [CFSG.KS.F2Orb24.insK_eq, CFSG.KS.F2Orb24.mem_ins, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hy,
      h v hv]
    congr 1
    cases e : Nat.beq y v
    · simp only [decide_eq_false_iff_not]; intro h'; rw [h', Nat.beq_refl] at e; exact Bool.noConfusion e
    · simp only [decide_eq_true_eq]; exact (Nat.eq_of_beq_eq_true e).symm

theorem stepX2_R (n x : Nat) : ∀ (gs E : List Nat) (T : BT) (F : List Nat)
    (k : List Nat → List Nat → List Nat) (k2 : List Nat → BT → List Nat → List Nat × BT),
    InvT E T → (∀ E' T' F', InvT E' T' → RelT (k2 E' T' F') (k E' F')) →
    RelT (stepX2 n x gs E T F k2) (stepX n x gs E F k)
  | [], E, T, F, k, k2, hI, hk => hk E T F hI
  | s :: gs, E, T, F, k, k2, hI, hk => by
    show RelT (strictK (mulK n x s) fun y => bIfK (memT y E T) (stepX2 n x gs E T F k2)
      (stepX2 n x gs (y :: E) (insT y T) (y :: F) k2)) (stepX n x (s :: gs) E F k)
    rw [stepX, strictK_eq2, strictK_eq2, bIfK_eqT, bIfK_eqT, memT_eq hI]
    split
    · exact stepX2_R n x gs E T F k k2 hI hk
    · exact stepX2_R n x gs _ _ _ k k2 (invT_cons hI _) hk

theorem stepFr2_R (n : Nat) (gs : List Nat) : ∀ (fr E : List Nat) (T : BT) (F : List Nat)
    (k : List Nat → List Nat → List Nat) (k2 : List Nat → BT → List Nat → List Nat × BT),
    InvT E T → (∀ E' T' F', InvT E' T' → RelT (k2 E' T' F') (k E' F')) →
    RelT (stepFr2 n gs fr E T F k2) (stepFr n gs fr E F k)
  | [], E, T, F, k, k2, hI, hk => hk E T F hI
  | x :: fr, E, T, F, k, k2, hI, hk => by
    show RelT (stepX2 n x gs E T F fun E T F => stepFr2 n gs fr E T F k2) (stepFr n gs (x :: fr) E F k)
    rw [stepFr]
    exact stepX2_R n x gs E T F _ _ hI fun E' T' F' h' => stepFr2_R n gs fr E' T' F' k k2 h' hk

theorem closeK2_R (n : Nat) (gs : List Nat) : ∀ (fuel : Nat) (E : List Nat) (T : BT) (fr : List Nat),
    InvT E T → RelT (closeK2 n gs fuel E T fr) (closeK n gs fuel E fr)
  | 0, E, T, _, hI => ⟨rfl, hI⟩
  | fuel + 1, E, T, fr, hI => by
    show RelT (stepFr2 n gs fr E T [] fun E T F =>
      List.rec (motive := fun _ => List Nat × BT) (E, T) (fun _ _ _ => closeK2 n gs fuel E T F) F)
      (closeK n gs (fuel + 1) E fr)
    rw [closeK]
    refine stepFr2_R n gs fr E T [] _ _ hI fun E' T' F' h' => ?_
    cases F' with
    | nil => exact ⟨rfl, h'⟩
    | cons a F' => exact closeK2_R n gs fuel E' T' (a :: F') h'

@[expose] noncomputable def properK2 (D : Data) (fuel : Nat) (J : List Bool) (c out : List Int) :
    Bool :=
  let gs := tabU D J ++ tabUc D J c
  let gsP := gs.map (encK D.n)
  let idP := encK D.n (idT D.n)
  let p := closeK2 D.n gsP fuel [idP] (insT idP .nil) [idP]
  decide (D.n < 32) && gs.all (validT D.n) && validT D.n (wT D out) && memT idP p.1 p.2 &&
    (p.1.all fun x => gsP.all fun s => memT (mulK D.n x s) p.1 p.2) &&
    !memT (encK D.n (wT D out)) p.1 p.2

@[expose] noncomputable def pverdictK2 (P : PData) (idP : Nat) (pcP : List Nat) (J : List Bool) :
    PVerdict → Bool
  | .size => (idxU P.D J).length + 1 != P.ord
  | .notClosed i j => (idxU P.D J).contains i && (idxU P.D J).contains j &&
      !memUK P.D idP pcP J (mulK P.D.n (eltK P.D.n idP pcP i) (eltK P.D.n idP pcP j))
  | .bad t y g =>
      let gP := wK P.D g
      let giP := wK P.D (invWord g)
      (idxU P.D J).contains t && (idxU P.D J).contains y &&
      !Nat.beq (eltK P.D.n idP pcP t) idP &&
      ((idP :: (idxU P.D J).map (eltK P.D.n idP pcP)).all fun u =>
        commK P.D.n (mulK P.D.n (mulK P.D.n gP u) giP) (eltK P.D.n idP pcP t)) &&
      !memUK P.D idP pcP J (mulK P.D.n (mulK P.D.n gP (eltK P.D.n idP pcP y)) giP)
  | .good c nIdx out =>
      strictK (wK P.D c) fun cP => strictK (wK P.D (invWord c)) fun ciP =>
      forceL ((idP :: (idxU P.D J).map (eltK P.D.n idP pcP)).map fun u =>
          mulK P.D.n (mulK P.D.n cP u) ciP) fun Uc =>
      (idxU P.D J).length + 1 == P.ord && nIdx.length == P.nCount &&
      decide nIdx.Nodup && (nIdx.all fun i => (idxU P.D J).contains i) &&
      ((idxU P.D J).all fun i => nIdx.contains i ==
        Uc.all fun t => memK Uc (mulK P.D.n (mulK P.D.n (eltK P.D.n idP pcP i) t)
          (eltK P.D.n idP pcP i))) &&
      (!P.proper || properK2 P.D P.fuel J c out)

@[expose] noncomputable def pairCheckK2 (P : PData) : Bool :=
  let D := P.D
  let n := D.n
  decide (n < 32) && decide (2 ≤ P.ord) &&
  strictK (encK n (idT n)) fun idP =>
  forceL (D.pc.map (wK D)) fun pcP =>
  forceL (D.pc.map fun w => wK D (invWord w)) fun pciP =>
  forceL ((List.range (2 ^ D.pc.length)).map (eltK n idP pcP)) fun SP =>
  forceL (SP.map (invW n 5)) fun SiP =>
  forceL (D.cw.map (wK D)) fun cwP =>
  forceL (D.cw.map fun w => wK D (invWord w)) fun cwiP =>
  forceL ((D.cls.flatMap fun c => c.map Prod.fst).map (eltK n idP pcP)) fun clP =>
  strictK (eltK n idP pcP D.zIdx) fun zP =>
  baseK D idP pcP pciP SP SiP cwP cwiP clP zP &&
    (allMasks D.cls.length).all fun J => P.pv.any fun p => p.1 == J && pverdictK2 P idP pcP J p.2

theorem properK_eq2 : properK = properK2 := by
  funext D fuel J c out
  unfold properK properK2
  dsimp only
  obtain ⟨h1, h2⟩ := closeK2_R D.n ((tabU D J ++ tabUc D J c).map (encK D.n)) fuel
    [encK D.n (idT D.n)] (insT (encK D.n (idT D.n)) .nil) [encK D.n (idT D.n)] (invT_cons invT_nil _)
  simp only [memT_eq h2]
  rw [h1]

theorem pverdictK_eq2 : pverdictK = pverdictK2 := by
  funext P idP pcP J v
  cases v <;> simp only [pverdictK, pverdictK2, properK_eq2]

theorem pairCheckK_eq2 (P : PData) : pairCheckK P = pairCheckK2 P := by
  unfold pairCheckK pairCheckK2
  rw [pverdictK_eq2]

end CFSG.KC.S97RYK

end

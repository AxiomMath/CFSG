module

public import Certificates.Kernel.O8Twin.PChecks
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PcompFacts
import all Init.Data.List.SplitOn.Basic
meta import Certificates.Kernel.O8Twin.PData
meta import Certificates.Kernel.SporSch.Mathieu.Gen
meta import Certificates.Data.S7TwinO8

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8Twin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.KS.M11 CFSG.KS.SporSch.MBT CFSG.KC.KGC31P CFSG.KC.S7TwinK
open Certificates.S7TwinO8

meta def gens8 : Array (Array Nat) := (rootL.map List.toArray).toArray

meta def rqA : List (List Nat) := RSL.map Array.toList

meta def rqB : List (List Nat) := RSL.map fun r => (CFSG.KS.SporSch.MOCG.invA r).toList

meta def rqC : List (List Nat) := RSL.map fun r => (CFSG.KS.SporSch.MOCG.comp r r).toList

meta def candA : List (Array Nat) := (candWords ()).map (CFSG.KS.SporSch.MOCG.evalW 120 gens8)

meta def cqA : List (List Nat) := candA.map Array.toList

meta def cqB : List (List Nat) := candA.map fun c => (CFSG.KS.SporSch.MOCG.invA c).toList

meta def spA : List (List Nat) :=
  let X := CFSG.KS.SporSch.MOCG.evalW 120 gensT [2, 1, 2, 3, 2, 4, 2, 1, 2, 3, 2, 4]
  let Y := CFSG.KS.SporSch.MOCG.evalW 120 gensT [1, 3, 2, 1, 2, 4, 2, 1, 3, 2, 1, 4, 2]
  [id120, CFSG.KS.SporSch.MOCG.comp X X, X, CFSG.KS.SporSch.MOCG.invA X, Y,
    CFSG.KS.SporSch.MOCG.invA Y, CFSG.KS.SporSch.MOCG.comp X Y,
    CFSG.KS.SporSch.MOCG.comp Y X].map Array.toList

meta def perRepOM : List (List Nat) :=
  [[2, 0, 1], [2, 1, 0], [2, 1, 0], [1, 0], [1, 0], [1, 0], [1, 0], [1, 2, 3, 0], [5, 4], [7, 6],
    [8], [], [1, 0], [1, 0], [1], [2, 1], [1, 0], [1, 0], [1], [1, 2, 9], [], [], [5, 4], [8],
    [10], [], [5, 4], [8], [], [11], [], [], [], [], [5], [7, 6], [10], [], [5], [7, 6], [], [11],
    [], [], [], [], [5, 4], [], [10], [11], [5, 4], [5, 4], [], [], [], [], []]

meta def rqE : List (List Nat) := (List.range RSL.length).map fun i =>
  let R := RSL[i]!
  let RR := CFSG.KS.SporSch.MOCG.comp R R
  let Ri := CFSG.KS.SporSch.MOCG.invA R
  (perRepOM.getD i []).flatMap fun j =>
    let C := candA.getD j id120
    let Ci := CFSG.KS.SporSch.MOCG.invA C
    ([id120, RR, R, Ri].map fun t =>
      CFSG.KS.SporSch.MOCG.comp (CFSG.KS.SporSch.MOCG.comp C t) Ci).flatMap Array.toList

end CertificateChecks.KernelO8Twin

#kss_packs CertificateChecks.KernelO8Twin.RA 7 CertificateChecks.KernelO8Twin.rqA
#kss_packs CertificateChecks.KernelO8Twin.RE 7 CertificateChecks.KernelO8Twin.rqE
#kss_packs CertificateChecks.KernelO8Twin.RB 7 CertificateChecks.KernelO8Twin.rqB
#kss_packs CertificateChecks.KernelO8Twin.RC 7 CertificateChecks.KernelO8Twin.rqC
#kss_packs CertificateChecks.KernelO8Twin.CA 7 CertificateChecks.KernelO8Twin.cqA
#kss_packs CertificateChecks.KernelO8Twin.CB 7 CertificateChecks.KernelO8Twin.cqB
#kss_packs CertificateChecks.KernelO8Twin.SP 7 CertificateChecks.KernelO8Twin.spA

namespace CertificateChecks.KernelO8Twin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.KS.M11 CFSG.KS.SporSch.MBT CFSG.KC.KGC31P CFSG.KC.S7TwinK
open Certificates.S7TwinO8

@[expose] noncomputable def forceL : List Nat → (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun a _ ih k => strictB a (fun a' => ih (fun t => k (a' :: t))))

@[expose] def rot2 (L : List Nat) : List Nat := L.drop 2 ++ L.take 2

@[expose] noncomputable def ppairWitZ (n w : Nat) (sp0 sp : List Nat) (RR C Ci : Nat) : Bool :=
  forceL (sp.map (pcj n w C Ci)) fun J => J.all (pmem sp0) ||
    (J.any (fun x => !pmem sp x) && sp.any (fun a => pmem J a && !psqOne n w a)) ||
    (pmem J RR && sp.all (fun a => !pmem J a || psqOne n w a) &&
      (rot2 sp).any fun k => (rot2 J).any fun v => !Nat.beq (pc n w k v) (pc n w v k))

@[expose] noncomputable def canonQ (w R Y Yi : Nat) : Bool :=
  bAnd(Nat.ble (pg w (mask w) Y 0) (pg w (mask w) Yi 0),
    bAnd(Nat.ble (pg w (mask w) Y 0) (pg w (mask w) R (pg w (mask w) Y 0)),
      Nat.ble (pg w (mask w) Y 0) (pg w (mask w) Y (pg w (mask w) R 0))))

@[expose] noncomputable def prepZ (n w : Nat) (sp0 : List Nat) (R Ri RR Y Y2 : Nat)
    (cands : List (Nat × Nat)) : Bool :=
  bIf(Nat.beq RR Y2, bIf(canonQ w R Y (pinv n w Y),
    strictB (pc n w R Y) (fun RY => bIf(Nat.beq RY (pc n w Y Ri),
      forceL [pidn n w, RR, R, Ri, Y, pinv n w Y, RY, pc n w Y R]
        (fun sp => cands.any fun c => ppairWitZ n w sp0 sp RR c.1 c.2), true)), true), true)

@[expose] noncomputable def allZ (n w : Nat) (sp0 : List Nat) (Y Y2 : Nat) :
    List Nat → List Nat → List Nat → List (List (Nat × Nat)) → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List (List (Nat × Nat)) → Bool)
    (fun _ _ _ => true)
    (fun R _ ih B C D => List.rec (motive := fun _ => Bool) true (fun Ri B' _ =>
      List.rec (motive := fun _ => Bool) true (fun RR C' _ =>
        List.rec (motive := fun _ => Bool) true (fun cs D' _ =>
          bAnd(prepZ n w sp0 R Ri RR Y Y2 cs, ih B' C' D')) D) C) B)

@[expose] noncomputable def candsZ : List (List (Nat × Nat)) :=
  perRep.map (List.map fun j => (lget CA j, lget CB j))

@[expose] def perRepO : List (List Nat) :=
  [[2, 0, 1], [2, 1, 0], [2, 1, 0], [1, 0], [1, 0], [1, 0], [1, 0], [1, 2, 3, 0], [5, 4], [7, 6],
    [8], [], [1, 0], [1, 0], [1], [2, 1], [1, 0], [1, 0], [1], [1, 2, 9], [], [], [5, 4], [8],
    [10], [], [5, 4], [8], [], [11], [], [], [], [], [5], [7, 6], [10], [], [5], [7, 6], [], [11],
    [], [], [], [], [5, 4], [], [10], [11], [5, 4], [5, 4], [], [], [], [], []]

@[expose] noncomputable def candsO : List (List (Nat × Nat)) :=
  perRepO.map (List.map fun j => (lget CA j, lget CB j))

theorem kRA : RA = repsK := by decide +kernel

theorem kRB : RB = RA.map (pinv 120 7) := by decide +kernel

theorem kRC : RC = RA.map (fun R => pc 120 7 R R) := by decide +kernel

theorem kSP : SP = sp0K := by decide +kernel

theorem kCZ : candsZ = candsK := by decide +kernel

theorem kPO : List.Forall₂ List.Perm perRepO perRep := by decide +kernel

theorem any_perm {l l' : List (Nat × Nat)} (h : l.Perm l') (f : Nat × Nat → Bool) :
    l.any f = l'.any f := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  exact ⟨fun ⟨x, hx, e⟩ => ⟨x, h.mem_iff.1 hx, e⟩, fun ⟨x, hx, e⟩ => ⟨x, h.mem_iff.2 hx, e⟩⟩

theorem any_map_perm (g : Nat → Nat × Nat) : ∀ {L' L : List (List Nat)}, List.Forall₂ List.Perm L' L →
    List.Forall₂ (fun x y => ∀ f : Nat × Nat → Bool, x.any f = y.any f)
      (L'.map (List.map g)) (L.map (List.map g))
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (fun f => any_perm (h.map g) f) (any_map_perm g t)

theorem candsO_any :
    List.Forall₂ (fun x y => ∀ f : Nat × Nat → Bool, x.any f = y.any f) candsO candsZ :=
  any_map_perm _ kPO

theorem strictB_eqZ (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem forceL_eq : ∀ (L : List Nat) (k : List Nat → Bool), forceL L k = k L
  | [], _ => rfl
  | a :: L, k => by
    change strictB a (fun a' => forceL L (fun t => k (a' :: t))) = _
    rw [strictB_eqZ, forceL_eq L]

theorem any_rot2 (L : List Nat) (f : Nat → Bool) : (rot2 L).any f = L.any f := by
  conv_rhs => rw [← List.take_append_drop 2 L]
  rw [rot2, List.any_append, List.any_append, Bool.or_comm]

theorem ppairWitZ_eq (n w : Nat) (sp0 sp : List Nat) (R C Ci : Nat) :
    ppairWitZ n w sp0 sp (pc n w R R) C Ci = ppairWit n w sp0 sp R C Ci := by
  unfold ppairWitZ ppairWit
  rw [forceL_eq]
  have h1 : ∀ J : List Nat, (fun a => pmem J a && !psqOne n w a) =
      (fun a => !psqOne n w a && pmem J a) := fun J => funext fun a => Bool.and_comm _ _
  have h2 : ∀ J : List Nat, (fun a => !pmem J a || psqOne n w a) =
      (fun a => psqOne n w a || !pmem J a) := fun J => funext fun a => Bool.or_comm _ _
  simp only [any_rot2]
  rw [h1, h2]

theorem prepZ_eq (n w : Nat) (sp0 : List Nat) (R Y : Nat) (cs : List (Nat × Nat)) :
    prepZ n w sp0 R (pinv n w R) (pc n w R R) Y (pc n w Y Y) cs =
      (!canonQ w R Y (pinv n w Y) || prepY n w sp0 R cs Y) := by
  unfold prepZ prepY pq8Pair
  rw [strictB_eqZ, forceL_eq]
  simp only [ppairWitZ_eq]
  cases canonQ w R Y (pinv n w Y) <;> cases Nat.beq (pc n w R R) (pc n w Y Y) <;>
    cases Nat.beq (pc n w R Y) (pc n w Y (pinv n w R)) <;> rfl

theorem prepY_any (n w : Nat) (sp0 : List Nat) (R Y : Nat) {cs' cs : List (Nat × Nat)}
    (h : ∀ f : Nat × Nat → Bool, cs'.any f = cs.any f) :
    prepY n w sp0 R cs' Y = prepY n w sp0 R cs Y := by
  unfold prepY
  rw [h]

theorem allZ_eq (n w : Nat) (sp0 : List Nat) (Y : Nat) :
    ∀ (A : List Nat) (D' D : List (List (Nat × Nat))),
      List.Forall₂ (fun x y => ∀ f : Nat × Nat → Bool, x.any f = y.any f) D' D →
      allZ n w sp0 Y (pc n w Y Y) A (A.map (pinv n w)) (A.map fun R => pc n w R R) D' =
        (A.zip D).all fun p => !canonQ w p.1 Y (pinv n w Y) || prepY n w sp0 p.1 p.2 Y
  | [], _, _, _ => rfl
  | _ :: _, [], [], .nil => rfl
  | R :: A, cs' :: D', cs :: D, .cons hc h => by
    simp only [List.zip_cons_cons, List.all_cons]
    rw [← allZ_eq n w sp0 Y A D' D h, ← prepY_any n w sp0 R Y hc, ← prepZ_eq n w sp0 R Y cs']
    change bAnd(prepZ n w sp0 R (pinv n w R) (pc n w R R) Y (pc n w Y Y) cs', _) = _
    cases prepZ n w sp0 R (pinv n w R) (pc n w R R) Y (pc n w Y Y) cs' <;> rfl

@[expose] noncomputable def fld840 (E k : Nat) : Nat :=
  Nat.land (Nat.shiftRight E (Nat.mul k 840)) (mask 840)

@[expose] noncomputable def ppairWitE (n w : Nat) (sp0 sp : List Nat) (RR C Ci E : Nat) : Bool :=
  forceL (fld840 E 0 :: fld840 E 1 :: fld840 E 2 :: fld840 E 3 :: (sp.drop 4).map (pcj n w C Ci))
    fun J => J.all (pmem sp0) ||
    (J.any (fun x => !pmem sp x) && sp.any (fun a => pmem J a && !psqOne n w a)) ||
    (pmem J RR && sp.all (fun a => !pmem J a || psqOne n w a) &&
      (rot2 sp).any fun k => (rot2 J).any fun v => !Nat.beq (pc n w k v) (pc n w v k))

@[expose] noncomputable def anyE (f : Nat → Nat → Bool) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun j _ ih E => bIf(f j E, true, ih (Nat.shiftRight E 3360)))

@[expose] noncomputable def chkE (n w : Nat) (CA CB : List Nat) (a0 a1 a2 a3 : Nat) :
    List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun j _ ih E => bAnd(Nat.beq (fld840 E 0) (pcj n w (lget CA j) (lget CB j) a0),
      bAnd(Nat.beq (fld840 E 1) (pcj n w (lget CA j) (lget CB j) a1),
      bAnd(Nat.beq (fld840 E 2) (pcj n w (lget CA j) (lget CB j) a2),
      bAnd(Nat.beq (fld840 E 3) (pcj n w (lget CA j) (lget CB j) a3),
        ih (Nat.shiftRight E 3360))))))

@[expose] noncomputable def prepE (n w : Nat) (sp0 CA CB : List Nat) (R Ri RR Y Y2 Yi : Nat)
    (js : List Nat) (E : Nat) : Bool :=
  bIf(Nat.beq RR Y2, bIf(canonQ w R Y Yi, bIf(Nat.beq (pg w (mask w) R (pg w (mask w) Y 0))
      (pg w (mask w) Y (pg w (mask w) Ri 0)),
    strictB (pc n w R Y) (fun RY => bIf(Nat.beq RY (pc n w Y Ri),
      forceL [pidn n w, RR, R, Ri, Y, Yi, RY, pc n w Y R]
        (fun sp => anyE (fun j E' => ppairWitE n w sp0 sp RR (lget CA j) (lget CB j) E') js E),
      true)), true), true), true)

@[expose] noncomputable def allE (n w : Nat) (sp0 CA CB : List Nat) (Y Y2 Yi : Nat) :
    List Nat → List Nat → List Nat → List (List Nat) → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List (List Nat) → List Nat → Bool)
    (fun _ _ _ _ => true)
    (fun R _ ih B C D L => List.rec (motive := fun _ => Bool) true (fun Ri B' _ =>
      List.rec (motive := fun _ => Bool) true (fun RR C' _ =>
        List.rec (motive := fun _ => Bool) true (fun js D' _ =>
          List.rec (motive := fun _ => Bool) true (fun E L' _ =>
            bAnd(bIf(Nat.beq RR Y2, prepE n w sp0 CA CB R Ri RR Y Y2 Yi js E, true),
              ih B' C' D' L')) L) D) C) B)

@[expose] noncomputable def chkAll (n w : Nat) (CA CB : List Nat) :
    List Nat → List Nat → List Nat → List (List Nat) → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List (List Nat) → List Nat → Bool)
    (fun _ _ _ _ => true)
    (fun R _ ih B C D L => List.rec (motive := fun _ => Bool) true (fun Ri B' _ =>
      List.rec (motive := fun _ => Bool) true (fun RR C' _ =>
        List.rec (motive := fun _ => Bool) true (fun js D' _ =>
          List.rec (motive := fun _ => Bool) false (fun E L' _ =>
            bAnd(chkE n w CA CB (pidn n w) RR R Ri js E, ih B' C' D' L')) L) D) C) B)

theorem kRE : chkAll 120 7 CA CB RA RB RC perRepO RE = true := by decide +kernel

theorem ppairWitE_eq (n w : Nat) (sp0 : List Nat) (a0 a1 a2 a3 : Nat) (rest : List Nat)
    (RR C Ci E : Nat) (h0 : fld840 E 0 = pcj n w C Ci a0) (h1 : fld840 E 1 = pcj n w C Ci a1)
    (h2 : fld840 E 2 = pcj n w C Ci a2) (h3 : fld840 E 3 = pcj n w C Ci a3) :
    ppairWitE n w sp0 (a0 :: a1 :: a2 :: a3 :: rest) RR C Ci E =
      ppairWitZ n w sp0 (a0 :: a1 :: a2 :: a3 :: rest) RR C Ci := by
  unfold ppairWitE ppairWitZ
  rw [h0, h1, h2, h3]
  rfl

theorem anyE_eq (n w : Nat) (CA CB : List Nat) (a0 a1 a2 a3 : Nat) (f : Nat → Nat → Bool)
    (g : Nat → Bool)
    (hfg : ∀ j E, fld840 E 0 = pcj n w (lget CA j) (lget CB j) a0 →
      fld840 E 1 = pcj n w (lget CA j) (lget CB j) a1 →
      fld840 E 2 = pcj n w (lget CA j) (lget CB j) a2 →
      fld840 E 3 = pcj n w (lget CA j) (lget CB j) a3 → f j E = g j) :
    ∀ (js : List Nat) (E : Nat), chkE n w CA CB a0 a1 a2 a3 js E = true → anyE f js E = js.any g
  | [], _, _ => rfl
  | j :: js, E, h => by
    have h' : bAnd(Nat.beq (fld840 E 0) (pcj n w (lget CA j) (lget CB j) a0),
        bAnd(Nat.beq (fld840 E 1) (pcj n w (lget CA j) (lget CB j) a1),
        bAnd(Nat.beq (fld840 E 2) (pcj n w (lget CA j) (lget CB j) a2),
        bAnd(Nat.beq (fld840 E 3) (pcj n w (lget CA j) (lget CB j) a3),
          chkE n w CA CB a0 a1 a2 a3 js (Nat.shiftRight E 3360))))) = true := h
    simp only [bAnd_iff, Nat.beq_eq] at h'
    obtain ⟨e0, e1, e2, e3, ht⟩ := h'
    change bIf(f j E, true, anyE f js (Nat.shiftRight E 3360)) = (g j || js.any g)
    rw [hfg j E e0 e1 e2 e3, anyE_eq n w CA CB a0 a1 a2 a3 f g hfg js _ ht]
    cases g j <;> rfl

theorem pre_ok {n w R Y Ri : Nat} (hn : n < 2 ^ 32) (h0 : 0 < n)
    (h : Nat.beq (pc n w R Y) (pc n w Y Ri) = true) :
    Nat.beq (pg w (mask w) R (pg w (mask w) Y 0)) (pg w (mask w) Y (pg w (mask w) Ri 0)) =
      true := by
  have e := congrArg (fun p => pg w (mask w) p 0) (Nat.eq_of_beq_eq_true h)
  simp only [pc] at e
  rw [PF.pg_pcomp hn h0, PF.pg_pcomp hn h0] at e
  exact Nat.beq_eq.mpr e

theorem pg_pc0 (R Y : Nat) :
    pg 7 (mask 7) (pc 120 7 R Y) 0 = pg 7 (mask 7) R (pg 7 (mask 7) Y 0) := by
  simp only [pc]
  rw [PF.pg_pcomp (by norm_num) (by norm_num)]

theorem prepE_eq {n w : Nat} (hn : n < 2 ^ 32) (h0 : 0 < n) (sp0 CA CB : List Nat)
    (R Ri RR Y Y2 Yi : Nat) (hYi : Yi = pinv n w Y) (js : List Nat) (E : Nat)
    (h : chkE n w CA CB (pidn n w) RR R Ri js E = true) :
    prepE n w sp0 CA CB R Ri RR Y Y2 Yi js E =
      prepZ n w sp0 R Ri RR Y Y2 (js.map fun j => (lget CA j, lget CB j)) := by
  subst hYi
  unfold prepE prepZ
  simp only [strictB_eqZ, forceL_eq]
  cases Nat.beq RR Y2
  · rfl
  · cases canonQ w R Y (pinv n w Y)
    · rfl
    · cases hp : Nat.beq (pg w (mask w) R (pg w (mask w) Y 0))
          (pg w (mask w) Y (pg w (mask w) Ri 0))
      · cases hb : Nat.beq (pc n w R Y) (pc n w Y Ri)
        · rfl
        · rw [pre_ok hn h0 hb] at hp
          exact Bool.noConfusion hp
      · rw [anyE_eq n w CA CB (pidn n w) RR R Ri
          (fun j E' => ppairWitE n w sp0
            [pidn n w, RR, R, Ri, Y, pinv n w Y, pc n w R Y, pc n w Y R] RR (lget CA j)
              (lget CB j) E')
          (fun j => ppairWitZ n w sp0
            [pidn n w, RR, R, Ri, Y, pinv n w Y, pc n w R Y, pc n w Y R] RR (lget CA j)
              (lget CB j))
          (fun j E' e0 e1 e2 e3 => ppairWitE_eq n w sp0 _ _ _ _ _ RR _ _ E' e0 e1 e2 e3) js E h,
          List.any_map]
        rfl

theorem prepE_guard (n w : Nat) (sp0 CA CB : List Nat) (R Ri RR Y Y2 Yi : Nat) (js : List Nat)
    (E : Nat) : bIf(Nat.beq RR Y2, prepE n w sp0 CA CB R Ri RR Y Y2 Yi js E, true) =
      prepE n w sp0 CA CB R Ri RR Y Y2 Yi js E := by
  cases h : Nat.beq RR Y2
  · unfold prepE
    rw [h]
  · rfl

theorem allE_eq {n w : Nat} (hn : n < 2 ^ 32) (h0 : 0 < n) (sp0 CA CB : List Nat)
    (Y Y2 Yi : Nat) (hYi : Yi = pinv n w Y) :
    ∀ (A B C : List Nat) (D : List (List Nat)) (L : List Nat),
      chkAll n w CA CB A B C D L = true → allE n w sp0 CA CB Y Y2 Yi A B C D L =
        allZ n w sp0 Y Y2 A B C (D.map (List.map fun j => (lget CA j, lget CB j)))
  | [], _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, [], h => absurd (h : false = true) Bool.false_ne_true
  | R :: A, Ri :: B, RR :: C, js :: D, E :: L, h => by
    have h' : bAnd(chkE n w CA CB (pidn n w) RR R Ri js E, chkAll n w CA CB A B C D L) = true := h
    rw [bAnd_iff] at h'
    change bAnd(bIf(Nat.beq RR Y2, prepE n w sp0 CA CB R Ri RR Y Y2 Yi js E, true),
        allE n w sp0 CA CB Y Y2 Yi A B C D L) =
      bAnd(prepZ n w sp0 R Ri RR Y Y2 (js.map fun j => (lget CA j, lget CB j)),
        allZ n w sp0 Y Y2 A B C (D.map (List.map fun j => (lget CA j, lget CB j))))
    rw [prepE_guard, prepE_eq hn h0 sp0 CA CB R Ri RR Y Y2 Yi hYi js E h'.1,
      allE_eq hn h0 sp0 CA CB Y Y2 Yi hYi A B C D L h'.2]

theorem allE_none (n w : Nat) (sp0 CA CB : List Nat) (Y Y2 Yi : Nat) :
    ∀ (A B C : List Nat) (D : List (List Nat)) (L : List Nat),
      C.any (fun RR => Nat.beq RR Y2) = false → allE n w sp0 CA CB Y Y2 Yi A B C D L = true
  | [], _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _ => rfl
  | R :: A, Ri :: B, RR :: C, js :: D, E :: L, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    change bAnd(bIf(Nat.beq RR Y2, prepE n w sp0 CA CB R Ri RR Y Y2 Yi js E, true),
      allE n w sp0 CA CB Y Y2 Yi A B C D L) = true
    rw [h.1, allE_none n w sp0 CA CB Y Y2 Yi A B C D L h.2]

@[expose] noncomputable def pairsZ (Y : Nat) : Bool :=
  strictB (pc 120 7 Y Y) (fun Y2 => bIf(RC.any (fun RR => Nat.beq RR Y2),
    allE 120 7 SP CA CB Y Y2 (pc 120 7 Y2 Y) RA RB RC perRepO RE, true))

@[expose] noncomputable def pairsO8C (Y : Nat) : Bool :=
  (repsK.zip candsK).all fun p => !canonQ 7 p.1 Y (pinv 120 7 Y) || prepY 120 7 sp0K p.1 p.2 Y

theorem pairsZ_spec {Y : Nat} (h : pairsZ Y = true)
    (hYi : pc 120 7 (pc 120 7 Y Y) Y = pinv 120 7 Y) : pairsO8C Y = true := by
  have hc : perRepO.map (List.map fun j => (lget CA j, lget CB j)) = candsO := rfl
  simp only [pairsZ, strictB_eqZ] at h
  replace h : allE 120 7 SP CA CB Y (pc 120 7 Y Y) (pc 120 7 (pc 120 7 Y Y) Y) RA RB RC perRepO
      RE = true := by
    cases hc : RC.any (fun RR => Nat.beq RR (pc 120 7 Y Y))
    · exact allE_none _ _ _ _ _ _ _ _ RA RB RC perRepO RE hc
    · rw [hc] at h
      exact h
  rw [allE_eq (by norm_num) (by norm_num) SP CA CB Y (pc 120 7 Y Y) _ hYi RA RB RC perRepO RE kRE,
    hc, kRB, kRC, kRA, kSP, allZ_eq _ _ _ _ _ _ _ candsO_any, kCZ] at h
  unfold pairsO8C
  exact h

@[expose] noncomputable def recK (k : Nat) : Bool :=
  allN 53 (fun i => bIf(Nat.blt (Nat.add (Nat.mul k 53) i) RS.N,
    pairsZ (RS.E (Nat.add (Nat.mul k 53) i)), true))

theorem ch517202r : Nat.ble RS.N (Nat.mul 64 53) = true := by decide +kernel

end CertificateChecks.KernelO8Twin

#kc_each CertificateChecks.KernelO8Twin.recK 0 64

end

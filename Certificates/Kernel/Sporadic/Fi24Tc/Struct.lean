module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi24ThreeData
public import Certificates.Kernel.Sporadic.Fi24Tc.Data
public import Certificates.Kernel.Sporadic.Fi24Tc.Pack
public import Certificates.Data.Kernel.Ssa3Free
import all CFSG.RankThree.Asc83Table.MatCertDefs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CFSG.KD.Fi24Tc

open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi24Three CFSG.KC.Ssa3
open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

noncomputable def tqPk (w s m : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun h _ ih P => Bool.rec false (ih (Nat.shiftRight P w))
      (Nat.beq (Nat.land (Nat.shiftRight P s) m) h)) L

noncomputable def tqAt (P w s m n d i : Nat) : Nat :=
  Bool.rec d (Nat.land (Nat.shiftRight (Nat.shiftRight P (Nat.mul w i)) s) m) (Nat.blt i n)

theorem tqPk_get {w s m : Nat} : ∀ {L : List Nat} {P : Nat}, tqPk w s m L P = true →
    ∀ i (hi : i < L.length), (P >>> (w * i) >>> s) &&& m = L[i]
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | h :: t, P, hP, i, hi => by
    have hP' : Bool.rec false (tqPk w s m t (Nat.shiftRight P w))
        (Nat.beq (Nat.land (Nat.shiftRight P s) m) h) = true := hP
    cases hb : Nat.beq (Nat.land (Nat.shiftRight P s) m) h with
    | false =>
      rw [hb] at hP'
      exact absurd hP' Bool.false_ne_true
    | true =>
      rw [hb] at hP'
      cases i with
      | zero =>
        rw [Nat.mul_zero, Nat.shiftRight_zero, List.getElem_cons_zero]
        exact Nat.eq_of_beq_eq_true hb
      | succ i =>
        have := tqPk_get hP' i (Nat.lt_of_succ_lt_succ hi)
        rw [List.getElem_cons_succ, Nat.mul_succ, Nat.add_comm, Nat.shiftRight_add]
        exact this

theorem tqAt_eq {P w s m n d : Nat} {L : List Nat} (hP : tqPk w s m L P = true)
    (hn : L.length = n) (i : Nat) : tqAt P w s m n d i = L.getD i d := by
  unfold tqAt
  by_cases hi : i < n
  · have hb : Nat.blt i n = true := Nat.blt_eq.mpr hi
    rw [hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hn ▸ hi), Option.getD_some]
    exact tqPk_get hP i (hn ▸ hi)
  · have hb : Nat.blt i n = false := by
      cases h : Nat.blt i n with
      | false => rfl
      | true => exact absurd (Nat.blt_eq.mp h) hi
    rw [hb, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]

structure TqLk where
  nk : Nat → Nat
  na : Nat → Nat
  nb : Nat → Nat
  fv : Nat → Nat
  qk0 : Nat → Nat
  qk1 : Nat → Nat
  qx : Nat → Nat
  qy : Nat → Nat
  qt : Nat → Nat
  qf : Nat → Nat

noncomputable def TqLk.ofD (D : SData) : TqLk :=
  ⟨fun i => D.nk.getD i 1, fun i => D.na.getD i 0, fun i => D.nb.getD i 0,
    fun i => D.fv.getD i 0, fun i => D.qk.getD i 0, fun i => D.qk.getD i 1,
    fun i => D.qx.getD i 0, fun i => D.qy.getD i 0, fun i => D.qt.getD i 0,
    fun i => D.qf.getD i 0⟩

noncomputable def tqK : TqLk :=
  ⟨tqAt tqNP 32 22 1023 1557 1, tqAt tqNP 32 0 2047 1557 0, tqAt tqNP 32 11 2047 1557 0,
    tqAt tqFP 11 0 2047 90 0, tqAt tqQP 40 35 1 229 0, tqAt tqQP 40 35 1 229 1,
    tqAt tqQP 40 0 2047 229 0, tqAt tqQP 40 11 2047 229 0, tqAt tqQP 40 31 15 229 0,
    tqAt tqQP 40 22 511 229 0⟩

theorem tqNK : tqPk 32 22 1023 SD.nk tqNP = true := by decide +kernel
theorem tqNA : tqPk 32 0 2047 SD.na tqNP = true := by decide +kernel
theorem tqNB : tqPk 32 11 2047 SD.nb tqNP = true := by decide +kernel
theorem tqFV : tqPk 11 0 2047 SD.fv tqFP = true := by decide +kernel
theorem tqQK : tqPk 40 35 1 SD.qk tqQP = true := by decide +kernel
theorem tqQX : tqPk 40 0 2047 SD.qx tqQP = true := by decide +kernel
theorem tqQY : tqPk 40 11 2047 SD.qy tqQP = true := by decide +kernel
theorem tqQT : tqPk 40 31 15 SD.qt tqQP = true := by decide +kernel
theorem tqQF : tqPk 40 22 511 SD.qf tqQP = true := by decide +kernel
theorem tqLN : SD.nk.length = 1557 ∧ SD.na.length = 1557 ∧ SD.nb.length = 1557 ∧
    SD.fv.length = 90 ∧ SD.qk.length = 229 ∧ SD.qx.length = 229 ∧ SD.qy.length = 229 ∧
    SD.qt.length = 229 ∧ SD.qf.length = 229 := by decide +kernel

theorem tqFL_eq : tcSpec.facts = tqFL := by decide +kernel

theorem tqK_eq : TqLk.ofD SD = tqK := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := tqLN
  unfold TqLk.ofD tqK
  congr 1 <;> funext i
  · exact (tqAt_eq tqNK l1 i).symm
  · exact (tqAt_eq tqNA l2 i).symm
  · exact (tqAt_eq tqNB l3 i).symm
  · exact (tqAt_eq tqFV l4 i).symm
  · exact (tqAt_eq tqQK l5 i).symm
  · exact (tqAt_eq tqQK l5 i).symm
  · exact (tqAt_eq tqQX l6 i).symm
  · exact (tqAt_eq tqQY l7 i).symm
  · exact (tqAt_eq tqQT l8 i).symm
  · exact (tqAt_eq tqQF l9 i).symm

noncomputable def tqPid (K : TqLk) (y e x : Nat) : Bool :=
  bif Nat.beq e 0 then Nat.beq x 2 else bif Nat.beq e 1 then Nat.beq x y else
    Nat.ble 3 x && Nat.beq (K.nk (x - 3)) e && Nat.beq (K.na (x - 3)) y

noncomputable def tqMul (K : TqLk) (y z x : Nat) : Bool :=
  Nat.ble 3 x && Nat.beq (K.nk (x - 3)) 0 && Nat.beq (K.na (x - 3)) y &&
    Nat.beq (K.nb (x - 3)) z

theorem tqPid_ofD (D : SData) : tqPid (TqLk.ofD D) = pidS D := rfl

theorem tqMul_ofD (D : SData) : tqMul (TqLk.ofD D) = mulS D := rfl

noncomputable def tqProg (K : TqLk) (fv : List Nat) : List Op → List Nat → List Nat → Bool
  | [], [], V => V == fv
  | .mul i j k :: p, x :: xs, V => tqMul K (V.getD i 0) (V.getD j 0) x && tqProg K fv p xs (V.set k x)
  | .pow e i k :: p, x :: xs, V => tqPid K (V.getD i 0) e x && tqProg K fv p xs (V.set k x)
  | _, _, _ => false

theorem tqProg_ofD (D : SData) :
    ∀ p xs V, tqProg (TqLk.ofD D) D.fv p xs V = progS D p xs V
  | [], [], V => by simp only [tqProg, progS]
  | [], _ :: _, V => by simp only [tqProg, progS]
  | .mul _ _ _ :: _, [], V => by simp only [tqProg, progS]
  | .pow _ _ _ :: _, [], V => by simp only [tqProg, progS]
  | .mul i j k :: p, x :: xs, V => by
    simp only [tqProg, progS, tqMul_ofD, tqProg_ofD D p xs]
  | .pow e i k :: p, x :: xs, V => by
    simp only [tqProg, progS, tqPid_ofD, tqProg_ofD D p xs]

noncomputable def tqSsa (K : TqLk) (D : SData) (prog : List Op) (n : Nat) : Bool :=
  Nat.ble 2 n && prog.all (Op.lt n) && structS D &&
    tqProg K D.fv prog D.opn ((List.range n).map fun r => Nat.min r 2)

theorem tqSsa_of {D : SData} {K : TqLk} {prog : List Op} {n : Nat} (hK : TqLk.ofD D = K)
    (h : tqSsa K D prog n = true) : ssaOK D prog n = true := by
  subst hK
  simpa only [tqSsa, ssaOK, tqProg_ofD] using h

noncomputable def tqWid (K : TqLk) : Word → Nat → Bool
  | [], x => Nat.beq x 2
  | [(r, e)], x => tqPid K (K.fv r) e x
  | (r, e) :: w, x => tqMul K (K.na (x - 3)) (K.nb (x - 3)) x &&
      tqPid K (K.fv r) e (K.na (x - 3)) && tqWid K w (K.nb (x - 3))

theorem tqWid_ofD (D : SData) (w : Word) (x : Nat) : tqWid (TqLk.ofD D) w x = widS D w x := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
    cases w with
    | nil => simp only [tqWid, widS, tqPid_ofD]; rfl
    | cons b w => simp only [tqWid, widS, tqPid_ofD, tqMul_ofD, ← ih]; rfl

noncomputable def tqFact (K : TqLk) (n : Nat) (q : Nat) : MFact → Bool
  | .ord r e => Nat.beq (K.qk1 q) 0 && Nat.blt r n && Nat.blt 0 e &&
      tqPid K (K.fv r) e (K.qx q) && Nat.beq (K.qy q) 2
  | .conj h u w => Nat.beq (K.qk1 q) 0 && Nat.blt h n && wordLt n u && wordLt n w &&
      tqMul K (K.fv h) (K.nb (K.qx q - 3)) (K.qx q) &&
      tqWid K u (K.nb (K.qx q - 3)) &&
      tqMul K (K.na (K.qy q - 3)) (K.fv h) (K.qy q) &&
      tqWid K w (K.na (K.qy q - 3))
  | .ne w₁ w₂ t => !Nat.beq (K.qk0 q) 0 && wordLt n w₁ && wordLt n w₂ &&
      Nat.beq (K.qt q) t && tqWid K w₁ (K.qx q) && tqWid K w₂ (K.qy q)
  | .eq w₁ w₂ => Nat.beq (K.qk1 q) 0 && wordLt n w₁ && wordLt n w₂ &&
      tqWid K w₁ (K.qx q) && tqWid K w₂ (K.qy q)

theorem tqFact_ofD (D : SData) (n q : Nat) (g : MFact) :
    tqFact (TqLk.ofD D) n q g = factS D n q g := by
  cases g <;> simp only [tqFact, factS, tqPid_ofD, tqMul_ofD, tqWid_ofD] <;> rfl

noncomputable def tqCmps (K : TqLk) (n : Nat) (F : List MFact) (m nq : Nat) : Bool :=
  (List.range nq).all fun q =>
    Nat.blt (K.qf q) m && tqFact K n q (F.getD (K.qf q) (.eq [] []))

theorem tqCmps_of {D : SData} {K : TqLk} {n : Nat} {facts F : List MFact} {m nq : Nat}
    (hK : TqLk.ofD D = K) (hF : facts = F) (hm : F.length = m) (hq : D.qk.length = nq)
    (h : tqCmps K n F m nq = true) : cmpsS D n facts = true := by
  subst hK hF hm hq
  simp only [tqCmps, tqFact_ofD] at h
  exact h

noncomputable def tqEx (K : TqLk) (C : List Nat) : Nat → Nat → List (Nat × Nat)
  | 0, x => [(x, 1)]
  | f + 1, x =>
    bif Nat.blt x 2 || memS x C then [(x, 1)] else bif Nat.beq x 2 then [] else
    bif Nat.blt (K.na (x - 3)) x && Nat.blt (K.nb (x - 3)) x then
      bif Nat.beq (K.nk (x - 3)) 0 then
        tqEx K C f (K.na (x - 3)) ++ tqEx K C f (K.nb (x - 3))
      else powL (K.nk (x - 3)) (tqEx K C f (K.na (x - 3)))
    else []

theorem tqEx_ofD (D : SData) (C : List Nat) (f x : Nat) :
    tqEx (TqLk.ofD D) C f x = exS D C f x := by
  induction f generalizing x with
  | zero => simp only [tqEx, exS]
  | succ f ih => simp only [tqEx, exS, ih]; rfl

noncomputable def tqWex (K : TqLk) (C : List Nat) (f : Nat) : Word → List (Nat × Nat)
  | [] => []
  | (r, e) :: w => powL e (tqEx K C f (K.fv r)) ++ tqWex K C f w

theorem tqWex_ofD (D : SData) (C : List Nat) (f : Nat) (w : Word) :
    tqWex (TqLk.ofD D) C f w = wexS D C f w := by
  induction w with
  | nil => simp only [tqWex, wexS]
  | cons a w ih => simp only [tqWex, wexS, tqEx_ofD, ih]; rfl

noncomputable def tqFreeF (K : TqLk) (n f : Nat) : MFact → Bool
  | .eq w₁ w₂ => wordLt n w₁ && wordLt n w₂ &&
      eqL (mergeS (tqWex K (w₂.map fun p => K.fv p.1) f w₁))
        (mergeS (tqWex K (w₂.map fun p => K.fv p.1) f w₂))
  | _ => false

theorem tqFreeF_ofD (D : SData) (n f : Nat) (g : MFact) :
    tqFreeF (TqLk.ofD D) n f g = freeF D n f g := by
  cases g <;> simp only [tqFreeF, freeF, freeS, tqWex_ofD] <;> rfl

noncomputable def tqCover (K : TqLk) (n f : Nat) (F : List MFact) (m nq : Nat) : Bool :=
  (List.range m).all fun i =>
    (List.range nq).any (fun q => Nat.beq (K.qf q) i) ||
      tqFreeF K n f (F.getD i (.eq [] []))

theorem tqCover_of {D : SData} {K : TqLk} {n f : Nat} {facts F : List MFact} {m nq : Nat}
    (hK : TqLk.ofD D = K) (hF : facts = F) (hm : F.length = m) (hq : D.qk.length = nq)
    (h : tqCover K n f F m nq = true) : coverS D n f facts = true := by
  subst hK hF hm hq
  have e : tqFreeF (TqLk.ofD D) n f = freeF D n f := funext (tqFreeF_ofD D n f)
  simp only [tqCover, e] at h
  exact h

end CFSG.KD.Fi24Tc

public section

namespace CFSG.KD.Fi24Tc

open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi24Three CFSG.KC.Ssa3

theorem ssa_ok : ssaOK SD tcProg tcNregs = true :=
  tqSsa_of tqK_eq (by decide +kernel)

theorem struct_ok : structS SD = true := by decide +kernel

theorem cmps_ok : cmpsS SD tcNregs tcSpec.facts = true :=
  tqCmps_of (m := 275) (nq := 229) tqK_eq tqFL_eq (by decide +kernel) tqLN.2.2.2.2.1
    (by decide +kernel)

theorem cover_ok : coverS SD tcNregs 2000 tcSpec.facts = true :=
  tqCover_of (m := 275) (nq := 229) tqK_eq tqFL_eq (by decide +kernel) tqLN.2.2.2.2.1
    (by decide +kernel)

theorem nchunks : SD.cb.length = 239 + 1 := by decide +kernel

theorem wf_ok : tcSpec.wf = true := by decide +kernel

theorem fv0 : SD.fv.getD tcSpec.rA 0 = 0 := by decide +kernel

theorem fv1 : SD.fv.getD tcSpec.rB 0 = 1 := by decide +kernel

end CFSG.KD.Fi24Tc

end

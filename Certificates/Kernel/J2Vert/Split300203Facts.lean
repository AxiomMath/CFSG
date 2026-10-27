module

public import Certificates.Kernel.J2Vert.Split300203
public import CFSG.Certificates.Kernel.J2VertKSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Vert.Split

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.J2VertK
open CFSG.Monster.B.Co2.Native CFSG.Quasithin.Background.Harris.R1.J2Vert

theorem all_range_eq {k : Nat} {P Q : Nat → Bool} (h : ∀ j < k, P j = Q j) :
    (List.range k).all P = allN k Q := by
  rw [Bool.eq_iff_iff, List.all_eq_true, CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro hp j hj
    rw [← h j hj]
    exact hp j (List.mem_range.2 hj)
  · intro hq j hj
    have hj' := List.mem_range.1 hj
    rw [h j hj']
    exact hq j hj'

theorem hid : idA 64 = unpack 64 7 one := by
  have h := kId
  rw [bAnd_iff] at h
  exact (idK_sound h.2).symm

theorem cid : cn one = true := by
  have h := kId
  rw [bAnd_iff] at h
  exact h.1

theorem hS : ∀ l < 8, sArrs.getD l (idA 64) = unpack 64 7 (SG l) := by
  have h := kBindS
  rw [bAnd_iff] at h
  exact getD_of_bind (Nat.eq_of_beq_eq_true h.1) h.2

theorem hT : ∀ l < 3, tsArrs.getD l (idA 64) = unpack 64 7 (TG l) := by
  have h := kBindT
  rw [bAnd_iff] at h
  exact getD_of_bind (Nat.eq_of_beq_eq_true h.1) h.2

theorem genS {i : Nat} (hi : i < 8) : invEqK 64 7 (mask 7) (64 * 7) (SG i) (SGI i) = true ∧
    cn (SG i) = true ∧ cn (SGI i) = true := by
  have h := allN_spec kGenS i hi
  simp only [bAnd_iff] at h
  exact h

theorem genT {i : Nat} (hi : i < 3) : invEqK 64 7 (mask 7) (64 * 7) (TG i) (TGI i) = true ∧
    cn (TG i) = true ∧ cn (TGI i) = true := by
  have h := allN_spec kGenT i hi
  simp only [bAnd_iff] at h
  exact h

theorem allInvS {k : Nat} (hk : k ≤ 8) :
    allN k (fun i => invEqK 64 7 (mask 7) (64 * 7) (SG i) (SGI i)) = true :=
  CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => (genS (by omega)).1

theorem allInvT : allN 3 (fun i => invEqK 64 7 (mask 7) (64 * 7) (TG i) (TGI i)) = true :=
  CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => (genT hi).1

theorem invT {i : Nat} (hi : i < 3) : invCand 64 (unpack 64 7 (TG i)) = unpack 64 7 (TGI i) :=
  (invEqK_sound (genT hi).1).1

theorem hQ : ∀ l < 5, (sArrs.extract 0 5).getD l (idA 64) = unpack 64 7 (SG l) := by
  intro l hl
  have h8 : sArrs.size = 8 := by
    have h := kBindS
    rw [bAnd_iff] at h
    exact Nat.eq_of_beq_eq_true h.1
  rw [← hS l (by omega), Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_extract]
  simp [h8, hl]

theorem treeS : buildTab 64 sArrs tabS =
      (List.range (tabS.length + 1)).map (fun j => unpack 64 7 (ES j)) ∧
    ∀ j ≤ tabS.length, cK 64 7 (ES j) :=
  have h := (bAnd_iff (Nat.beq (ES 0) one) (treeK 64 7 8 SG ES tabS 0)).1 kTreeS
  buildTab_eq hS (fun l hl => (genS hl).2.1) hid cid (Nat.eq_of_beq_eq_true h.1) h.2

theorem treeT : buildTab 64 tsArrs tabTs =
      (List.range (tabTs.length + 1)).map (fun j => unpack 64 7 (ET j)) ∧
    ∀ j ≤ tabTs.length, cK 64 7 (ET j) :=
  have h := (bAnd_iff (Nat.beq (ET 0) one) (treeK 64 7 3 TG ET tabTs 0)).1 kTreeT
  buildTab_eq hT (fun l hl => (genT hl).2.1) hid cid (Nat.eq_of_beq_eq_true h.1) h.2

theorem treeQ : buildTab 64 (sArrs.extract 0 5) tabQs =
      (List.range (tabQs.length + 1)).map (fun j => unpack 64 7 (EQ j)) ∧
    ∀ j ≤ tabQs.length, cK 64 7 (EQ j) :=
  have h := (bAnd_iff (Nat.beq (EQ 0) one) (treeK 64 7 5 SG EQ tabQs 0)).1 kTreeQ
  buildTab_eq hQ (fun l hl => (genS (by omega)).2.1) hid cid (Nat.eq_of_beq_eq_true h.1) h.2

theorem lenS : tabS.length + 1 = 3840 := by decide
theorem lenT : tabTs.length + 1 = 256 := by decide
theorem lenQ : tabQs.length + 1 = 32 := by decide

theorem bS : buildTab 64 sArrs tabS = (List.range 3840).map (fun j => unpack 64 7 (ES j)) := by
  rw [treeS.1, lenS]

theorem bT : buildTab 64 tsArrs tabTs = (List.range 256).map (fun j => unpack 64 7 (ET j)) := by
  rw [treeT.1, lenT]

theorem bQ : buildTab 64 (sArrs.extract 0 5) tabQs =
    (List.range 32).map (fun j => unpack 64 7 (EQ j)) := by
  rw [treeQ.1, lenQ]

theorem cT {j : Nat} (hj : j < 256) : cn (ET j) = true :=
  treeT.2 j (by have := lenT; omega)

theorem cQ {j : Nat} (hj : j < 32) : cn (EQ j) = true :=
  treeQ.2 j (by have := lenQ; omega)

theorem pcE {p q : Nat} (hp : cn p = true) (hq : cn q = true) :
    compA 64 (unpack 64 7 p) (unpack 64 7 q) = unpack 64 7 (pc p q) := compA_unpack hp hq

theorem pcC {p q : Nat} (hp : cn p = true) (hq : cn q = true) : cn (pc p q) = true :=
  canonK_pcomp hp hq

theorem line_eq {k : Nat} (hk : k < 32) :
    (!eqA 64 (compA 64 (unpack 64 7 (EQ k)) (unpack 64 7 (EQ k))) (idA 64) ||
      eqA 64 (unpack 64 7 (EQ k)) (idA 64) || eqA 64 (unpack 64 7 (EQ k)) (sArrs.getD 0 (idA 64)) ||
      !((List.range 3).all fun j =>
        eqA 64 (compA 64 (compA 64 (tsArrs.getD j (idA 64)) (unpack 64 7 (EQ k)))
          (invCand 64 (tsArrs.getD j (idA 64)))) (unpack 64 7 (EQ k)) ||
        eqA 64 (compA 64 (compA 64 (tsArrs.getD j (idA 64)) (unpack 64 7 (EQ k)))
          (invCand 64 (tsArrs.getD j (idA 64))))
          (compA 64 (sArrs.getD 0 (idA 64)) (unpack 64 7 (EQ k)))) ||
      eqA 64 (unpack 64 7 (EQ k)) (sArrs.getD 1 (idA 64)) ||
      eqA 64 (unpack 64 7 (EQ k)) (compA 64 (sArrs.getD 0 (idA 64)) (sArrs.getD 1 (idA 64)))) =
    lineK (EQ k) := by
  have cv := cQ hk
  have c0 := (genS (i := 0) (by omega)).2.1
  have c1 := (genS (i := 1) (by omega)).2.1
  have hj : (List.range 3).all (fun j =>
        eqA 64 (compA 64 (compA 64 (tsArrs.getD j (idA 64)) (unpack 64 7 (EQ k)))
          (invCand 64 (tsArrs.getD j (idA 64)))) (unpack 64 7 (EQ k)) ||
        eqA 64 (compA 64 (compA 64 (tsArrs.getD j (idA 64)) (unpack 64 7 (EQ k)))
          (invCand 64 (tsArrs.getD j (idA 64))))
          (compA 64 (sArrs.getD 0 (idA 64)) (unpack 64 7 (EQ k)))) =
      allN 3 fun j => Nat.beq (pc (pc (TG j) (EQ k)) (TGI j)) (EQ k) ||
        Nat.beq (pc (pc (TG j) (EQ k)) (TGI j)) (pc (SG 0) (EQ k)) := by
    refine all_range_eq fun j hj => ?_
    obtain ⟨-, ct, cti⟩ := genT hj
    rw [hT j hj, invT hj, hS 0 (by omega), pcE ct cv, pcE (pcC ct cv) cti, pcE c0 cv,
      eqA_unpack (pcC (pcC ct cv) cti) cv, eqA_unpack (pcC (pcC ct cv) cti) (pcC c0 cv)]
  rw [hj, hS 0 (by omega), hS 1 (by omega), pcE cv cv, pcE c0 c1, hid, eqA_unpack (pcC cv cv) cid,
    eqA_unpack cv cid, eqA_unpack cv c0, eqA_unpack cv c1, eqA_unpack cv (pcC c0 c1)]
  rfl

theorem line : normalLineCheck 64 sArrs tsArrs 3 (buildTab 64 (sArrs.extract 0 5) tabQs) = true := by
  unfold normalLineCheck
  rw [bQ, List.all_eq_true]
  intro v hv
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv
  have hk' := List.mem_range.1 hk
  rw [line_eq hk']
  exact allN_spec kLine k hk'

theorem count_eq {f : Array Nat → Bool} {g : Nat → Bool} (h : ∀ k < 256, f (unpack 64 7 (ET k)) = g k) :
    ((buildTab 64 tsArrs tabTs).filter f).length = countN 256 g := by
  rw [bT, List.filter_map, List.length_map, ← List.countP_eq_length_filter, countN_eq]
  refine List.countP_congr fun k hk => ?_
  have hk' := List.mem_range.1 hk
  simp only [Function.comp_apply, h k hk']

theorem cent : centCount 64 (buildTab 64 tsArrs tabTs) (sArrs.getD 1 (idA 64)) = 128 := by
  unfold centCount
  rw [← Nat.eq_of_beq_eq_true kCent]
  refine count_eq fun k hk => ?_
  have c1 := (genS (i := 1) (by omega)).2.1
  have cy := cT hk
  rw [hS 1 (by omega), pcE cy c1, pcE c1 cy, eqA_unpack (pcC cy c1) (pcC c1 cy)]

theorem root_eq {x s : Array Nat} {X S : Nat} (hx : x = unpack 64 7 X) (hs : s = unpack 64 7 S)
    (cx : cn X = true) (cs : cn S = true) :
    rootCount 64 (buildTab 64 tsArrs tabTs) x s = countN 256 (fun k => rootK X S (ET k)) := by
  unfold rootCount
  refine count_eq fun k hk => ?_
  have cy := cT hk
  rw [hx, hs, pcE cy cx, pcE cx cy, pcE cy cy, eqA_unpack (pcC cy cx) (pcC cx cy),
    eqA_unpack (pcC cy cy) cs]
  rfl

theorem facts :
    (relCheck 64 sArrs (vRels false) = true)
    ∧ (tabLower 64 sArrs tabS 3840 = true)
    ∧ (tabMem 64 sArrs tabS tsArrs 3 = true)
    ∧ (tabLower 64 tsArrs tabTs 256 = true)
    ∧ (tabClosed 64 tsArrs 3 tabTs = true)
    ∧ (tabClosed 64 (sArrs.extract 0 5) 5 tabQs = true)
    ∧ (normalLineCheck 64 sArrs tsArrs 3 (buildTab 64 (sArrs.extract 0 5) tabQs) = true)
    ∧ (centCount 64 (buildTab 64 tsArrs tabTs) (sArrs.getD 1 (idA 64)) = 128)
    ∧ (rootCount 64 (buildTab 64 tsArrs tabTs) (sArrs.getD 1 (idA 64)) (sArrs.getD 0 (idA 64))
        = 28)
    ∧ (rootCount 64 (buildTab 64 tsArrs tabTs) (sArrs.getD 1 (idA 64)) (sArrs.getD 1 (idA 64))
        = 12)
    ∧ (rootCount 64 (buildTab 64 tsArrs tabTs) (sArrs.getD 1 (idA 64))
        (compA 64 (sArrs.getD 0 (idA 64)) (sArrs.getD 1 (idA 64))) = 12) := by
  have c0 := (genS (i := 0) (by omega)).2.1
  have c1 := (genS (i := 1) (by omega)).2.1
  refine ⟨relCheck_of hS (fun l hl => (genS hl).2.1) (fun l hl => (genS hl).2.2) (allInvS le_rfl)
      hid cid kRel,
    tabLower_of treeS.1 treeS.2 lenS kSortS,
    tabMem_of hT bS kMem,
    tabLower_of treeT.1 treeT.2 lenT kSortT,
    tabClosed_of hT (fun l hl => (genT hl).2.1) (fun l hl => (genT hl).2.2) allInvT bT
      (fun j hj => cT hj) kClosedT,
    tabClosed_of hQ (fun l hl => (genS (by omega)).2.1) (fun l hl => (genS (by omega)).2.2)
      (allInvS (by omega)) bQ (fun j hj => cQ hj) kClosedQ,
    line, cent, ?_, ?_, ?_⟩
  · rw [root_eq (hS 1 (by omega)) (hS 0 (by omega)) c1 c0]
    exact Nat.eq_of_beq_eq_true kRoot0
  · rw [root_eq (hS 1 (by omega)) (hS 1 (by omega)) c1 c1]
    exact Nat.eq_of_beq_eq_true kRoot1
  · rw [root_eq (hS 1 (by omega)) (by rw [hS 0 (by omega), hS 1 (by omega), pcE c0 c1]) c1
      (pcC c0 c1)]
    exact Nat.eq_of_beq_eq_true kRoot2

end CertificateChecks.KernelJ2Vert.Split

end

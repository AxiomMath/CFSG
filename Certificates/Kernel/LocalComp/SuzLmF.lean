module

public import Certificates.Kernel.LocalComp.SuzLmC0
public import Certificates.Kernel.LocalComp.SuzLmC1
public import Certificates.Kernel.LocalComp.SuzLmC2
public import Certificates.Kernel.LocalComp.SuzLmC3
public import Certificates.Kernel.LocalComp.SuzLmC4
public import Certificates.Kernel.LocalComp.SuzLmC5
public import Certificates.Kernel.LocalComp.B0SuzProof
public import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.HeSylKSound
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelLC.SuzLm.centAll CertificateChecks.KernelLC.SuzLm.centSl 96

namespace CertificateChecks.KernelLC.SuzLm

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.L34K CFSG.KC.L34KSnd
open CertificateChecks.KernelLC CFSG.PSL3Four.Native CFSG.ComponentClassification.AS81.SuzB0
open CFSG.LocalAnalysis.GLTheoremA.H1017.SuzLm
open CFSG.KLie.CT (andB orB notB)

attribute [local irreducible] matEnum idTab

abbrev Cn (p : Nat) : Prop := canonK 64 7 (mask 7) (64 * 7) p = true

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem hsz : szOK 64 7 = true := by decide

theorem cn {j : Nat} (hj : j < 25920) : Cn (SuzB0M.T j) := CFSG.KS.Raw.Orb.allN_iff.1 kCan j hj

theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b := by
  by_cases h : a = b
  · subst h
    rw [Nat.beq_refl]
    exact beq_self_eq_true a
  · have h' : Nat.beq a b = false := by
      cases h2 : Nat.beq a b
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h2) h
    rw [h']
    exact beq_false_of_ne h

@[expose] noncomputable def TT : Array Tab := Array.ofFn (n := 25920) fun j => unpack 64 7 (SuzB0M.T j.val)

theorem tabs_eq : matEnum.tabs = TT := CertificateChecks.KernelLC.B0Suz.mat_tabs

theorem TT_size : TT.size = 25920 := Array.size_ofFn

theorem TT_get {j : Nat} (hj : j < 25920) : TT[j]! = unpack 64 7 (SuzB0M.T j) := by
  unfold TT
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem TT_toList : TT.toList = (List.range 25920).map fun j => unpack 64 7 (SuzB0M.T j) := by
  unfold TT
  exact CFSG.KC.BfsPin.pts_toList (fun j => unpack 64 7 (SuzB0M.T j))

theorem filter_map' {α β : Type} (p : β → Bool) (f : α → β) : ∀ l : List α,
    (l.map f).filter p = (l.filter fun x => p (f x)).map f
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.filter_cons, List.filter_cons, filter_map' p f l]
    cases p (f x) <;> rfl

theorem count_eq {p : Tab → Bool} {q : Nat → Bool}
    (h : ∀ j < 25920, p (unpack 64 7 (SuzB0M.T j)) = q j) :
    (TT.toList.filter p).length = CFSG.KC.HeAutK.cntR q 0 25920 := by
  rw [TT_toList, filter_map', List.length_map, CFSG.KC.HeAutK.cntR_eq]
  congr 1
  exact List.filter_congr fun j hj => h j (List.mem_range.1 hj)

theorem nine : lmNineOK () = true := by
  have h := kNine
  rw [strictB_app, strictB_app] at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h3⟩ := andB_iff.1 h
  unfold pc e at h2 h3
  have hk : LmW 0 < 25920 := Nat.blt_eq.mp h1
  have c := cn hk
  have c2 := CFSG.KC.BfsPin.canonK_pcomp c c
  have c3 := CFSG.KC.BfsPin.canonK_pcomp c c2
  have c32 := CFSG.KC.BfsPin.canonK_pcomp c3 c3
  unfold lmNineOK
  simp only []
  rw [tabs_eq, CFSG.KC.L34KSnd.anyBelow_iff]
  refine ⟨LmW 0, by rw [TT_size]; exact hk, ?_⟩
  rw [TT_get hk, comp_unpack' c c, comp_unpack' c c2, comp_unpack' c3 c3, comp_unpack' c3 c32,
    idTab_unpack' hsz, beq_unpack c3 (canon_pidn hsz),
    beq_unpack (CFSG.KC.BfsPin.canonK_pcomp c3 c32) (canon_pidn hsz), notB_iff.1 h2]
  exact h3

theorem stab : lmStabOK () = true := by
  unfold lmStabOK
  simp only []
  rw [tabs_eq, CFSG.KS.BfsReplay.allBelow_iff]
  intro x hx
  have hs : x / 9 < 7 := by omega
  have h := CFSG.KS.Raw.Orb.allN_iff.1 (stabAll (x / 9) hs) (x % 9) (Nat.mod_lt _ (by norm_num))
  have e : Nat.succ (Nat.add (Nat.mul 9 (x / 9)) (x % 9)) = x + 1 := by
    change 9 * (x / 9) + x % 9 + 1 = x + 1
    omega
  rw [e] at h
  have hc : (TT.toList.filter fun t => t[x + 1]! == x + 1).length = fixCnt (x + 1) := by
    unfold fixCnt
    refine count_eq fun j hj => ?_
    rw [CFSG.KC.BfsPin.unpack_get' (by omega), beq_nat]
  have h' := notB_iff.1 h
  change Nat.beq (fixCnt (x + 1) % 27) 0 = false at h'
  rw [hc, bne, beq_nat, h']
  rfl

theorem cent : lmCentOK () = true := by
  unfold lmCentOK
  simp only []
  rw [tabs_eq, CFSG.KS.BfsReplay.allBelow_iff, TT_size]
  intro k hk
  have hs : k / 270 < 96 := by omega
  have h := CFSG.KS.Raw.Orb.allN_iff.1 (centAll (k / 270) hs) (k % 270) (Nat.mod_lt _ (by norm_num))
  have ek : Nat.add (Nat.mul 270 (k / 270)) (k % 270) = k := by
    change 270 * (k / 270) + k % 270 = k
    omega
  rw [ek, strictB_app] at h
  have c := cn hk
  rw [TT_get hk]
  have e1 : (comp 64 (unpack 64 7 (SuzB0M.T k)) (unpack 64 7 (SuzB0M.T k)) == idTab 64) =
      invPt 64 7 (SuzB0M.T k) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, invPt_iff c]
  have e2 : (unpack 64 7 (SuzB0M.T k) == idTab 64) = Nat.beq (SuzB0M.T k) e := by
    rw [idTab_unpack' hsz, beq_unpack c (canon_pidn hsz)]
    rfl
  have hc : (TT.toList.filter fun t => comp 64 t (unpack 64 7 (SuzB0M.T k)) ==
      comp 64 (unpack 64 7 (SuzB0M.T k)) t).length = centCnt (SuzB0M.T k) := by
    unfold centCnt
    refine count_eq fun j hj => ?_
    rw [Bool.eq_iff_iff, beq_iff_eq, commPt_iff (cn hj) c]
  rw [e1, e2, hc]
  unfold centPt at h
  rcases orB_iff.1 h with h1 | h1
  · rw [notB_iff.1 h1]
    rfl
  rcases orB_iff.1 h1 with h2 | h2
  · rw [h2]
    cases invPt 64 7 (SuzB0M.T k) <;> rfl
  · have h' := notB_iff.1 h2
    change Nat.beq (centCnt (SuzB0M.T k) % 27) 0 = false at h'
    rw [bne, beq_nat, h']
    cases invPt 64 7 (SuzB0M.T k) <;> cases Nat.beq (SuzB0M.T k) e <;> rfl

theorem rank_true : lmRankOK () = true := by
  unfold lmRankOK
  rw [nine, stab, cent]
  rfl

end CertificateChecks.KernelLC.SuzLm

end

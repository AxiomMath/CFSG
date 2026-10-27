module

public import Certificates.Kernel.LocalComp.L34Aut.C0
public import Certificates.Kernel.LocalComp.L34Aut.C1
public import Certificates.Kernel.LocalComp.L34Aut.C2
public import Certificates.Kernel.LocalComp.L34Aut.C3
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Certificates.Kernel.L34AutSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Aut

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34W CFSG.KC.L34FixPow CFSG.KC.L34Aut CertificateChecks.KernelLC.L34X
open CertificateChecks.KernelLC.L34Cert CFSG.PSL3Four.Native
open CFSG.KC.L34Scan (pts_get')
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def autAt (x : Nat) : Bool :=
  autPt (pidn 42 6) (RP 0) (RP 1) (RP 2) (RP 3) zP (pcomp 42 6 (mask 6) zP zP)
    (pcomp 42 6 (mask 6) zP (RP 2)) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) zP zP) (RP 2))
    (L34C3.P 1) (L34C3.P 3) x

theorem aut_of {lo n : Nat} (h : aut5180 lo n = true) {i : Nat} (h1 : 1344 * lo ≤ i)
    (h2 : i < 1344 * (lo + n)) : autAt (L34R.T i) = true := by
  unfold aut5180 at h
  simp only [sB] at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h (i / 1344 - lo) (by omega)
  have h'' := CFSG.KS.Raw.Orb.allN_iff.1 h' (i % 1344) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul 1344 (Nat.add lo (i / 1344 - lo))) (i % 1344) = i := by
    change 1344 * (lo + (i / 1344 - lo)) + i % 1344 = i
    omega
  rw [e] at h''
  exact h''

theorem autAll : ∀ i < 241920, autAt (L34R.T i) = true := by
  intro i hi
  rcases Nat.lt_or_ge i (1344 * 15) with h | h0
  · exact aut_of k5180c0 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 30) with h | h1
  · exact aut_of k5180c1 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 45) with h | h2
  · exact aut_of k5180c2 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 60) with h | h3
  · exact aut_of k5180c3 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 75) with h | h4
  · exact aut_of k5180c4 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 90) with h | h5
  · exact aut_of k5180c5 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 105) with h | h6
  · exact aut_of k5180c6 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 120) with h | h7
  · exact aut_of k5180c7 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 135) with h | h8
  · exact aut_of k5180c8 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 150) with h | h9
  · exact aut_of k5180c9 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 165) with h | h10
  · exact aut_of k5180c10 (by omega) (by omega)
  · exact aut_of k5180c11 (by omega) (by omega)

theorem parts {i : Nat} (hi : i < 241920) :
    cenPt (L34C3.P 1) (L34C3.P 3) (pidn 42 6) zP (pcomp 42 6 (mask 6) zP zP)
        (RP 2) (pcomp 42 6 (mask 6) zP (RP 2))
        (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) zP zP) (RP 2)) (L34R.T i) = true ∧
      expPt (L34R.T i) = true ∧
      witPt (pidn 42 6) (RP 0) 64 L34C1.P (fun k => pinv (L34C1.P k)) false (L34R.T i) = true ∧
      witPt (pidn 42 6) (RP 1) 168 L34C2.P (fun k => pinv (L34C2.P k)) false (L34R.T i) = true ∧
      witPt (pidn 42 6) (RP 2) 60 L34C3.P (fun k => pinv (L34C3.P k))
        (orB (Nat.beq (L34R.T i) zP) (Nat.beq (L34R.T i) (pcomp 42 6 (mask 6) zP zP)))
        (L34R.T i) = true ∧
      witPt (pidn 42 6) (RP 3) 72 L34C4.P (fun k => pinv (L34C4.P k)) false (L34R.T i) = true := by
  have h := autAll i hi
  unfold autAt autPt at h
  obtain ⟨a, h⟩ := andB_iff.1 h
  obtain ⟨b, h⟩ := andB_iff.1 h
  obtain ⟨c, h⟩ := andB_iff.1 h
  obtain ⟨d, h⟩ := andB_iff.1 h
  obtain ⟨f, g⟩ := andB_iff.1 h
  exact ⟨a, b, c, d, f, g⟩

theorem auxP : CertificateChecks.KernelLC.L34R.T 227642 = zP ∧ Cn zP ∧
    Nat.beq zP (pidn 42 6) = false ∧ fixPow zP 3 = true ∧
    pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (RP 2) zP) (RP 2) = pcomp 42 6 (mask 6) zP zP ∧
    notInK 20160 CertificateChecks.KernelLC.L34S.T zP = true ∧
    notInK 20160 CertificateChecks.KernelLC.L34S.T (pcomp 42 6 (mask 6) zP zP) = true ∧
    notInK 20160 CertificateChecks.KernelLC.L34S.T (pcomp 42 6 (mask 6) (RP 2) zP) = true ∧
    notInK 20160 CertificateChecks.KernelLC.L34S.T
      (pcomp 42 6 (mask 6) (RP 2) (pcomp 42 6 (mask 6) zP zP)) = true ∧
    (∀ a < 60, commPt 42 6 (L34C3.P a) zP = true) ∧
    (∀ k < 20160, orB (notB (commPt 42 6 (CertificateChecks.KernelLC.L34S.T k) zP))
      (commPt 42 6 (CertificateChecks.KernelLC.L34S.T k) (RP 2)) = true) ∧
    invsK (pidn 42 6) 64 L34C1.P = true ∧ invsK (pidn 42 6) 168 L34C2.P = true ∧
    invsK (pidn 42 6) 60 L34C3.P = true ∧ invsK (pidn 42 6) 72 L34C4.P = true := by
  have h := k5180aux
  unfold aux5180 at h
  simp only [sB] at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h⟩ := andB_iff.1 h
  obtain ⟨h6, h⟩ := andB_iff.1 h
  obtain ⟨h7, h⟩ := andB_iff.1 h
  obtain ⟨h8, h⟩ := andB_iff.1 h
  obtain ⟨h9, h⟩ := andB_iff.1 h
  obtain ⟨h10, h⟩ := andB_iff.1 h
  obtain ⟨h11, h⟩ := andB_iff.1 h
  obtain ⟨h12, h⟩ := andB_iff.1 h
  obtain ⟨h13, h⟩ := andB_iff.1 h
  obtain ⟨h14, h15⟩ := andB_iff.1 h
  refine ⟨Nat.eq_of_beq_eq_true h1, h2, notB_iff.1 h3, h4, Nat.eq_of_beq_eq_true h5, h6, h7, h8,
    h9, CFSG.KS.Raw.Orb.allN_iff.1 h10, fun k hk => ?_, h12, h13, h14, h15⟩
  have := CFSG.KS.Raw.Orb.allN_iff.1 h11 k hk
  simpa only [sB] using this

theorem zT_eq : zT = unpack 42 6 zP := by decide +kernel

theorem cz : Cn zP := auxP.2.1

theorem cr3 : Cn (RP 2) := cnRP (by decide)

theorem cz2 : Cn (pcomp 42 6 (mask 6) zP zP) := canonK_pcomp cz cz

theorem z2T_eq : z2T = unpack 42 6 (pcomp 42 6 (mask 6) zP zP) := by
  unfold z2T
  rw [zT_eq, comp_unpack' cz cz]

theorem invs_of {m : Nat} {C : Nat → Nat} (h : invsK (pidn 42 6) m C = true) :
    ∀ k < m, Cn (C k) ∧ Cn (pinv (C k)) ∧ pcomp 42 6 (mask 6) (C k) (pinv (C k)) = pidn 42 6 := by
  intro k hk
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h k hk
  obtain ⟨a, h'⟩ := andB_iff.1 h'
  obtain ⟨b, c⟩ := andB_iff.1 h'
  exact ⟨a, b, Nat.eq_of_beq_eq_true c⟩

theorem invD {m : Nat} {C : Nat → Nat} (h : invsK (pidn 42 6) m C = true) :
    (∀ k < m, ((pts 42 6 m C).map (invTab 42))[k]! = unpack 42 6 (pinv (C k))) ∧
      invsOK 42 (pts 42 6 m C) ((pts 42 6 m C).map (invTab 42)) = true :=
  invsOK_of_pcomp (size_pts 42 6 m C) (fun _ hk => pts_get' hk) (invs_of h)

theorem hi1 : invsK (pidn 42 6) 64 L34C1.P = true := auxP.2.2.2.2.2.2.2.2.2.2.2.1
theorem hi2 : invsK (pidn 42 6) 168 L34C2.P = true := auxP.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem hi3 : invsK (pidn 42 6) 60 L34C3.P = true := auxP.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem hi4 : invsK (pidn 42 6) 72 L34C4.P = true := auxP.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem cC3 {a : Nat} (ha : a < 60) : Cn (L34C3.P a) := (invs_of hi3 a ha).1

theorem witOK_of {m p r : Nat} {C : Nat → Nat} {exc : Array Tab} {ex : Nat → Bool}
    (hinv : invsK (pidn 42 6) m C = true) (hr : Cn r)
    (hex : ∀ i < 241920, ex (L34R.T i) = true → memTab exc (unpack 42 6 (L34R.T i)) = true)
    (hw : ∀ i < 241920,
      witPt (pidn 42 6) r m C (fun k => pinv (C k)) (ex (L34R.T i)) (L34R.T i) = true)
    (hp : p = 3 ∨ p = 5 ∨ p = 7) :
    witOK 42 p (pts 42 6 241920 L34R.T) (pts 42 6 m C) ((pts 42 6 m C).map (invTab 42)) exc
      (unpack 42 6 r) = true := by
  unfold witOK
  rw [size_pts, CFSG.KS.BfsReplay.allBelow_iff]
  intro i hi
  rw [pts_get' hi]
  exact witPt_sound rfl (pinR.canon i hi) hr (size_pts 42 6 m C) (fun _ ha => pts_get' ha)
    (invD hinv).1 (fun a ha => ⟨(invs_of hinv a ha).1, (invs_of hinv a ha).2.1⟩) (hex i hi)
    (hw i hi) hp

theorem exc_mem {x : Nat}
    (h : orB (Nat.beq x zP) (Nat.beq x (pcomp 42 6 (mask 6) zP zP)) = true) :
    memTab #[zT, z2T] (unpack 42 6 x) = true := by
  unfold memTab
  rw [anyBelow_iff]
  rcases orB_iff.1 h with h | h
  · refine ⟨0, by decide, ?_⟩
    rw [Nat.eq_of_beq_eq_true h, ← zT_eq]
    exact beq_self_eq_true _
  · refine ⟨1, by decide, ?_⟩
    rw [Nat.eq_of_beq_eq_true h, ← z2T_eq]
    exact beq_self_eq_true _

theorem six_mem {x : Nat}
    (h : x = pidn 42 6 ∨ x = zP ∨ x = pcomp 42 6 (mask 6) zP zP ∨ x = RP 2 ∨
      x = pcomp 42 6 (mask 6) zP (RP 2) ∨ x = pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) zP zP) (RP 2)) :
    memTab #[idTab 42, zT, z2T, r₃T, comp 42 zT r₃T, comp 42 z2T r₃T] (unpack 42 6 x) = true := by
  unfold memTab
  rw [anyBelow_iff]
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨0, by decide, ?_⟩
    rw [← idTab42]
    exact beq_self_eq_true _
  · refine ⟨1, by decide, ?_⟩
    rw [← zT_eq]
    exact beq_self_eq_true _
  · refine ⟨2, by decide, ?_⟩
    rw [← z2T_eq]
    exact beq_self_eq_true _
  · refine ⟨3, by decide, ?_⟩
    rw [← r3_eq]
    exact beq_self_eq_true _
  · refine ⟨4, by decide, ?_⟩
    rw [← comp_unpack' cz cr3, ← zT_eq, ← r3_eq]
    exact beq_self_eq_true _
  · refine ⟨5, by decide, ?_⟩
    rw [← comp_unpack' cz2 cr3, ← z2T_eq, ← r3_eq]
    exact beq_self_eq_true _

theorem aut_true :
    l34AutCheck (enumBFS 42 gensS 20160).tabs (enumBFS 42 gTabs 241920).tabs = true := by
  have cr1 : Cn (RP 0) := cnRP (by decide)
  have cr2 : Cn (RP 1) := cnRP (by decide)
  have cr4 : Cn (RP 3) := cnRP (by decide)
  have hf : ∀ i < 241920, (fun _ : Nat => false) (L34R.T i) = true →
      memTab (#[] : Array Tab) (unpack 42 6 (L34R.T i)) = true :=
    fun _ _ h => absurd h Bool.false_ne_true
  have h3 : ∀ i < 241920, (fun x => orB (Nat.beq x zP) (Nat.beq x (pcomp 42 6 (mask 6) zP zP)))
      (L34R.T i) = true → memTab #[zT, z2T] (unpack 42 6 (L34R.T i)) = true :=
    fun _ _ h => exc_mem h
  unfold l34AutCheck
  dsimp only
  rw [hS.1, hR.1, cent1, cent2, cent3, cent4]
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (invD hi1).2, (invD hi2).2, (invD hi3).2,
    (invD hi4).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold memTab
    rw [size_pts, anyBelow_iff]
    refine ⟨227642, by decide, ?_⟩
    rw [pts_get' (by decide), auxP.1, ← zT_eq]
    exact beq_self_eq_true _
  · rw [zT_eq, idTab42, beq_unpack cz cn_pidn, auxP.2.2.1]
    rfl
  · rw [zT_eq, fixPow_eq cz]
    exact auxP.2.2.2.1
  · rw [z2T_eq, r3_eq, zT_eq, comp_unpack' cr3 cz, comp_unpack' (canonK_pcomp cr3 cz) cr3,
      beq_unpack (canonK_pcomp (canonK_pcomp cr3 cz) cr3) cz2, auxP.2.2.2.2.1]
    exact Nat.beq_refl _
  · exact notIn_sound zT_eq cz pinS.canon auxP.2.2.2.2.2.1
  · exact notIn_sound z2T_eq cz2 pinS.canon auxP.2.2.2.2.2.2.1
  · exact notIn_sound (by rw [r3_eq, zT_eq, comp_unpack' cr3 cz]) (canonK_pcomp cr3 cz) pinS.canon
      auxP.2.2.2.2.2.2.2.1
  · exact notIn_sound (by rw [r3_eq, z2T_eq, comp_unpack' cr3 cz2]) (canonK_pcomp cr3 cz2)
      pinS.canon auxP.2.2.2.2.2.2.2.2.1
  · rw [size_pts, CFSG.KS.BfsReplay.allBelow_iff]
    intro a ha
    beta_reduce
    rw [pts_get' ha, zT_eq, commB (cC3 ha) cz]
    exact auxP.2.2.2.2.2.2.2.2.2.1 a ha
  · rw [size_pts, CFSG.KS.BfsReplay.allBelow_iff]
    intro k hk
    beta_reduce
    rw [pts_get' hk, zT_eq, r3_eq, commB (pinS.canon k hk) cz, commB (pinS.canon k hk) cr3]
    rcases orB_iff.1 (auxP.2.2.2.2.2.2.2.2.2.2.1 k hk) with h | h
    · rw [notB_iff.1 h]
      rfl
    · rw [h, Bool.or_true]
  · unfold centScanOK
    rw [size_pts, CFSG.KS.BfsReplay.allBelow_iff]
    intro k hk
    beta_reduce
    rw [pts_get' hk]
    exact cenPt_sound (pinR.canon k hk) (cC3 (by decide)) (cC3 (by decide))
      ⟨1, by rw [size_pts]; decide, pts_get' (by decide)⟩
      ⟨3, by rw [size_pts]; decide, pts_get' (by decide)⟩ six_mem (parts hk).1
  · unfold expOK
    rw [size_pts, CFSG.KS.BfsReplay.allBelow_iff]
    intro k hk
    beta_reduce
    rw [pts_get' hk]
    exact expPt_sound (pinR.canon k hk) (parts hk).2.1
  · rw [r1_eq]
    exact witOK_of hi1 cr1 (ex := fun _ => false) hf (fun i hi => (parts hi).2.2.1) (by decide)
  · rw [r1_eq]
    exact witOK_of hi1 cr1 (ex := fun _ => false) hf (fun i hi => (parts hi).2.2.1) (by decide)
  · rw [r1_eq]
    exact witOK_of hi1 cr1 (ex := fun _ => false) hf (fun i hi => (parts hi).2.2.1) (by decide)
  · rw [r2_eq]
    exact witOK_of hi2 cr2 (ex := fun _ => false) hf (fun i hi => (parts hi).2.2.2.1) (by decide)
  · rw [r2_eq]
    exact witOK_of hi2 cr2 (ex := fun _ => false) hf (fun i hi => (parts hi).2.2.2.1) (by decide)
  · rw [r2_eq]
    exact witOK_of hi2 cr2 (ex := fun _ => false) hf (fun i hi => (parts hi).2.2.2.1) (by decide)
  · rw [r3_eq]
    exact witOK_of hi3 cr3 (ex := fun x => orB (Nat.beq x zP) (Nat.beq x (pcomp 42 6 (mask 6) zP zP))) h3 (fun i hi => (parts hi).2.2.2.2.1) (by decide)
  · rw [r3_eq]
    exact witOK_of hi3 cr3 (ex := fun x => orB (Nat.beq x zP) (Nat.beq x (pcomp 42 6 (mask 6) zP zP))) h3 (fun i hi => (parts hi).2.2.2.2.1) (by decide)
  · rw [r3_eq]
    exact witOK_of hi3 cr3 (ex := fun x => orB (Nat.beq x zP) (Nat.beq x (pcomp 42 6 (mask 6) zP zP))) h3 (fun i hi => (parts hi).2.2.2.2.1) (by decide)
  · rw [r4_eq]
    exact witOK_of hi4 cr4 (ex := fun _ => false) hf (fun i hi => (parts hi).2.2.2.2.2) (by decide)
  · rw [r4_eq]
    exact witOK_of hi4 cr4 (ex := fun _ => false) hf (fun i hi => (parts hi).2.2.2.2.2) (by decide)
  · rw [r4_eq]
    exact witOK_of hi4 cr4 (ex := fun _ => false) hf (fun i hi => (parts hi).2.2.2.2.2) (by decide)

end CertificateChecks.KernelLC.L34Aut

end

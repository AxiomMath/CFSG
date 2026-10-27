module

public import Certificates.Kernel.LocalComp.L34E16
public import Certificates.Kernel.LocalComp.L34Cert
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelLC.L34E16

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.KC.L34KSnd

abbrev Cn (p : Nat) : Prop := canonK 42 6 (mask 6) (42 * 6) p = true

theorem hsz : szOK 42 6 = true := by decide

theorem lg_parts (j : Nat) : genT j = unpack 42 6 (lg j) ∧ Cn (lg j) := by
  have h2 : g₃T = unpack 42 6 (L34R.G 2) := by
    have := L34Cert.bindS.2 2 (by decide)
    rwa [show gensS[2]! = g₃T from rfl] at this
  match j with
  | 0 => exact ⟨L34Cert.e1, L34Cert.cnG (k := 0) (by decide)⟩
  | 1 => exact ⟨L34Cert.e2, L34Cert.cnG (k := 1) (by decide)⟩
  | 2 => exact ⟨h2, L34Cert.cnG (k := 2) (by decide)⟩
  | j + 3 =>
    have e : lg (j + 3) = L34R.G 2 := by
      unfold lg
      simp
    rw [e]
    exact ⟨h2, L34Cert.cnG (k := 2) (by decide)⟩

theorem fold_unpack : ∀ (wd : List Nat) (acc : Nat), Cn acc →
    wd.foldl (fun t j => comp 42 t (genT j)) (unpack 42 6 acc) = unpack 42 6 (wfoldL lg acc wd) ∧
      Cn (wfoldL lg acc wd)
  | [], acc, h => ⟨rfl, h⟩
  | j :: wd, acc, h => by
    rw [List.foldl_cons, (lg_parts j).1, comp_unpack' h (lg_parts j).2]
    exact fold_unpack wd _ (CFSG.KC.BfsPin.canonK_pcomp h (lg_parts j).2)

theorem wordTab_unpack (wd : List Nat) :
    wordTab wd = unpack 42 6 (wfoldL lg (pidn 42 6) wd) ∧ Cn (wfoldL lg (pidn 42 6) wd) := by
  unfold wordTab
  rw [idTab_unpack' hsz]
  exact fold_unpack wd _ (canon_pidn hsz)

theorem parts : ETE.k = 4 ∧ (∀ j < 4, ETE.G j = wfoldL lg (pidn 42 6) (lget2 wT₀ j)) ∧
    GensOK 42 6 EEE.k EEE.G e16Gens := by
  obtain ⟨h1, h2, h3⟩ := (by simpa only [bAnd_iff] using k_gens :
    Nat.beq ETE.k 4 = true ∧ _ ∧ gensK e16Gens 42 6 EEE.k EEE.G = true)
  exact ⟨Nat.eq_of_beq_eq_true h1,
    fun j hj => Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 h2 j hj), gensOK_of h3⟩

theorem hds : penumHdK (pidn 42 6) ETE.cnt 64 ETE.T ETE.PL = true ∧
    penumHdK (pidn 42 6) EEE.cnt 16 EEE.T EEE.PL = true ∧ EEE.cnt = 16 := by
  obtain ⟨h1, h2, h3⟩ := (by simpa only [bAnd_iff] using k_hd :
    penumHdK (pidn 42 6) ETE.cnt 64 ETE.T ETE.PL = true ∧
      penumHdK (pidn 42 6) EEE.cnt 16 EEE.T EEE.PL = true ∧ Nat.beq EEE.cnt 16 = true)
  exact ⟨h1, h2, Nat.eq_of_beq_eq_true h3⟩

theorem cntT_le : ETE.cnt ≤ 64 := by
  have h := hds.1
  unfold penumHdK at h
  obtain ⟨-, h, -⟩ := (by simpa only [bAnd_iff] using h :
    Nat.blt 0 ETE.cnt = true ∧ Nat.ble ETE.cnt 64 = true ∧ _)
  exact Nat.le_of_ble_eq_true h

theorem gensT : GensOK 42 6 ETE.k ETE.G (wordTabs wT₀) := by
  refine ⟨by rw [parts.1]; rfl, fun j hj => ?_⟩
  rw [parts.1] at hj
  have e : (wordTabs wT₀)[j]! = wordTab (wT₀.getD j []) := by
    unfold wordTabs
    rw [getElem!_pos _ j (by simp [wT₀]; omega), List.getElem_toArray, List.getElem_map,
      List.getD_eq_getElem]
  rw [e, parts.2.1 j hj, lget2_eq]
  exact wordTab_unpack _

theorem ptT : ∀ i < ETE.cnt, penumPtK 42 6 (mask 6) (42 * 6) false ETE.G ETE.GI ETE.k ETE.cnt
    ETE.T ETE.PL ETE.POS ETE.SRT ETE.SRI i = true := fun i hi =>
  penumSl_spec k_slT i (Nat.zero_le _) (by have := cntT_le; omega) hi

theorem ptE : ∀ i < EEE.cnt, penumPtK 42 6 (mask 6) (42 * 6) false EEE.G EEE.GI EEE.k EEE.cnt
    EEE.T EEE.PL EEE.POS EEE.SRT EEE.SRI i = true := fun i hi =>
  penumSl_spec k_slE i (Nat.zero_le _) (by rw [hds.2.2] at hi; omega) hi

theorem encT : enumBFS 42 (wordTabs wT₀) 64 = penumRec 42 6 ETE.cnt ETE.T ETE.PL ∧
    enumOK 42 (wordTabs wT₀) (penumRec 42 6 ETE.cnt ETE.T ETE.PL) = true :=
  penumK_left_sound hsz gensT hds.1 ptT

theorem encE : enumBFS 42 e16Gens 16 = penumRec 42 6 EEE.cnt EEE.T EEE.PL ∧
    enumOK 42 e16Gens (penumRec 42 6 EEE.cnt EEE.T EEE.PL) = true :=
  penumK_left_sound hsz parts.2.2 hds.2.1 ptE

theorem recE_get {i : Nat} (hi : i < 16) :
    (penumRec 42 6 EEE.cnt EEE.T EEE.PL).tabs[i]! = unpack 42 6 (EEE.T i) := by
  rw [getElem!_pos _ i (by simp [penumRec, hds.2.2, hi])]
  simp [penumRec]

theorem inT {j : Nat} (hj : j < 4) : ∃ i < ETE.cnt, ETE.T i = EEE.G j := by
  have h := CFSG.KS.Raw.Orb.allN_iff.1 k_in j hj
  by_contra hn
  have : allN ETE.cnt (fun q => (Nat.beq (ETE.T q) (EEE.G j)).not) = true :=
    CFSG.KS.Raw.Orb.allN_iff.2 fun q hq => by
      cases hb : Nat.beq (ETE.T q) (EEE.G j)
      · rfl
      · exact absurd ⟨q, hq, Nat.eq_of_beq_eq_true hb⟩ hn
  rw [this] at h
  exact Bool.false_ne_true h

theorem e16_true : l34E16Check (wordTabs wT₀) = true := by
  have hk4 : EEE.k = 4 := parts.2.2.1.symm
  unfold l34E16Check
  simp only [encT.1, encE.1, encT.2, encE.2, Bool.true_and, Bool.and_true, Bool.and_eq_true]
  have hsE : (penumRec 42 6 EEE.cnt EEE.T EEE.PL).tabs.size = 16 := by
    rw [penumRec_eq, Array.size_ofFn, hds.2.2]
  refine ⟨⟨?_, by rw [hsE]; rfl⟩, ?_⟩
  · rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro j hj
    have hj4 : j < 4 := by simpa [e16Gens] using hj
    rw [(parts.2.2.2 j (hk4 ▸ hj4)).1]
    obtain ⟨i, hi, e⟩ := inT hj4
    exact (found_penumRec_iff ptT (parts.2.2.2 j (hk4 ▸ hj4)).2).2 ⟨i, hi, e⟩
  · rw [hsE, CFSG.KS.BfsReplay.allBelow_iff]
    intro a ha
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (CFSG.KS.Raw.Orb.allN_iff.1 k_ab a ha)
    have ca := penumPt_canon (ptE a (hds.2.2 ▸ ha))
    rw [Bool.and_eq_true, recE_get ha, comp_unpack' ca ca, idTab_unpack' hsz,
      CFSG.KC.L34KSnd.beq_unpack (CFSG.KC.BfsPin.canonK_pcomp ca ca) (canon_pidn hsz),
      CFSG.KS.BfsReplay.allBelow_iff]
    refine ⟨h1, fun b hb => ?_⟩
    have cb := penumPt_canon (ptE b (hds.2.2 ▸ hb))
    rw [recE_get hb, comp_unpack' ca cb, comp_unpack' cb ca,
      CFSG.KC.L34KSnd.beq_unpack (CFSG.KC.BfsPin.canonK_pcomp ca cb)
        (CFSG.KC.BfsPin.canonK_pcomp cb ca)]
    exact CFSG.KS.Raw.Orb.allN_iff.1 h2 b hb

end CertificateChecks.KernelLC.L34E16

end

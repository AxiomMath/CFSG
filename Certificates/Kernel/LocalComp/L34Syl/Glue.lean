module

public import Certificates.Kernel.LocalComp.L34Syl.Chk
public import Certificates.Kernel.LocalComp.L34Para.Final
public import CFSG.Certificates.Kernel.L34FixPowSound
public import CFSG.Certificates.Kernel.L34Scan2Sound
public import CFSG.Certificates.Kernel.L34InvSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KC.L34KSnd CFSG.KC.L34FixPow CFSG.KC.L34Scan2 CFSG.KC.L34W CertificateChecks.KernelLC.L34X
open CertificateChecks.KernelLC.L34Cert CFSG.PSL3Four.Native
open CFSG.KC.L34Scan (strictB_app pts_get' orB_eq)
open CFSG.KLie.CT (andB orB notB)

theorem filter_get {N j : Nat} {T : Nat → Nat} {f : Tab → Bool}
    (hj : j < ((pts 42 6 N T).filter f).size) :
    ∃ i < N, f (unpack 42 6 (T i)) = true ∧ ((pts 42 6 N T).filter f)[j]! = unpack 42 6 (T i) := by
  rw [getElem!_pos _ j hj]
  obtain ⟨hm, hf⟩ := Array.mem_filter.1 (Array.getElem_mem hj)
  obtain ⟨i, hi, e⟩ := CFSG.KC.L34Inv.mem_pts_iff.1 hm
  exact ⟨i, hi, by rw [e]; exact hf, e.symm⟩

theorem filter_size {N : Nat} {T : Nat → Nat} (f : Tab → Bool) :
    ((pts 42 6 N T).filter f).size =
      ((List.range N).filter fun i => f (unpack 42 6 (T i))).length := by
  rw [← Array.length_toList, Array.toList_filter]
  unfold pts
  rw [pts_toList (N := N) (fun i => unpack 42 6 (T i)), List.filter_map, List.length_map]
  rfl

theorem memTab_of {N x : Nat} {T : Nat → Nat} (h : memL N T x = true) :
    memTab (pts 42 6 N T) (unpack 42 6 x) = true := by
  obtain ⟨q, hq, e⟩ := memL_spec h
  unfold memTab
  rw [size_pts, anyBelow_iff]
  exact ⟨q, hq, by rw [pts_get' hq, e]; exact beq_self_eq_true _⟩

theorem cntR_len (f : Nat → Bool) : ∀ N,
    CFSG.KC.HeAutK.cntR f 0 N = ((List.range N).filter f).length
  | 0 => rfl
  | N + 1 => by
    rw [CFSG.KC.HeAutK.cntR_succ, cntR_len f N, Nat.zero_add, List.range_succ, List.filter_append,
      List.length_append]
    cases h : f N <;> simp [h]

theorem hP : (enumBFS 42 pGens 64).tabs = pts 42 6 64 L34SyP.T ∧
    enumOK 42 pGens (enumBFS 42 pGens 64) = true ∧ (∀ i < 64, Cn (L34SyP.T i)) ∧
    CFSG.KS.PEnum.GensOK 42 6 4 L34SyP.G pGens :=
  CertificateChecks.KernelLC.L34Para.rec_of kSylP_gens kSylP_hd kSylP_sl

theorem hF : (enumBFS 42 (fGens ()) 16).tabs = pts 42 6 16 L34SyF.T ∧
    enumOK 42 (fGens ()) (enumBFS 42 (fGens ()) 16) = true ∧ (∀ k < 16, Cn (L34SyF.T k)) ∧
    CFSG.KS.PEnum.GensOK 42 6 4 L34SyF.G (fGens ()) :=
  CertificateChecks.KernelLC.L34Para.rec_of kSylF_gens kSylF_hd kSylF_sl

theorem cP {i : Nat} (hi : i < 64) : Cn (L34SyP.T i) := hP.2.2.1 i hi

theorem cF {k : Nat} (hk : k < 16) : Cn (L34SyF.T k) := hF.2.2.1 k hk

theorem gN : CFSG.KS.PEnum.GensOK 42 6 1 L34SyN.N #[nT] := CFSG.KS.PEnum.gensOK_of kSylN_gens

theorem parts : (∀ j < 4, memL 20160 CertificateChecks.KernelLC.L34S.T (L34SyP.G j) = true) ∧
    memL 20160 CertificateChecks.KernelLC.L34S.T (L34SyN.N 0) = true ∧ Cn (L34SyN.N 1) ∧
    pcomp 42 6 (mask 6) (L34SyN.N 0) (L34SyN.N 1) = pidn 42 6 ∧
    CFSG.KC.HeAutK.cntR (fun i => cenP (L34SyP.T i)) 0 64 = 4 ∧
    (∀ i < 64, sylPt (RP 2) (L34SyN.N 0) (L34SyN.N 1) (pidn 42 6) i = true) ∧
    ∀ k < 16, sylF (pidn 42 6) k = true := by
  have h := kSyl
  unfold sylK at h
  rw [strictB_app, strictB_app, strictB_app, strictB_app] at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h⟩ := andB_iff.1 h
  obtain ⟨h6, h7⟩ := andB_iff.1 h
  exact ⟨CFSG.KS.Raw.Orb.allN_iff.1 h1, h2, h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5, CFSG.KS.Raw.Orb.allN_iff.1 h6, CFSG.KS.Raw.Orb.allN_iff.1 h7⟩

theorem ptP {i : Nat} (hi : i < 64) : iv i < 64 ∧
    pcomp 42 6 (mask 6) (L34SyP.T i) (L34SyP.T (iv i)) = pidn 42 6 ∧
    fixPow (L34SyP.T i) 4 = true ∧
    memL 64 L34SyP.T (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (RP 2) (L34SyP.T i)) (RP 2)) =
      true ∧
    memL 64 L34SyP.T
      (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (L34SyN.N 0) (L34SyP.T i)) (L34SyN.N 1)) = true ∧
    memL 64 L34SyP.T
      (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (L34SyN.N 1) (L34SyP.T i)) (L34SyN.N 0)) = true ∧
    (cenP (L34SyP.T i) = true →
      cenTail (RP 2) (L34SyN.N 0) (L34SyN.N 1) (pidn 42 6) i (L34SyP.T i) = true) := by
  have h := parts.2.2.2.2.2.1 i hi
  unfold sylPt at h
  rw [strictB_app] at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h⟩ := andB_iff.1 h
  obtain ⟨h6, h7⟩ := andB_iff.1 h
  refine ⟨Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true h2, h3, h4, h5, h6, fun hc => ?_⟩
  rcases orB_iff.1 h7 with h | h
  · rw [hc] at h
    exact absurd h (by decide)
  · exact h

theorem tailP {i : Nat} (hi : i < 64) (hc : cenP (L34SyP.T i) = true) :
    Nat.beq (pcomp 42 6 (mask 6) (L34SyP.T i) (L34SyP.T i)) (pidn 42 6) = true ∧
    commPt 42 6 (L34SyP.T i) (RP 2) = true ∧ wa i < 64 ∧ wb i < 64 ∧ comW i = L34SyP.T i ∧
    memL 16 L34SyF.T (L34SyP.T i) = true ∧
    ∀ j < 64, cenP (L34SyP.T j) = true →
      fusePt (L34SyN.N 0) (L34SyN.N 1) (pidn 42 6) (L34SyP.T i) (L34SyP.T j) = true := by
  have h := (ptP hi).2.2.2.2.2.2 hc
  unfold cenTail at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h⟩ := andB_iff.1 h
  obtain ⟨h6, h7⟩ := andB_iff.1 h
  refine ⟨h1, h2, Nat.le_of_ble_eq_true h3, Nat.le_of_ble_eq_true h4, Nat.eq_of_beq_eq_true h5,
    h6, fun j hj hcj => ?_⟩
  have h8 := CFSG.KS.Raw.Orb.allN_iff.1 h7 j hj
  beta_reduce at h8
  rw [strictB_app] at h8
  rcases orB_iff.1 h8 with h | h
  · rw [hcj] at h
    exact absurd h (by decide)
  · exact h

theorem fP {k : Nat} (hk : k < 16) : memL 64 L34SyP.T (L34SyF.T k) = true ∧
    Nat.beq (pcomp 42 6 (mask 6) (L34SyF.T k) (L34SyF.T k)) (pidn 42 6) = true ∧
    ∀ l < 16, commPt 42 6 (L34SyF.T k) (L34SyF.T l) = true := by
  have h := parts.2.2.2.2.2.2 k hk
  unfold sylF at h
  rw [strictB_app] at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h3⟩ := andB_iff.1 h
  exact ⟨h1, h2, CFSG.KS.Raw.Orb.allN_iff.1 h3⟩

theorem hinv : (∀ k < 64, ((pts 42 6 64 L34SyP.T).map (invTab 42))[k]! =
      unpack 42 6 (L34SyP.T (iv k))) ∧
    invsOK 42 (pts 42 6 64 L34SyP.T) ((pts 42 6 64 L34SyP.T).map (invTab 42)) = true :=
  invsOK_of_pcomp (size_pts 42 6 64 _) (fun k hk => pts_get' hk) fun k hk =>
    ⟨cP hk, cP (ptP hk).1, (ptP hk).2.1⟩

theorem cen_eq {x : Nat} (hx : Cn x) :
    (allBelow (pts 42 6 64 L34SyP.T).size fun j =>
      comp 42 (unpack 42 6 x) (pts 42 6 64 L34SyP.T)[j]! ==
        comp 42 (pts 42 6 64 L34SyP.T)[j]! (unpack 42 6 x)) = cenP x := by
  rw [Bool.eq_iff_iff, size_pts, CFSG.KS.BfsReplay.allBelow_iff]
  unfold cenP
  rw [CFSG.KS.Raw.Orb.allN_iff]
  refine forall_congr' fun j => imp_congr_right fun hj => ?_
  rw [pts_get' hj, beq_iff_eq, commPt_iff hx (cP hj)]

theorem et_size {f : Tab → Bool}
    (hf : ∀ i < 64, f (unpack 42 6 (L34SyP.T i)) = cenP (L34SyP.T i)) :
    ((pts 42 6 64 L34SyP.T).filter f).size = 4 := by
  rw [filter_size, List.filter_congr (q := fun i => cenP (L34SyP.T i))
    fun i hi => hf i (List.mem_range.1 hi), ← cntR_len]
  exact parts.2.2.2.2.1

theorem et_get {f : Tab → Bool} {j : Nat} (hj : j < ((pts 42 6 64 L34SyP.T).filter f).size)
    (hf : ∀ i < 64, f (unpack 42 6 (L34SyP.T i)) = cenP (L34SyP.T i)) :
    ∃ i < 64, cenP (L34SyP.T i) = true ∧
      ((pts 42 6 64 L34SyP.T).filter f)[j]! = unpack 42 6 (L34SyP.T i) := by
  obtain ⟨i, hi, hc, e⟩ := filter_get hj
  exact ⟨i, hi, by rw [← hf i hi]; exact hc, e⟩

theorem cr : Cn (RP 2) := cnRP (by decide)

theorem cn0 : Cn (L34SyN.N 0) := (gN.2 0 (by decide)).2

theorem hN : nT = unpack 42 6 (L34SyN.N 0) := (gN.2 0 (by decide)).1

theorem hnI : invTab 42 nT = unpack 42 6 (L34SyN.N 1) := by
  rw [hN]
  exact invTab_eq_of_pcomp cn0 parts.2.2.1 parts.2.2.2.1

theorem syl_true : l34SylCheck (enumBFS 42 gensS 20160).tabs = true := by
  have cn1 : Cn (L34SyN.N 1) := parts.2.2.1
  have hcen : ∀ i < 64, (fun t => allBelow (pts 42 6 64 L34SyP.T).size fun j =>
      comp 42 t (pts 42 6 64 L34SyP.T)[j]! == comp 42 (pts 42 6 64 L34SyP.T)[j]! t)
        (unpack 42 6 (L34SyP.T i)) = cenP (L34SyP.T i) := fun i hi => cen_eq (cP hi)
  unfold l34SylCheck
  dsimp only
  rw [hS.1, hP.1, hF.1]
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  refine ⟨?_, hP.2.1, size_pts _ _ _ _, hinv.2, ?_, ?_, et_size ?_, ?_, hF.2.1,
    size_pts _ _ _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hP.2.2.2.1, CFSG.KS.BfsReplay.allBelow_iff]
    intro j hj
    rw [(hP.2.2.2.2 j hj).1]
    exact memTab_of (parts.1 j hj)
  · rw [size_pts, CFSG.KS.BfsReplay.allBelow_iff]
    intro k hk
    beta_reduce
    rw [pts_get' hk, fixPow_eq (cP hk)]
    exact (ptP hk).2.2.1
  · rw [size_pts, CFSG.KS.BfsReplay.allBelow_iff]
    intro k hk
    beta_reduce
    rw [pts_get' hk, r3_eq]
    unfold conjTab
    rw [comp_unpack' cr (cP hk), comp_unpack' (canonK_pcomp cr (cP hk)) cr]
    exact found_of_memL (ptP hk).2.2.2.1
  · exact hcen
  · rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro k hk
    beta_reduce
    obtain ⟨i, hi, hc, e⟩ := et_get hk hcen
    obtain ⟨t1, t2, t3, t4, t5, -, -⟩ := tailP hi hc
    have cx := cP hi
    rw [e, r3_eq, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [comp_unpack' cx cx, idTab42, beq_unpack (canonK_pcomp cx cx) cn_pidn]
      exact t1
    · rw [beq_iff_eq]
      exact ((commPt_iff cx cr).1 t2).symm
    · rw [size_pts, anyBelow_iff]
      refine ⟨wa i, t3, ?_⟩
      beta_reduce
      rw [anyBelow_iff]
      refine ⟨wb i, t4, ?_⟩
      have ca := cP t3
      have cb := cP t4
      have cai := cP (ptP t3).1
      have cbi := cP (ptP t4).1
      rw [pts_get' t3, pts_get' t4, hinv.1 _ t3, hinv.1 _ t4]
      unfold commTab
      rw [comp_unpack' ca cb, comp_unpack' (canonK_pcomp ca cb) cai,
        comp_unpack' (canonK_pcomp (canonK_pcomp ca cb) cai) cbi,
        beq_unpack (canonK_pcomp (canonK_pcomp (canonK_pcomp ca cb) cai) cbi) cx]
      unfold comW at t5
      rw [t5]
      exact Nat.beq_refl _
  · rw [size_pts, CFSG.KS.BfsReplay.allBelow_iff]
    intro k hk
    beta_reduce
    obtain ⟨f1, f2, f3⟩ := fP hk
    have cy := cF hk
    rw [pts_get' hk, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨found_of_memL f1, ?_⟩, ?_⟩
    · rw [comp_unpack' cy cy, idTab42, beq_unpack (canonK_pcomp cy cy) cn_pidn]
      exact f2
    · rw [CFSG.KS.BfsReplay.allBelow_iff]
      intro l hl
      beta_reduce
      rw [pts_get' hl, beq_iff_eq]
      exact (commPt_iff cy (cF hl)).1 (f3 l hl)
  · rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro k hk
    beta_reduce
    obtain ⟨i, hi, hc, e⟩ := et_get hk hcen
    rw [e]
    exact found_of_memL (tailP hi hc).2.2.2.2.2.1
  · rw [hN]
    exact memTab_of parts.2.1
  · rw [hnI, hN]
    unfold invsOK
    simp only [Bool.and_eq_true, beq_iff_eq, CFSG.KS.BfsReplay.allBelow_iff]
    refine ⟨rfl, fun k hk => ?_⟩
    have hk0 : k = 0 := by
      change k < 1 at hk
      omega
    subst hk0
    exact ⟨size_unpack _, comp_inv_of_pcomp cn0 cn1 parts.2.2.2.1⟩
  · rw [hnI, hN, size_pts, CFSG.KS.BfsReplay.allBelow_iff]
    intro k hk
    beta_reduce
    have cx := cP hk
    rw [pts_get' hk, Bool.and_eq_true]
    unfold conjTab
    rw [comp_unpack' cn0 cx, comp_unpack' (canonK_pcomp cn0 cx) cn1, comp_unpack' cn1 cx,
      comp_unpack' (canonK_pcomp cn1 cx) cn0]
    exact ⟨found_of_memL (ptP hk).2.2.2.2.1, found_of_memL (ptP hk).2.2.2.2.2.1⟩
  · rw [hnI, hN, CFSG.KS.BfsReplay.allBelow_iff]
    intro a ha
    beta_reduce
    rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro b hb
    beta_reduce
    obtain ⟨i, hi, hc, e⟩ := et_get ha hcen
    obtain ⟨j, hj, hcj, e'⟩ := et_get hb hcen
    have cx := cP hi
    have cy := cP hj
    have hf := (tailP hi hc).2.2.2.2.2.2 j hj hcj
    unfold fusePt at hf
    rw [e, e', idTab42, beq_unpack cx cn_pidn, beq_unpack cy cn_pidn, beq_unpack cx cy]
    unfold conjTab
    rw [comp_unpack' cn0 cx, comp_unpack' (canonK_pcomp cn0 cx) cn1, comp_unpack' cn1 cx,
      comp_unpack' (canonK_pcomp cn1 cx) cn0,
      beq_unpack (canonK_pcomp (canonK_pcomp cn0 cx) cn1) cy,
      beq_unpack (canonK_pcomp (canonK_pcomp cn1 cx) cn0) cy]
    simp only [orB_eq, Bool.or_assoc] at hf ⊢
    exact hf

end CertificateChecks.KernelLC.L34Syl

end

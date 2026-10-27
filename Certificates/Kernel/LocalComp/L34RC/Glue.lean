module

public import Certificates.Kernel.LocalComp.L34RC.C07a
public import Certificates.Kernel.LocalComp.L34RC.C07b
public import Certificates.Kernel.LocalComp.L34RC.C07c
public import Certificates.Kernel.LocalComp.L34RC.C07d
public import Certificates.Kernel.LocalComp.L34RC.Four
public import Certificates.Kernel.LocalComp.L34ScanFinal
public import Certificates.Kernel.LocalComp.L34T3.Glue
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRCertInputs
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34RC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34Scan CFSG.KC.L34Scan2 CFSG.KC.L34W CFSG.KC.L34Pow CertificateChecks.KernelLC.L34X
open CertificateChecks.KernelLC.L34Cert
open CertificateChecks.KernelLC.L34T3 (sapp)
open CertificateChecks.KernelLC.L34Scan (canonC)
open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KLie.CT (andB orB notB)

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem strictN_app' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem nf_of {a : Bool} (h : notB a = false) : a = true := by
  cases a
  · exact absurd h (by decide)
  · rfl

theorem rc_of {lo n : Nat} (h : rc22207 lo n = true) {i : Nat} (h1 : 1344 * lo ≤ i)
    (h2 : i < 1344 * (lo + n)) :
    allPt (RP 0) (RP 1) (RP 2) (RP 3) (pidn 42 6) (L34RU.Q i) (L34R.T i) = true := by
  unfold rc22207 at h
  rw [sapp, sapp, sapp, sapp, sapp] at h
  have h' := allN_spec h (i / 1344 - lo) (by omega)
  beta_reduce at h'
  have h'' := allN_spec h' (i % 1344) (Nat.mod_lt _ (by decide))
  beta_reduce at h''
  have e : Nat.add (Nat.mul 1344 (Nat.add lo (i / 1344 - lo))) (i % 1344) = i := by
    change 1344 * (lo + (i / 1344 - lo)) + i % 1344 = i
    omega
  rw [e, sapp, sapp] at h''
  exact h''

theorem allPtAll : ∀ i < 241920,
    allPt (RP 0) (RP 1) (RP 2) (RP 3) (pidn 42 6) (L34RU.Q i) (L34R.T i) = true := by
  intro i hi
  rcases Nat.lt_or_ge i (1344 * 15) with h | h0
  · exact rc_of k07c0 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 30) with h | h1
  · exact rc_of k07c1 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 45) with h | h2
  · exact rc_of k07c2 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 60) with h | h3
  · exact rc_of k07c3 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 75) with h | h4
  · exact rc_of k07c4 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 90) with h | h5
  · exact rc_of k07c5 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 105) with h | h6
  · exact rc_of k07c6 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 120) with h | h7
  · exact rc_of k07c7 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 135) with h | h8
  · exact rc_of k07c8 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 150) with h | h9
  · exact rc_of k07c9 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 165) with h | h10
  · exact rc_of k07c10 (by omega) (by omega)
  · exact rc_of k07c11 (by omega) (by omega)

theorem parts {i : Nat} (hi : i < 241920) :
    sqPt (L34RU.Q i) (L34R.T i) = true ∧ cenPt (RP 1) 168 L34C2.P (pidn 42 6) (L34R.T i) = true ∧
      cenPt (RP 2) 60 L34C3.P (pidn 42 6) (L34R.T i) = true ∧
      oddPt (RP 0) L34C1.P (pidn 42 6) (L34R.T i) = true ∧
      invPt4 91 (RP 3) (pidn 42 6) (L34R.T i) = true := by
  have h := allPtAll i hi
  unfold allPt at h
  obtain ⟨a, h⟩ := andB_iff.1 h
  obtain ⟨b, h⟩ := andB_iff.1 h
  obtain ⟨c, h⟩ := andB_iff.1 h
  obtain ⟨d, f⟩ := andB_iff.1 h
  exact ⟨a, b, c, d, f⟩

theorem commT_eq {x g : Nat} (hx : Cn x) (hg : Cn g) :
    commT (unpack 42 6 x) (unpack 42 6 g) = commPt 42 6 x g := by
  rw [Bool.eq_iff_iff]
  unfold commT
  rw [beq_iff_eq, commPt_iff hx hg]

theorem iterPt_eq (x k p : Nat) : iterPt x k p = (pg 6 (mask 6) x)^[k] p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl

theorem iter_lt {x : Nat} (hx : Cn x) {p : Nat} (hp : p < 42) :
    ∀ k, (pg 6 (mask 6) x)^[k] p < 42
  | 0 => hp
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact canon_lt hx (iter_lt hx hp k)

theorem pg_pow2K {x : Nat} (hx : Cn x) :
    ∀ k, ∀ p < 42, pg 6 (mask 6) (pow2K 42 6 k x) p = (pg 6 (mask 6) x)^[2 ^ k] p
  | 0, p, _ => rfl
  | k + 1, p, hp => by
    rw [pow2K_succ, pg_pcomp' (pow2K_canon hx k) hp,
      pg_pow2K hx k _ (canon_lt (pow2K_canon hx k) hp), pg_pow2K hx k p hp,
      ← Function.iterate_add_apply, pow_succ, mul_two]

theorem sq_sound {x f : Nat} (hx : Cn x) (h : sqPt f x = true) :
    (!(CFSG.ComponentClassification.GrSLit.powTwoTab (unpack 42 6 x) 8 == idTab 42) ||
      found (indexOf (pts 42 6 20160 L34S.T)) (pts 42 6 20160 L34S.T)
        (comp 42 (unpack 42 6 x) (unpack 42 6 x))) = true := by
  unfold sqPt at h
  rcases orB_iff.1 h with h | h
  · obtain ⟨h1, h⟩ := andB_iff.1 h
    obtain ⟨h2, h3⟩ := andB_iff.1 h
    have b1 := Nat.le_of_ble_eq_true h1
    have b2 := Nat.le_of_ble_eq_true h2
    have hf : found (indexOf (pts 42 6 20160 L34S.T)) (pts 42 6 20160 L34S.T)
        (unpack 42 6 (pcomp 42 6 (mask 6) x x)) = true := by
      unfold pts
      exact found_pts (q := Nat.sub f 1) (by change f - 1 < 20160; omega)
        (Nat.eq_of_beq_eq_true h3)
    rw [comp_unpack' hx hx, hf, Bool.or_true]
  · obtain ⟨p, hp, hq⟩ := ex_of_notB_allN h
    rw [sapp] at hq
    obtain ⟨a, b⟩ := andB_iff.1 (nf_of hq)
    have hne : (pg 6 (mask 6) x)^[256 % retK x p] p ≠ p := by
      rw [← iterPt_eq]
      exact Nat.ne_of_beq_eq_false (notB_iff.1 b)
    have hper : Function.IsPeriodicPt (pg 6 (mask 6) x) (retK x p) p := by
      unfold Function.IsPeriodicPt Function.IsFixedPt
      rw [← iterPt_eq]
      exact Nat.eq_of_beq_eq_true a
    rw [hper.iterate_mod_apply] at hne
    have hpow : CFSG.ComponentClassification.GrSLit.powTwoTab (unpack 42 6 x) 8 ≠ idTab 42 := by
      intro e
      rw [powTwoTab_unpack hx, idTab42] at e
      have e' := unpack_inj' (pow2K_canon hx 8) cn_pidn e
      have h8 := pg_pow2K hx 8 p hp
      rw [e', pg_pidn' szOK42 hp] at h8
      exact hne h8.symm
    rw [beq_false_of_ne hpow]
    rfl

theorem outSq_true : outSqOK (pts 42 6 241920 L34R.T) (pts 42 6 20160 L34S.T) = true := by
  unfold outSqOK
  dsimp only
  rw [CFSG.KS.BfsReplay.allBelow_iff, size_pts]
  intro i hi
  rw [pts_get' hi]
  exact sq_sound (pinR.canon i hi) (parts hi).1

theorem cen_sound {N m r : Nat} {T CP : Nat → Nat} (hT : ∀ i < N, Cn (T i))
    (hc : ∀ c < m, Cn (CP c)) (hr : Cn r) (h : ∀ i < N, cenPt r m CP (pidn 42 6) (T i) = true) :
    centOK (pts 42 6 N T) (unpack 42 6 r) (pts 42 6 m CP) = true := by
  unfold centOK
  rw [CFSG.KS.BfsReplay.allBelow_iff, size_pts]
  intro i hi
  have hx := hT i hi
  have eall : (allBelow (pts 42 6 m CP).size fun j =>
      commT (pts 42 6 N T)[i]! (pts 42 6 m CP)[j]!) = allN m fun c => commPt 42 6 (T i) (CP c) := by
    rw [size_pts, Bool.eq_iff_iff, CFSG.KS.BfsReplay.allBelow_iff, CFSG.KS.Raw.Orb.allN_iff]
    refine forall_congr' fun c => imp_congr_right fun hcm => ?_
    rw [pts_get' hi, pts_get' hcm, commT_eq hx (hc c hcm)]
  rw [eall, pts_get' hi, commT_eq hx hr, idTab42, beq_unpack hx cn_pidn, beq_unpack hx hr]
  have h' := h i hi
  unfold cenPt at h'
  simpa only [orB_eq, notB_eq, Bool.not_and, Bool.or_assoc] using h'

theorem odd_sound {x r : Nat} {C : Nat → Nat} (hx : Cn x) (cr : Cn r) (hC : ∀ c < 64, Cn (C c))
    (h : oddPt r C (pidn 42 6) x = true) :
    (!(commT (unpack 42 6 x) (unpack 42 6 r) && powTab (unpack 42 6 x) 945 == idTab 42 &&
        !(unpack 42 6 x == idTab 42)) ||
      decide (countBelow (pts 42 6 64 C).size
        (fun i => commT (unpack 42 6 x) (pts 42 6 64 C)[i]!) ≤ 4)) = true := by
  have hpw : powTab (unpack 42 6 x) 945 = unpack 42 6 (ppowK x 945) :=
    (ppowK_spec hx (powTab (unpack 42 6 x)) rfl (fun _ => rfl) 945).2
  have hcnt : countBelow (pts 42 6 64 C).size
      (fun i => commT (unpack 42 6 x) (pts 42 6 64 C)[i]!) =
      CFSG.KC.HeAutK.cntR (fun c => commPt 42 6 x (C c)) 0 64 := by
    rw [CFSG.KC.HeAutK.cntR_eq, size_pts]
    unfold countBelow
    refine congrArg List.length (List.filter_congr fun c hc => ?_)
    have hc' := List.mem_range.1 hc
    rw [pts_get' hc', commT_eq hx (hC c hc')]
  rw [hcnt, commT_eq hx cr, hpw, idTab42, beq_unpack (ppowK_cn hx 945) cn_pidn,
    beq_unpack hx cn_pidn]
  unfold oddPt at h
  rw [with945_eq hx] at h
  rcases orB_iff.1 h with h | h
  · rw [notB_iff.1 h]
    rfl
  rcases orB_iff.1 h with h | h
  · rw [h]
    simp only [Bool.not_true, Bool.and_false, Bool.not_false, Bool.true_or]
  rcases orB_iff.1 h with h | h
  · rw [notB_iff.1 h]
    simp only [Bool.and_false, Bool.false_and, Bool.not_false, Bool.true_or]
  · rw [decide_eq_true (Nat.le_of_ble_eq_true h), Bool.or_true]

theorem innerOdd_true : innerOddOK (pts 42 6 241920 L34R.T) (pts 42 6 64 L34C1.P) = true := by
  unfold innerOddOK
  rw [CFSG.KS.BfsReplay.allBelow_iff, size_pts, r1_eq]
  intro i hi
  rw [pts_get' hi]
  exact odd_sound (pinR.canon i hi) (cnRP (by decide)) canonC.1 (parts hi).2.2.2.1

theorem topK_succ (e s n : Nat) : topK e s (n + 1) =
    Bool.rec (motive := fun _ => Nat) (topK e (pcomp 42 6 (mask 6) s s) n) s
      (Nat.beq (pcomp 42 6 (mask 6) s s) e) := by
  unfold topK
  exact strictN_app' _ (fun s2 => Bool.rec (motive := fun _ => Nat) (topK e s2 n) s
    (Nat.beq s2 e))

theorem topInv_eq : ∀ n {s : Nat}, Cn s →
    Cn (topK (pidn 42 6) s n) ∧ topInv (unpack 42 6 s) n = unpack 42 6 (topK (pidn 42 6) s n)
  | 0, _, hs => ⟨hs, rfl⟩
  | n + 1, s, hs => by
    have c2 := canonK_pcomp hs hs
    obtain ⟨ih1, ih2⟩ := topInv_eq n c2
    rw [topK_succ]
    unfold topInv
    rw [comp_unpack' hs hs, idTab42, beq_unpack c2 cn_pidn]
    cases hb : Nat.beq (pcomp 42 6 (mask 6) s s) (pidn 42 6)
    · exact ⟨ih1, by simpa using ih2⟩
    · exact ⟨hs, by simp⟩

theorem mem_invs {t : Tab} (ht : t ∈ (invs₄ (pts 42 6 241920 L34R.T)).toList) :
    ∃ a < 91, t = unpack 42 6 (L34RU.U a) ∧ Cn (L34RU.U a) := by
  unfold invs₄ at ht
  rw [Array.mem_toList_iff, Array.mem_filter] at ht
  obtain ⟨hR', hp⟩ := ht
  obtain ⟨i, hi, rfl⟩ := mem_pts (Array.mem_toList_iff.2 hR')
  have cx := pinR.canon i hi
  have cr := cnRP (j := 3) (by decide)
  rw [r4_eq, commT_eq cx cr, comp_unpack' cx cx, idTab42, beq_unpack (canonK_pcomp cx cx) cn_pidn,
    beq_unpack cx cn_pidn] at hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨⟨hc, hsq⟩, hne⟩ := hp
  have h := (parts hi).2.2.2.2
  unfold invPt4 at h
  rcases orB_iff.1 h with h | h
  · rw [hc] at h
    exact absurd h (by decide)
  rcases orB_iff.1 h with h | h
  · have hv : invPt 42 6 (L34R.T i) = true := (invPt_iff cx).2 (by
      rw [comp_unpack' cx cx, idTab42, Nat.eq_of_beq_eq_true hsq])
    rw [hv] at h
    exact absurd h (by decide)
  rcases orB_iff.1 h with h | h
  · rw [hne] at h
    exact absurd h (by decide)
  · obtain ⟨a, ha, e⟩ := memL_spec h
    exact ⟨a, ha, by rw [e], by rw [e]; exact cx⟩

theorem four_sound {u v : Nat} (cu : Cn u) (cv : Cn v) (h : fourPair (RP 3) (pidn 42 6) u v = true) :
    (commT (unpack 42 6 u) (unpack 42 6 v) ||
      !(CFSG.ComponentClassification.GrSLit.powTwoTab
          (comp 42 (unpack 42 6 u) (unpack 42 6 v)) 8 == idTab 42) ||
      (comp 42 (topInv (comp 42 (unpack 42 6 u) (unpack 42 6 v)) 8)
          (topInv (comp 42 (unpack 42 6 u) (unpack 42 6 v)) 8) == idTab 42 &&
        !(topInv (comp 42 (unpack 42 6 u) (unpack 42 6 v)) 8 == idTab 42) &&
        commT (topInv (comp 42 (unpack 42 6 u) (unpack 42 6 v)) 8) (unpack 42 6 u) &&
        !(topInv (comp 42 (unpack 42 6 u) (unpack 42 6 v)) 8 == r₄T ()) &&
        !(topInv (comp 42 (unpack 42 6 u) (unpack 42 6 v)) 8 == comp 42 (r₄T ()) (unpack 42 6 u)) &&
        !(topInv (comp 42 (unpack 42 6 u) (unpack 42 6 v)) 8 == unpack 42 6 u))) = true := by
  have cr := cnRP (j := 3) (by decide)
  have cs := canonK_pcomp cu cv
  obtain ⟨cz, ez⟩ := topInv_eq 8 cs
  rw [r4_eq, commT_eq cu cv, comp_unpack' cu cv, powTwoTab_unpack cs, ez, idTab42,
    beq_unpack (pow2K_canon cs 8) cn_pidn, comp_unpack' cz cz,
    beq_unpack (canonK_pcomp cz cz) cn_pidn, beq_unpack cz cn_pidn, commT_eq cz cu,
    beq_unpack cz cr, comp_unpack' cr cu, beq_unpack cz (canonK_pcomp cr cu), beq_unpack cz cu]
  unfold fourPair at h
  rw [sapp, sapp] at h
  simpa only [orB_eq, andB_eq, notB_eq, Bool.or_assoc, Bool.and_assoc] using h

theorem fourRow {a b : Nat} (ha : a < 91) (hb : b < 91) :
    fourPair (RP 3) (pidn 42 6) (L34RU.U a) (L34RU.U b) = true := by
  have hrow : ∀ {lo n : Nat}, fourRows lo n = true → lo ≤ a → a < lo + n →
      fourPair (RP 3) (pidn 42 6) (L34RU.U a) (L34RU.U b) = true := by
    intro lo n h h1 h2
    unfold fourRows at h
    rw [sapp, sapp] at h
    have h' := allN_spec h (a - lo) (by omega)
    beta_reduce at h'
    rw [show Nat.add lo (a - lo) = a from Nat.add_sub_cancel' h1, sapp] at h'
    exact allN_spec h' b hb
  rcases Nat.lt_or_ge a 31 with h | h
  · exact hrow k07f0 (by omega) (by omega)
  rcases Nat.lt_or_ge a 61 with h' | h'
  · exact hrow k07f1 (by omega) (by omega)
  · exact hrow k07f2 (by omega) (by omega)

theorem four_of {N : Array Tab}
    (hN : ∀ t ∈ N.toList, ∃ a < 91, t = unpack 42 6 (L34RU.U a) ∧ Cn (L34RU.U a)) :
    (allBelow N.size fun i => allBelow N.size fun j =>
      commT N[i]! N[j]! || !(CFSG.ComponentClassification.GrSLit.powTwoTab (comp 42 N[i]! N[j]!) 8 ==
        idTab 42) ||
      (comp 42 (topInv (comp 42 N[i]! N[j]!) 8) (topInv (comp 42 N[i]! N[j]!) 8) == idTab 42 &&
        !(topInv (comp 42 N[i]! N[j]!) 8 == idTab 42) &&
        commT (topInv (comp 42 N[i]! N[j]!) 8) N[i]! &&
        !(topInv (comp 42 N[i]! N[j]!) 8 == r₄T ()) &&
        !(topInv (comp 42 N[i]! N[j]!) 8 == comp 42 (r₄T ()) N[i]!) &&
        !(topInv (comp 42 N[i]! N[j]!) 8 == N[i]!))) = true := by
  refine CFSG.KS.BfsReplay.allBelow_iff.2 fun i hi => CFSG.KS.BfsReplay.allBelow_iff.2 fun j hj => ?_
  obtain ⟨a, ha, ea, ca⟩ := hN _ (Array.mem_toList_iff.2 (Array.getElem_mem hi))
  obtain ⟨b, hb, eb, cb⟩ := hN _ (Array.mem_toList_iff.2 (Array.getElem_mem hj))
  rw [getElem!_pos N i hi, getElem!_pos N j hj, ea, eb]
  exact four_sound ca cb (fourRow ha hb)

theorem four_true : fourOK (pts 42 6 241920 L34R.T) = true := by
  unfold fourOK
  dsimp only
  exact four_of fun t ht => mem_invs ht

theorem rCert_true : rCertOK = true := by
  unfold rCertOK
  dsimp only
  rw [hR.1, hS.1, cent1, cent2, cent3, outSq_true, innerOdd_true, four_true, r2_eq, r3_eq,
    cen_sound pinR.canon canonC.2.1 (cnRP (by decide)) fun i hi => (parts hi).2.1,
    cen_sound pinR.canon canonC.2.2 (cnRP (by decide)) fun i hi => (parts hi).2.2.1]
  rfl

end CertificateChecks.KernelLC.L34RC

end

module

public import Certificates.Kernel.LocalComp.L34V1.VAll
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Certificates.Kernel.L34ScanSound
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.L34PreSound

public section

namespace CertificateChecks.KernelLC.L34V1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KS.PEnum CFSG.KC.L34KSnd CertificateChecks.KernelLC.L34V1G
open CertificateChecks.KernelLC.L34Cert CFSG.PSL3Four.Native Certificates.Seitz77L34
open CFSG.KLie.CT (fget andB orB notB)

abbrev Cn (p : Nat) : Prop := canonK 42 6 (mask 6) (42 * 6) p = true
abbrev Cn16 (p : Nat) : Prop := canonK 16 5 (mask 5) (16 * 5) p = true

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem sz16 : szOK 16 5 = true := by decide

theorem fe_parts : GensOK 42 6 FE.k FE.G (fGens ()) ∧ FE.cnt = 16 ∧
    penumHdK (pidn 42 6) FE.cnt 16 FE.T FE.PL = true ∧
    penumSlK 42 6 (mask 6) (42 * 6) false FE.G FE.GI FE.k FE.cnt FE.T FE.PL FE.POS FE.SRT
      FE.SRI 0 16 = true ∧ ∀ a < 16, ∀ b < 16, a ≠ b → FE.T a ≠ FE.T b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := (by simpa only [bAnd_iff] using k_fe :
    gensK (fGens ()) 42 6 FE.k FE.G = true ∧ Nat.beq FE.cnt 16 = true ∧ _ ∧ _ ∧ _)
  refine ⟨gensOK_of h1, Nat.eq_of_beq_eq_true h2, h3, h4, fun a ha b hb hab e => ?_⟩
  have h := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h5 a ha) b hb
  rw [orB_eq, notB_eq, e, Nat.beq_refl] at h
  simp only [Bool.not_true, Bool.or_false] at h
  exact hab (Nat.eq_of_beq_eq_true h)

theorem fe_pt : ∀ i < FE.cnt, penumPtK 42 6 (mask 6) (42 * 6) false FE.G FE.GI FE.k FE.cnt FE.T
    FE.PL FE.POS FE.SRT FE.SRI i = true := fun i hi =>
  penumSl_spec fe_parts.2.2.2.1 i (Nat.zero_le _) (by rw [fe_parts.2.1] at hi; omega) hi

theorem fe_enc : enumBFS 42 (fGens ()) 16 = penumRec 42 6 FE.cnt FE.T FE.PL ∧
    enumOK 42 (fGens ()) (penumRec 42 6 FE.cnt FE.T FE.PL) = true :=
  penumK_left_sound (cap := 16) (by decide) fe_parts.1 fe_parts.2.2.1 fe_pt

@[expose] noncomputable def EFt : Array Tab := (penumRec 42 6 FE.cnt FE.T FE.PL).tabs

theorem EFt_size : EFt.size = 16 := by
  unfold EFt
  rw [penumRec_eq, Array.size_ofFn, fe_parts.2.1]

theorem EFt_get {i : Nat} (hi : i < 16) : EFt[i]! = unpack 42 6 (FE.T i) := by
  unfold EFt
  rw [getElem!_pos _ i (by rw [penumRec_eq, Array.size_ofFn, fe_parts.2.1]; exact hi)]
  simp [penumRec]

theorem cFE {i : Nat} (hi : i < 16) : Cn (FE.T i) :=
  penumPt_canon (fe_pt i (by rw [fe_parts.2.1]; exact hi))

theorem posOf_eq {p c : Nat} (hp : p < 16) (hc : FE.T p = c) :
    posOf (indexOf EFt) EFt (unpack 42 6 c) = p := by
  have hf : found (indexOf EFt) EFt (unpack 42 6 c) = true := by
    rw [found_indexOf_iff]
    exact ⟨p, by rw [EFt_size]; exact hp, by rw [EFt_get hp, hc]⟩
  unfold found at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hf
  obtain ⟨h1, h2⟩ := hf
  rw [EFt_size] at h1
  rw [EFt_get h1] at h2
  have e := CFSG.KC.L34KSnd.unpack_inj' (cFE h1) (hc ▸ cFE hp) h2
  by_contra hne
  exact fe_parts.2.2.2.2 _ h1 p hp hne (by rw [e, hc])

theorem vK_all : ∀ k < 241920, orB (rejF (L34R.T k)) (vK (pidn 42 6) k (L34R.T k)) = true := by
  intro k hk
  have hs : k / 1344 < 180 := by omega
  have h := CFSG.KS.Raw.Orb.allN_iff.1 (by
    have h1 := vsAll (k / 1344) hs
    unfold vs at h1
    rwa [CFSG.KC.L34Scan.strictB_app] at h1) (k % 1344) (Nat.mod_lt _ (by decide))
  rw [CFSG.KC.L34Scan.strictB_app] at h
  have e : Nat.add (Nat.mul 1344 (k / 1344)) (k % 1344) = k := Nat.div_add_mod k 1344
  rw [e, CFSG.KC.L34Scan.strictB_app] at h
  exact h

theorem fx_lt : ∀ j < 6, FX j < 42 := by decide

theorem fx_fix : ∀ j < 6, ∀ q < 16, pg 6 (mask 6) (FE.T q) (FX j) = FX j := fun j hj q hq =>
  Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 k_fix q hq) j hj)

theorem rejF_false {k : Nat} (hk : k < 241920)
    (hall : (allN 16 fun i => inFE (pc (pc (L34R.T k) (FE.T i))
      (pinvS 42 6 (mask 6) (L34R.T k)))) = true) : rejF (L34R.T k) = false := by
  have hPP := CFSG.KC.L34Pre.PinE.pp pinR k hk
  have hc : ∀ i < 16, ∃ q < 16, FE.T q = pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (L34R.T k)
      (FE.T i)) (pinvS 42 6 (mask 6) (L34R.T k)) := by
    intro i hi
    have h := CFSG.KS.Raw.Orb.allN_iff.1 hall i hi
    unfold inFE at h
    rw [notB_iff] at h
    refine Classical.byContradiction fun hn => ?_
    have h2 : allN 16 (fun q => notB (Nat.beq (FE.T q)
        (pc (pc (L34R.T k) (FE.T i)) (pinvS 42 6 (mask 6) (L34R.T k))))) = true := by
      rw [CFSG.KS.Raw.Orb.allN_iff]
      intro q hq
      cases e : Nat.beq (FE.T q) (pc (pc (L34R.T k) (FE.T i)) (pinvS 42 6 (mask 6) (L34R.T k)))
      · rfl
      · exact absurd ⟨q, hq, Nat.eq_of_beq_eq_true e⟩ hn
    rw [h] at h2
    exact absurd h2 (by decide)
  have hd : ∀ a < 16, ∀ b < 16, FE.T a = FE.T b → a = b := fun a ha b hb e =>
    Classical.byContradiction fun hne => fe_parts.2.2.2.2 a ha b hb hne e
  have h3 : allN 6 (fun j => notB (CFSG.KC.L34Pre.mvFix 6 16 FE.T (L34R.T k) (FX j))) = true := by
    rw [CFSG.KS.Raw.Orb.allN_iff]
    intro j hj
    rw [CFSG.KC.L34Pre.mvFix_false hPP (fun q hq => cFE hq) hd (fx_fix j hj) (fx_lt j hj) hc]
    rfl
  unfold rejF
  rw [h3]
  rfl

theorem point_facts {k : Nat} (hk : k < 241920) :
    Cn (pinvS 42 6 (mask 6) (L34R.T k)) ∧
      pc (L34R.T k) (pinvS 42 6 (mask 6) (L34R.T k)) = pidn 42 6 ∧
      ((allN 16 fun i => inFE (pc (pc (L34R.T k) (FE.T i)) (pinvS 42 6 (mask 6) (L34R.T k)))) =
          true →
        W k < 360 ∧ ∀ i < 16, yg (W k) i < 16 ∧
          FE.T (yg (W k) i) = pc (pc (L34R.T k) (FE.T i)) (pinvS 42 6 (mask 6) (L34R.T k))) := by
  have hPP := CFSG.KC.L34Pre.PinE.pp pinR k hk
  have h := vK_all k hk
  rw [orB_eq, Bool.or_eq_true] at h
  rcases h with hr | h
  · refine ⟨hPP.inv.1, CFSG.KC.L34Pre.pcomp_pinvS_PP hPP, fun hall => ?_⟩
    rw [rejF_false hk hall] at hr
    exact absurd hr (by decide)
  unfold vK at h
  rw [CFSG.KC.L34Scan.strictB_app] at h
  obtain ⟨h1, h⟩ := andT h
  obtain ⟨h2, h⟩ := andT h
  refine ⟨h1, Nat.eq_of_beq_eq_true h2, fun hall => ?_⟩
  rw [orB_eq, notB_eq, hall, CFSG.KC.L34Scan.strictB_app] at h
  simp only [Bool.not_true, Bool.false_or] at h
  obtain ⟨h3, h4⟩ := andT h
  refine ⟨Nat.blt_eq.mp h3, fun i hi => ?_⟩
  have h5 := CFSG.KS.Raw.Orb.allN_iff.1 h4 i hi
  rw [CFSG.KC.L34Scan.strictB_app] at h5
  obtain ⟨h6, h7⟩ := andT h5
  exact ⟨Nat.blt_eq.mp h6, Nat.eq_of_beq_eq_true h7⟩

theorem ky_parts : allN 360 yK = true ∧ YI.length = 46 ∧ (YI.all fun y => Nat.blt y 360) = true := by
  obtain ⟨h1, h2, h3⟩ := (by simpa only [bAnd_iff] using k_y :
    allN 360 yK = true ∧ Nat.beq YI.length 46 = true ∧ (YI.all fun y => Nat.blt y 360) = true)
  exact ⟨h1, Nat.eq_of_beq_eq_true h2, h3⟩

theorem yK_parts {y : Nat} (hy : y < 360) : Cn16 (YP y) ∧
    (Nat.beq (YP y) (pidn 16 5) ||
      decide (CFSG.PSL3Four.Native.countBelow 16 (fun i => Nat.beq (pg 5 (mask 5) (YP y) i) i) ≤ 4))
      = true ∧
    (Nat.beq (pc16 (YP y) (YP y)) (pidn 16 5) = true → y ∈ YI) := by
  have hk := ky_parts.1
  have h := CFSG.KS.Raw.Orb.allN_iff.1 hk y hy
  unfold yK at h
  rw [CFSG.KC.L34Scan.strictB_app] at h
  obtain ⟨h1, h⟩ := andT h
  obtain ⟨h2, h3⟩ := andT h
  refine ⟨h1, ?_, fun hp => ?_⟩
  · rw [orB_eq] at h2
    simpa [Nat.ble_eq] using h2
  · rw [orB_eq, notB_eq, hp] at h3
    simpa using h3

theorem acts_mem {x : Tab} (hx : x ∈ v1Acts EFt (pts 42 6 241920 L34R.T)) :
    ∃ y < 360, x = unpack 16 5 (YP y) := by
  obtain ⟨r, hr, hok, he⟩ := (mem_v1Acts _ _ _).1 hx
  unfold pts at hr
  rw [Array.mem_ofFn] at hr
  obtain ⟨⟨k, hk⟩, rfl⟩ := hr
  have ct := pinR.canon k hk
  obtain ⟨cti, hti, hw⟩ := point_facts hk
  have hinv : invTab 42 (unpack 42 6 (L34R.T k)) = unpack 42 6 (pinvS 42 6 (mask 6) (L34R.T k)) :=
    invTab_eq_of_pcomp ct cti hti
  have hconj : ∀ i < 16, conjTab 42 (unpack 42 6 (L34R.T k))
      (invTab 42 (unpack 42 6 (L34R.T k))) EFt[i]! =
      unpack 42 6 (pc (pc (L34R.T k) (FE.T i)) (pinvS 42 6 (mask 6) (L34R.T k))) := by
    intro i hi
    unfold conjTab pc
    rw [hinv, EFt_get hi, comp_unpack' ct (cFE hi), comp_unpack' (canonK_pcomp ct (cFE hi)) cti]
  have hall : (allN 16 fun i => inFE (pc (pc (L34R.T k) (FE.T i))
      (pinvS 42 6 (mask 6) (L34R.T k)))) = true := by
    rw [CFSG.KS.Raw.Orb.allN_iff]
    intro i hi
    unfold v1Ok at hok
    have h := (CFSG.KS.BfsReplay.allBelow_iff.1 hok) i (by rw [EFt_size]; exact hi)
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, EFt_size, hconj i hi] at h
    obtain ⟨h1, h2⟩ := h
    rw [EFt_get h1] at h2
    have cc : Cn (pc (pc (L34R.T k) (FE.T i)) (pinvS 42 6 (mask 6) (L34R.T k))) :=
      canonK_pcomp (canonK_pcomp ct (cFE hi)) cti
    have e := CFSG.KC.L34KSnd.unpack_inj' (cFE h1) cc h2
    unfold inFE
    rw [notB_iff]
    cases hA : allN 16 (fun q => notB (Nat.beq (FE.T q)
        (pc (pc (L34R.T k) (FE.T i)) (pinvS 42 6 (mask 6) (L34R.T k)))))
    · rfl
    · have := CFSG.KS.Raw.Orb.allN_iff.1 hA _ h1
      rw [e, Nat.beq_refl] at this
      exact absurd this (by decide)
  obtain ⟨hy, hyi⟩ := hw hall
  refine ⟨W k, hy, ?_⟩
  rw [← he]
  apply Array.ext
  · unfold v1Img
    rw [Array.size_map, EFt_size, size_unpack]
  · intro i h1 h2
    have hi : i < 16 := by simpa [size_unpack] using h2
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2]
    unfold v1Img
    rw [map_get _ (by rw [EFt_size]; exact hi), hconj i hi, CFSG.KC.BfsPin.unpack_get' hi]
    exact posOf_eq (hyi i hi).1 (hyi i hi).2

theorem countBelow_congr {f g : Nat → Bool} (h : ∀ i < 16, f i = g i) :
    CFSG.PSL3Four.Native.countBelow 16 f = CFSG.PSL3Four.Native.countBelow 16 g := by
  unfold CFSG.PSL3Four.Native.countBelow
  rw [List.filter_congr fun i hi => h i (List.mem_range.1 hi)]

theorem p1 {y : Nat} (hy : y < 360) :
    (unpack 16 5 (YP y) == idTab 16 ||
      decide (CFSG.PSL3Four.Native.countBelow 16 (fun i => (unpack 16 5 (YP y))[i]! == i) ≤ 4)) =
      true := by
  obtain ⟨c, h, -⟩ := yK_parts hy
  rw [idTab_unpack' sz16, CFSG.KC.L34KSnd.beq_unpack c (canon_pidn sz16),
    countBelow_congr (g := fun i => Nat.beq (pg 5 (mask 5) (YP y) i) i) fun i hi => by
      rw [CFSG.KC.BfsPin.unpack_get' hi, Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]]
  exact h

theorem yi_get {y : Nat} (h : y ∈ YI) : ∃ a < 46, YI.getD a 0 = y := by
  obtain ⟨a, ha, e⟩ := List.getElem_of_mem h
  have hl : YI.length = 46 := ky_parts.2.1
  refine ⟨a, by omega, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, Option.getD_some, e]

theorem yi_lt {a : Nat} (ha : a < 46) : YI.getD a 0 < 360 := by
  have hall := ky_parts.2.2
  have hl : YI.length = 46 := ky_parts.2.1
  rw [List.all_eq_true] at hall
  have hm : YI.getD a 0 ∈ YI := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.getElem_mem _
  exact Nat.blt_eq.mp (hall _ hm)

theorem inv_mem {x : Tab} (hx : x ∈ (v1Acts EFt (pts 42 6 241920 L34R.T)).filter
    fun s => comp 16 s s == idTab 16) : ∃ a < 46, x = unpack 16 5 (YP (YI.getD a 0)) := by
  rw [Array.mem_filter] at hx
  obtain ⟨hm, hsq⟩ := hx
  obtain ⟨y, hy, rfl⟩ := acts_mem hm
  have c := (yK_parts hy).1
  rw [comp_unpack' c c, idTab_unpack' sz16, CFSG.KC.L34KSnd.beq_unpack (canonK_pcomp c c) (canon_pidn sz16)] at hsq
  obtain ⟨a, ha, e⟩ := yi_get ((yK_parts hy).2.2 hsq)
  exact ⟨a, ha, by rw [e]⟩

theorem tri_ok {a b c : Nat} (ha : a < 46) (hb : b < 46) (hc : c < 46) :
    (unpack 16 5 (YP (YI.getD a 0)) == idTab 16 || unpack 16 5 (YP (YI.getD b 0)) == idTab 16 ||
      unpack 16 5 (YP (YI.getD b 0)) == unpack 16 5 (YP (YI.getD a 0)) ||
      !(comp 16 (unpack 16 5 (YP (YI.getD a 0))) (unpack 16 5 (YP (YI.getD b 0))) ==
          comp 16 (unpack 16 5 (YP (YI.getD b 0))) (unpack 16 5 (YP (YI.getD a 0))) &&
        comp 16 (unpack 16 5 (YP (YI.getD a 0))) (unpack 16 5 (YP (YI.getD c 0))) ==
          comp 16 (unpack 16 5 (YP (YI.getD c 0))) (unpack 16 5 (YP (YI.getD a 0))) &&
        comp 16 (unpack 16 5 (YP (YI.getD b 0))) (unpack 16 5 (YP (YI.getD c 0))) ==
          comp 16 (unpack 16 5 (YP (YI.getD c 0))) (unpack 16 5 (YP (YI.getD b 0)))) ||
      unpack 16 5 (YP (YI.getD c 0)) == idTab 16 ||
      unpack 16 5 (YP (YI.getD c 0)) == unpack 16 5 (YP (YI.getD a 0)) ||
      unpack 16 5 (YP (YI.getD c 0)) == unpack 16 5 (YP (YI.getD b 0)) ||
      unpack 16 5 (YP (YI.getD c 0)) ==
        comp 16 (unpack 16 5 (YP (YI.getD a 0))) (unpack 16 5 (YP (YI.getD b 0)))) = true := by
  have cA := (yK_parts (yi_lt ha)).1
  have cB := (yK_parts (yi_lt hb)).1
  have cC := (yK_parts (yi_lt hc)).1
  have ht := triAll a ha
  unfold tri at ht
  have h := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 ht b hb) c hc
  unfold triK at h
  simp only [CFSG.KC.L34Scan.strictB_app] at h
  rw [comp_unpack' cA cB, comp_unpack' cB cA, comp_unpack' cA cC, comp_unpack' cC cA,
    comp_unpack' cB cC, comp_unpack' cC cB, idTab_unpack' sz16,
    CFSG.KC.L34KSnd.beq_unpack cA (canon_pidn sz16), CFSG.KC.L34KSnd.beq_unpack cB (canon_pidn sz16), CFSG.KC.L34KSnd.beq_unpack cB cA,
    CFSG.KC.L34KSnd.beq_unpack (canonK_pcomp cA cB) (canonK_pcomp cB cA),
    CFSG.KC.L34KSnd.beq_unpack (canonK_pcomp cA cC) (canonK_pcomp cC cA),
    CFSG.KC.L34KSnd.beq_unpack (canonK_pcomp cB cC) (canonK_pcomp cC cB),
    CFSG.KC.L34KSnd.beq_unpack cC (canon_pidn sz16), CFSG.KC.L34KSnd.beq_unpack cC cA, CFSG.KC.L34KSnd.beq_unpack cC cB,
    CFSG.KC.L34KSnd.beq_unpack cC (canonK_pcomp cA cB)]
  simpa only [orB_eq, andB_eq, notB_eq, Bool.or_assoc, pc16] using h

theorem v1Act_true : l34V1ActCheck (enumBFS 42 gTabs 241920).tabs = true := by
  unfold l34V1ActCheck
  rw [hR.1, fe_enc.1]
  dsimp only
  rw [fe_enc.2]
  have hsz : (penumRec 42 6 FE.cnt FE.T FE.PL).tabs.size = 16 := EFt_size
  rw [hsz]
  simp only [Bool.true_and, beq_self_eq_true, Bool.and_eq_true]
  have hacts : ∀ x ∈ v1Acts (penumRec 42 6 FE.cnt FE.T FE.PL).tabs (pts 42 6 241920 L34R.T),
      ∃ y < 360, x = unpack 16 5 (YP y) :=
    fun x hx => acts_mem hx
  have hinvs : ∀ x ∈ (v1Acts (penumRec 42 6 FE.cnt FE.T FE.PL).tabs
      (pts 42 6 241920 L34R.T)).filter (fun s => comp 16 s s == idTab 16),
      ∃ a < 46, x = unpack 16 5 (YP (YI.getD a 0)) :=
    fun x hx => inv_mem hx
  generalize v1Acts (penumRec 42 6 FE.cnt FE.T FE.PL).tabs (pts 42 6 241920 L34R.T) = A
    at hacts hinvs ⊢
  generalize A.filter (fun s => comp 16 s s == idTab 16) = B at hinvs ⊢
  refine ⟨?_, ?_⟩
  · rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro a ha
    rw [getElem!_pos A a ha]
    obtain ⟨y, hy, e⟩ := hacts _ (Array.getElem_mem ha)
    rw [e]
    exact p1 hy
  · rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro a ha
    rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro b hb
    rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro c hc
    rw [getElem!_pos B a ha, getElem!_pos B b hb, getElem!_pos B c hc]
    obtain ⟨a', ha', ea⟩ := hinvs _ (Array.getElem_mem ha)
    obtain ⟨b', hb', eb⟩ := hinvs _ (Array.getElem_mem hb)
    obtain ⟨c', hc', ec⟩ := hinvs _ (Array.getElem_mem hc)
    rw [ea, eb, ec]
    exact tri_ok ha' hb' hc'

end CertificateChecks.KernelLC.L34V1

end

module

public import Certificates.Kernel.LocalComp.L34Un.Small
public import Certificates.Kernel.LocalComp.L34Un.P0
public import Certificates.Kernel.LocalComp.L34Un.P1
public import Certificates.Kernel.LocalComp.L34Un.P2
public import Certificates.Kernel.LocalComp.L34Un.P3
public import Certificates.Kernel.LocalComp.L34Un.P4
public import Certificates.Kernel.LocalComp.L34Un.P5
public import Certificates.Kernel.LocalComp.L34Un.Scan
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Certificates.Kernel.L34ScanSound
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelLC.L34Un

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KS.PEnum CFSG.KC.L34KSnd CertificateChecks.KernelLC.L34X CertificateChecks.KernelLC.L34Cert
open CFSG.PSL3Four.Native Certificates.L34Unitary Certificates.L34Borel
open CFSG.KLie.CT (andB orB notB)

abbrev Cn (p : Nat) : Prop := canonK 42 6 (mask 6) (42 * 6) p = true

theorem cR : Cn R0 := pinR.canon 86182 (by decide)

theorem append_get_left {A B : Array Tab} {i : Nat} (h : i < A.size) : (A ++ B)[i]! = A[i]! := by
  rw [getElem!_pos _ i (by simp; omega), Array.getElem_append_left h, getElem!_pos A i h]

theorem append_get_right {A B : Array Tab} {i : Nat} (h1 : A.size ≤ i)
    (h2 : i < A.size + B.size) : (A ++ B)[i]! = B[i - A.size]! := by
  rw [getElem!_pos _ i (by simp; omega), Array.getElem_append_right h1,
    getElem!_pos B (i - A.size) (by omega)]

theorem pairOK_of {j k cnt : Nat} {G GI T PL POS SRT SRI : Nat → Nat} (hk : k = 10)
    (hcnt : cnt = 20160) (hhd : penumHdK (pidn 42 6) cnt 20160 T PL = true)
    (hg : gensK (borelGens j) 42 6 5 G = true)
    (hc : ∀ i < 5, G (i + 5) = pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) R0 (G i)) R0)
    (hpt : ∀ i < cnt, penumPtK 42 6 (mask 6) (42 * 6) false G GI k cnt T PL POS SRT SRI i = true) :
    Certificates.L34Unitary.pairOK (unpack 42 6 R0) j = true := by
  have hB := gensOK_of hg
  have hGO : GensOK 42 6 k G (pairGens (unpack 42 6 R0) j) := by
    refine ⟨?_, fun i hi => ?_⟩
    · unfold pairGens
      rw [Array.size_append, Array.size_map, hB.1, hk]
    · rw [hk] at hi
      unfold pairGens
      by_cases h5 : i < 5
      · rw [append_get_left (by rw [hB.1]; exact h5)]
        exact hB.2 i h5
      · have hi5 : i - 5 < 5 := by omega
        obtain ⟨hb, cb⟩ := hB.2 (i - 5) hi5
        rw [append_get_right (by rw [hB.1]; omega) (by rw [Array.size_map, hB.1]; omega), hB.1,
          map_get _ (by rw [hB.1]; exact hi5), hb]
        unfold conjTab
        rw [comp_unpack' cR cb, comp_unpack' (canonK_pcomp cR cb) cR]
        have e := hc (i - 5) hi5
        rw [Nat.sub_add_cancel (by omega)] at e
        rw [e]
        exact ⟨rfl, canonK_pcomp (canonK_pcomp cR cb) cR⟩
  obtain ⟨h1, h2⟩ := penumK_left_sound (cap := 20160) (by decide) hGO hhd hpt
  unfold Certificates.L34Unitary.pairOK
  dsimp only
  rw [h1, h2, Bool.true_and, penumRec_eq, Array.size_ofFn, hcnt]
  rfl

theorem pt_of {k cnt : Nat} {G GI T PL POS SRT SRI : Nat → Nat} (hcnt : cnt = 20160)
    (h : ∀ s < 32, penumSlK 42 6 (mask 6) (42 * 6) false G GI k cnt T PL POS SRT SRI
      (Nat.mul s 630) 630 = true) :
    ∀ i < cnt, penumPtK 42 6 (mask 6) (42 * 6) false G GI k cnt T PL POS SRT SRI i = true := by
  intro i hi
  have hs : i / 630 < 32 := by omega
  exact penumSl_spec (h (i / 630) hs) i (by change i / 630 * 630 ≤ i; omega)
    (by change i < i / 630 * 630 + 630; omega) hi

theorem parts {k cnt : Nat} {G T PL : Nat → Nat} {j : Nat}
    (h : bAnd(Nat.beq k 10, bAnd(Nat.beq cnt 20160, bAnd(penumHdK (pidn 42 6) cnt 20160 T PL,
      bAnd(gensK (borelGens j) 42 6 5 G, allN 5 (fun i => Nat.beq (G (Nat.add i 5))
        (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) R0 (G i)) R0)))))) = true) :
    k = 10 ∧ cnt = 20160 ∧ penumHdK (pidn 42 6) cnt 20160 T PL = true ∧
      gensK (borelGens j) 42 6 5 G = true ∧
      ∀ i < 5, G (i + 5) = pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) R0 (G i)) R0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := (by simpa only [bAnd_iff] using h :
    Nat.beq k 10 = true ∧ Nat.beq cnt 20160 = true ∧ _ ∧ _ ∧ _)
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, h3, h4,
    fun i hi => Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 h5 i hi)⟩

theorem pair_all : ∀ j < 6, Certificates.L34Unitary.pairOK (unpack 42 6 R0) j = true := by
  intro j hj
  interval_cases j
  · obtain ⟨a, b, c, d, e⟩ := parts (k := UP0.k) (cnt := UP0.cnt) (G := UP0.G) (T := UP0.T)
      (PL := UP0.PL) (j := 0) k_p0
    exact pairOK_of a b c d e (pt_of b ck0All)
  · obtain ⟨a, b, c, d, e⟩ := parts (k := UP1.k) (cnt := UP1.cnt) (G := UP1.G) (T := UP1.T)
      (PL := UP1.PL) (j := 1) k_p1
    exact pairOK_of a b c d e (pt_of b ck1All)
  · obtain ⟨a, b, c, d, e⟩ := parts (k := UP2.k) (cnt := UP2.cnt) (G := UP2.G) (T := UP2.T)
      (PL := UP2.PL) (j := 2) k_p2
    exact pairOK_of a b c d e (pt_of b ck2All)
  · obtain ⟨a, b, c, d, e⟩ := parts (k := UP3.k) (cnt := UP3.cnt) (G := UP3.G) (T := UP3.T)
      (PL := UP3.PL) (j := 3) k_p3
    exact pairOK_of a b c d e (pt_of b ck3All)
  · obtain ⟨a, b, c, d, e⟩ := parts (k := UP4.k) (cnt := UP4.cnt) (G := UP4.G) (T := UP4.T)
      (PL := UP4.PL) (j := 4) k_p4
    exact pairOK_of a b c d e (pt_of b ck4All)
  · obtain ⟨a, b, c, d, e⟩ := parts (k := UP5.k) (cnt := UP5.cnt) (G := UP5.G) (T := UP5.T)
      (PL := UP5.PL) (j := 5) k_p5
    exact pairOK_of a b c d e (pt_of b ck5All)

theorem e0_parts : GensOK 42 6 UE0.k UE0.G e0Gens ∧ UE0.cnt = 9 ∧
    penumHdK (pidn 42 6) UE0.cnt 9 UE0.T UE0.PL = true ∧
    penumSlK 42 6 (mask 6) (42 * 6) false UE0.G UE0.GI UE0.k UE0.cnt UE0.T UE0.PL UE0.POS
      UE0.SRT UE0.SRI 0 9 = true := by
  obtain ⟨h1, h2, h3, h4⟩ := (by simpa only [bAnd_iff] using k_e0 :
    gensK e0Gens 42 6 UE0.k UE0.G = true ∧ Nat.beq UE0.cnt 9 = true ∧ _ ∧ _)
  exact ⟨gensOK_of h1, Nat.eq_of_beq_eq_true h2, h3, h4⟩

theorem e0_enc : e0Enum = penumRec 42 6 UE0.cnt UE0.T UE0.PL ∧
    enumOK 42 e0Gens (penumRec 42 6 UE0.cnt UE0.T UE0.PL) = true :=
  penumK_left_sound (cap := 9) (by decide) e0_parts.1 e0_parts.2.2.1 fun i hi =>
    penumSl_spec e0_parts.2.2.2 i (Nat.zero_le _) (by rw [e0_parts.2.1] at hi; omega) hi

theorem e0_get {i : Nat} (hi : i < 2) : e0Gens[i]! = unpack 42 6 (UE0.G i) ∧ Cn (UE0.G i) :=
  e0_parts.1.2 i (by rw [← e0_parts.1.1]; simpa [e0Gens] using hi)

theorem u0_eq : u0T = unpack 42 6 (UE0.G 0) ∧ Cn (UE0.G 0) := e0_get (i := 0) (by decide)

theorem t3b_eq : t3bT = unpack 42 6 (UE0.G 1) ∧ Cn (UE0.G 1) := e0_get (i := 1) (by decide)

theorem scan_all : ∀ i < 241920, unK (pidn 42 6) R0 (L34R.T i) = true :=
  scanSl_spec (L := 1344) (K := 180) (by decide) (by decide) fun s hs => by
    have h1 := unAll s hs
    unfold un at h1
    rwa [strictB_app, strictB_app] at h1

theorem unitary_true : l34UnitaryCheck (enumBFS 42 gensS 20160).tabs
    (enumBFS 42 gTabs 241920).tabs = true := by
  unfold l34UnitaryCheck
  rw [hS.1, hR.1, e0_enc.1, e0_enc.2]
  have hf : found (indexOf (pts 42 6 20160 L34S.T)) (pts 42 6 20160 L34S.T) t3bT = true := by
    rw [t3b_eq.1]
    exact found_pts (q := 19566) (by decide) (Nat.eq_of_beq_eq_true k_b)
  have hsz : (penumRec 42 6 UE0.cnt UE0.T UE0.PL).tabs.size = 9 := by
    rw [penumRec_eq, Array.size_ofFn, e0_parts.2.1]
  rw [hf, hsz]
  simp only [Bool.true_and, beq_self_eq_true]
  rw [CFSG.KS.BfsReplay.allBelow_iff, size_pts]
  intro i hi
  have hx := pinR.canon i hi
  rw [pts_get' hi]
  have h := scan_all i hi
  unfold unK at h
  simp only [orB_eq, notB_eq] at h
  have e1 : (unpack 42 6 (L34R.T i) == idTab 42) = Nat.beq (L34R.T i) (pidn 42 6) := by
    rw [idTab_unpack' hsz42, CFSG.KC.L34KSnd.beq_unpack hx (canon_pidn hsz42)]
  have e2 : (comp 42 (unpack 42 6 (L34R.T i)) (unpack 42 6 (L34R.T i)) == idTab 42) =
      invPt 42 6 (L34R.T i) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, invPt_iff hx]
  have e3 : ∀ g, Cn g → (comp 42 (unpack 42 6 (L34R.T i)) (unpack 42 6 g) ==
      comp 42 (unpack 42 6 g) (unpack 42 6 (L34R.T i))) = commPt 42 6 (L34R.T i) g :=
    fun g hg => by rw [Bool.eq_iff_iff, beq_iff_eq, commPt_iff hx hg]
  rw [u0_eq.1, t3b_eq.1, e1, e2, e3 _ u0_eq.2, e3 _ t3b_eq.2]
  by_cases hr : L34R.T i = R0
  · rw [hr, CFSG.KS.BfsReplay.allBelow_iff.2 pair_all, Bool.or_true]
  · have hb : Nat.beq (L34R.T i) R0 = false := by
      cases hb : Nat.beq (L34R.T i) R0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hr
    rw [hb] at h
    have h' : (Nat.beq (L34R.T i) (pidn 42 6) || !invPt 42 6 (L34R.T i) ||
        !commPt 42 6 (L34R.T i) (UE0.G 0) || !commPt 42 6 (L34R.T i) (UE0.G 1)) = true := by
      simpa only [Bool.or_assoc, Bool.or_false] using h
    rw [Bool.or_eq_true]
    exact Or.inl h'

end CertificateChecks.KernelLC.L34Un

end

module

public import Certificates.Kernel.Tc.HeKDefs
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.PK.Perm.CompC
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Each
meta import Certificates.Kernel.Tc.HeSrc

namespace CertificateChecks.KernelTc.He

open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

meta def cut3M (w : List Int) (a b : Nat) : List (List Int) :=
  [w.take a, (w.drop a).take b, w.drop (a + b)]

meta def arrsP : Array (Array Nat) :=
  (cut3M (heThreeWordsA.getD 1 []) 24 24 ++ cut3M (heThreeWordsA.getD 2 []) 20 19 ++
    cut3M ((heTcWs.getD 10 []).take 71) 24 24 ++ cut3M (heTcWs.getD 6 []) 23 23 ++
    cut3M (heTcWs.getD 7 []) 23 23).toArray.map heThreeArr

meta def arrsX : Array (Array Nat) :=
  #[heThreeArr (heThreeWordsA.getD 1 []), heThreeArr (heThreeWordsA.getD 2 []),
    heThreeArr ((heTcWs.getD 10 []).take 71)]

end CertificateChecks.KernelTc.He

public section

#kmisc_packarrs CertificateChecks.KernelTc.He.HWP CertificateChecks.KernelTc.He.arrsP 14

#kmisc_packarrs CertificateChecks.KernelTc.He.HWX CertificateChecks.KernelTc.He.arrsX 14

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc.He

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu CFSG.KC.HeLoc
  CertificateChecks.KernelLC.HeFix

@[expose] def wX : List (List Int) :=
  [CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.heThreeWordsA.getD 1 [],
    CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.heThreeWordsA.getD 2 [], (heTcWs.getD 10 []).take 71,
    heTcWs.getD 6 [], heTcWs.getD 7 []]

@[expose] def cut3 (w : List Int) (a b : Nat) : List (List Int) :=
  [w.take a, (w.drop a).take b, w.drop (a + b)]

@[expose] def pcs : List (List Int) :=
  cut3 (wX.getD 0 []) 24 24 ++ cut3 (wX.getD 1 []) 20 19 ++ cut3 (wX.getD 2 []) 24 24 ++
    cut3 (wX.getD 3 []) 23 23 ++ cut3 (wX.getD 4 []) 23 23

@[expose] noncomputable def wordC (wd : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 8330 14)
    (fun z _ ih => strictN ih (fun T => strictN (icode z) (fun c =>
      pcompC 8330 14 (mask 14) (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
        L2 (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
        L2I (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T))) wd

theorem wordC_eq : ∀ wd : List Int, wordC wd = wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I wd
  | [] => rfl
  | z :: wd => by
    change strictN (wordC wd) (fun T => strictN (icode z) (fun c =>
        pcompC 8330 14 (mask 14) (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
          L2 (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
          L2I (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T)) =
      strictN (wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I wd) (fun T => strictN (icode z)
        (fun c => pcomp 8330 14 (mask 14) (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
          L2 (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
          L2I (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T))
    rw [wordC_eq wd]
    simp only [CFSG.KS.PK.pcompC_eq]

@[expose] noncomputable def pOK (k : Nat) : Bool := Nat.beq (wordC (pcs.getD k [])) (HWP k)

#kc_each CertificateChecks.KernelTc.He.pOK 0 15

theorem pcomp_assocW {n w p q r : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (_hq : canonK n w (mask w) (n * w) q = true) (hr : canonK n w (mask w) (n * w) r = true) :
    pcomp n w (mask w) (pcomp n w (mask w) p q) r =
      pcomp n w (mask w) p (pcomp n w (mask w) q r) := by
  obtain ⟨hn, hw, -, -⟩ := PF.canon_facts hp
  obtain ⟨-, -, -, hrr⟩ := PF.canon_facts hr
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) (PF.pcomp_shr _ _ hn32 hw0) fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pcomp hn32 (hrr i hi), PF.pg_pcomp hn32 hi,
    PF.pg_pcomp hn32 hi]

theorem wordK_append {n w : Nat} {S SI : Nat → Nat}
    (hS : ∀ j, canonK n w (mask w) (n * w) (S j) = true)
    (hSI : ∀ j, canonK n w (mask w) (n * w) (SI j) = true)
    (hI : canonK n w (mask w) (n * w) (pidn n w) = true) {v : List Int}
    (hv : canonK n w (mask w) (n * w) (wordK n w (mask w) (pidn n w) S SI v) = true) :
    ∀ u : List Int, canonK n w (mask w) (n * w) (wordK n w (mask w) (pidn n w) S SI u) = true ∧
      wordK n w (mask w) (pidn n w) S SI (u ++ v) =
        pcomp n w (mask w) (wordK n w (mask w) (pidn n w) S SI u)
          (wordK n w (mask w) (pidn n w) S SI v)
  | [] => by
    obtain ⟨hn, hw, hp0, hpr⟩ := PF.canon_facts hv
    have hn32 : n < 2 ^ 32 := by omega
    have hw0 := PF.w_pos hw
    refine ⟨hI, (PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) hp0 fun i hi => ?_).symm⟩
    change pg w (mask w) (pcomp n w (mask w) (pidn n w) (wordK n w (mask w) (pidn n w) S SI v)) i = _
    rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw (hpr i hi)]
  | z :: u => by
    obtain ⟨hu, e⟩ := wordK_append hS hSI hI hv u
    have eL : ∀ x : List Int, wordK n w (mask w) (pidn n w) S SI (z :: x) =
        pcomp n w (mask w) (Bool.rec (motive := fun _ => Nat)
          (SI (Nat.sub (Nat.shiftRight (icode z) (nat_lit 1)) (nat_lit 1)))
          (S (Nat.sub (Nat.shiftRight (icode z) (nat_lit 1)) (nat_lit 1)))
          (Nat.beq (Nat.land (icode z) (nat_lit 1)) (nat_lit 0)))
          (wordK n w (mask w) (pidn n w) S SI x) := fun x => by
      change strictN (wordK n w (mask w) (pidn n w) S SI x) (fun T => strictN (icode z) (fun c =>
        pcomp n w (mask w) (Bool.rec (motive := fun _ => Nat)
          (SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))
          (S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))
          (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0))) T)) = _
      rw [PF.strictN_eqP, PF.strictN_eqP]
    have hL : canonK n w (mask w) (n * w) (Bool.rec (motive := fun _ => Nat)
        (SI (Nat.sub (Nat.shiftRight (icode z) (nat_lit 1)) (nat_lit 1)))
        (S (Nat.sub (Nat.shiftRight (icode z) (nat_lit 1)) (nat_lit 1)))
        (Nat.beq (Nat.land (icode z) (nat_lit 1)) (nat_lit 0))) = true := by
      cases Nat.beq (Nat.land (icode z) (nat_lit 1)) (nat_lit 0)
      · exact hSI _
      · exact hS _
    refine ⟨?_, ?_⟩
    · rw [eL]
      exact CFSG.KC.BfsPin.canonK_pcomp hL hu
    · rw [List.cons_append, eL, eL, e, pcomp_assocW hL hu hv]

theorem cLet : bAnd(canonK 8330 14 (mask 14) (8330 * 14) (L2 0),
    bAnd(canonK 8330 14 (mask 14) (8330 * 14) (L2 1),
    bAnd(canonK 8330 14 (mask 14) (8330 * 14) (L2I 0),
    bAnd(canonK 8330 14 (mask 14) (8330 * 14) (L2I 1),
    bAnd(canonK 8330 14 (mask 14) (8330 * 14) (nat_lit 0),
      canonK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14)))))) = true := by
  quickRfl

theorem cTab : bAnd(canonK 8330 14 (mask 14) (8330 * 14) (HT 6),
    bAnd(canonK 8330 14 (mask 14) (8330 * 14) (HT 7),
    bAnd(canonK 8330 14 (mask 14) (8330 * 14) (HT 8),
    bAnd(canonK 8330 14 (mask 14) (8330 * 14) (HWX 0),
    bAnd(canonK 8330 14 (mask 14) (8330 * 14) (HWX 1),
      canonK 8330 14 (mask 14) (8330 * 14) (HWX 2)))))) = true := by
  quickRfl

theorem cP : allN 15 (fun k => canonK 8330 14 (mask 14) (8330 * 14) (HWP k)) = true := by
  quickRfl

theorem kV : bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HWP 0) (pcompC 8330 14 (mask 14) (HWP 1) (HWP 2)))
      (HWX 0),
    bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HWP 3) (pcompC 8330 14 (mask 14) (HWP 4) (HWP 5)))
      (HWX 1),
    bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HWP 6) (pcompC 8330 14 (mask 14) (HWP 7) (HWP 8)))
      (HWX 2),
    bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HWP 9) (pcompC 8330 14 (mask 14) (HWP 10) (HWP 11)))
      (HT 6),
      Nat.beq (pcompC 8330 14 (mask 14) (HWP 12) (pcompC 8330 14 (mask 14) (HWP 13) (HWP 14)))
        (HT 7))))) = true := by
  quickRfl

theorem kP : bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HWX 0) (HT 7)) (HT 8),
    bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HT 6) (HT 6)) (HT 9),
    bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HWX 2) (HT 7)) (HT 10),
    bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HT 7) (HT 7)) (HT 11),
    bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HWX 2) (pcompC 8330 14 (mask 14) (HWX 2)
      (pcompC 8330 14 (mask 14) (HT 6) (pcompC 8330 14 (mask 14) (HWX 0) (HWX 1))))) (HT 12),
      Nat.beq (pcompC 8330 14 (mask 14) (HT 8) (pcompC 8330 14 (mask 14) (HWX 0) (HWX 0)))
        (HT 13)))))) = true := by
  quickRfl

theorem kI : allN 6 (fun j => bAnd(szOK 8330 14, bAnd(lettersK 2 (heTcWs.getD (Nat.add 8 j) []),
    invEqK 8330 14 (mask 14) (8330 * 14) (HT (Nat.add 8 j)) (HTI (Nat.add 8 j))))) = true := by
  quickRfl

theorem canonL : (∀ j, canonK 8330 14 (mask 14) (8330 * 14) (L2 j) = true) ∧
    (∀ j, canonK 8330 14 (mask 14) (8330 * 14) (L2I j) = true) ∧
    canonK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14) = true := by
  have hc := cLet
  simp only [bAnd_iff] at hc
  obtain ⟨a0, a1, b0, b1, z, hI⟩ := hc
  refine ⟨fun j => ?_, fun j => ?_, hI⟩
  · match j with
    | 0 => exact a0
    | 1 => exact a1
    | _ + 2 => exact z
  · match j with
    | 0 => exact b0
    | 1 => exact b1
    | _ + 2 => exact z

theorem appK {u v : List Int} {a b : Nat}
    (hu : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I u = a)
    (hv : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I v = b)
    (hb : canonK 8330 14 (mask 14) (8330 * 14) b = true) :
    wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (u ++ v) = pcomp 8330 14 (mask 14) a b ∧
      canonK 8330 14 (mask 14) (8330 * 14) (pcomp 8330 14 (mask 14) a b) = true := by
  have hb' : canonK 8330 14 (mask 14) (8330 * 14) (wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I v)
      = true := by
    rw [hv]
    exact hb
  obtain ⟨hcu, e⟩ := wordK_append canonL.1 canonL.2.1 canonL.2.2 hb' u
  rw [hu] at hcu e
  rw [hv] at e
  exact ⟨e, CFSG.KC.BfsPin.canonK_pcomp hcu hb⟩

theorem wOK_of {k : Nat} (e : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (heTcWs.getD k []) = HT k)
    (h : bAnd(szOK 8330 14, bAnd(lettersK 2 (heTcWs.getD k []),
      invEqK 8330 14 (mask 14) (8330 * 14) (HT k) (HTI k))) = true) : wOK k = true := by
  unfold wOK wordEqK
  rw [e, Nat.beq_refl]
  simp only [bAnd_iff] at h ⊢
  exact ⟨⟨h.1, h.2.1, trivial⟩, h.2.2⟩

theorem wX_eq {i a b c : Nat}
    (e : wX.getD i [] = pcs.getD a [] ++ (pcs.getD b [] ++ pcs.getD c []))
    (h0 : pOK a = true) (h1 : pOK b = true) (h2 : pOK c = true)
    (c2 : canonK 8330 14 (mask 14) (8330 * 14) (HWP c) = true) :
    wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (wX.getD i []) =
      pcomp 8330 14 (mask 14) (HWP a) (pcomp 8330 14 (mask 14) (HWP b) (HWP c)) := by
  unfold pOK at h0 h1 h2
  rw [wordC_eq] at h0 h1 h2
  have h := appK (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2) c2
  rw [e, (appK (Nat.eq_of_beq_eq_true h0) h.1 h.2).1]

theorem eV : pcomp 8330 14 (mask 14) (HWP 0) (pcomp 8330 14 (mask 14) (HWP 1) (HWP 2)) = HWX 0 ∧
    pcomp 8330 14 (mask 14) (HWP 3) (pcomp 8330 14 (mask 14) (HWP 4) (HWP 5)) = HWX 1 ∧
    pcomp 8330 14 (mask 14) (HWP 6) (pcomp 8330 14 (mask 14) (HWP 7) (HWP 8)) = HWX 2 ∧
    pcomp 8330 14 (mask 14) (HWP 9) (pcomp 8330 14 (mask 14) (HWP 10) (HWP 11)) = HT 6 ∧
    pcomp 8330 14 (mask 14) (HWP 12) (pcomp 8330 14 (mask 14) (HWP 13) (HWP 14)) = HT 7 := by
  have hc := kV
  simp only [bAnd_iff, CFSG.KS.PK.pcompC_eq] at hc
  obtain ⟨h0, h1, h2, h3, h4⟩ := hc
  exact ⟨Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2,
    Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

theorem eX0 : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (wX.getD 0 []) = HWX 0 :=
  (wX_eq (i := 0) (a := 0) (b := 1) (c := 2) rfl pOK0 pOK1 pOK2
    (allN_spec cP 2 (by decide))).trans eV.1

theorem eX1 : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (wX.getD 1 []) = HWX 1 :=
  (wX_eq (i := 1) (a := 3) (b := 4) (c := 5) rfl pOK3 pOK4 pOK5
    (allN_spec cP 5 (by decide))).trans eV.2.1

theorem eX2 : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (wX.getD 2 []) = HWX 2 :=
  (wX_eq (i := 2) (a := 6) (b := 7) (c := 8) rfl pOK6 pOK7 pOK8
    (allN_spec cP 8 (by decide))).trans eV.2.2.1

theorem eR1 : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (heTcWs.getD 6 []) = HT 6 :=
  (wX_eq (i := 3) (a := 9) (b := 10) (c := 11) rfl pOK9 pOK10 pOK11
    (allN_spec cP 11 (by decide))).trans eV.2.2.2.1

theorem eR2 : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (heTcWs.getD 7 []) = HT 7 :=
  (wX_eq (i := 4) (a := 12) (b := 13) (c := 14) rfl pOK12 pOK13 pOK14
    (allN_spec cP 14 (by decide))).trans eV.2.2.2.2

theorem cT : canonK 8330 14 (mask 14) (8330 * 14) (HT 6) = true ∧
    canonK 8330 14 (mask 14) (8330 * 14) (HT 7) = true ∧
    canonK 8330 14 (mask 14) (8330 * 14) (HT 8) = true ∧
    canonK 8330 14 (mask 14) (8330 * 14) (HWX 0) = true ∧
    canonK 8330 14 (mask 14) (8330 * 14) (HWX 1) = true ∧
    canonK 8330 14 (mask 14) (8330 * 14) (HWX 2) = true := by
  have hc := cTab
  simp only [bAnd_iff] at hc
  exact hc

theorem eP : pcomp 8330 14 (mask 14) (HWX 0) (HT 7) = HT 8 ∧
    pcomp 8330 14 (mask 14) (HT 6) (HT 6) = HT 9 ∧
    pcomp 8330 14 (mask 14) (HWX 2) (HT 7) = HT 10 ∧
    pcomp 8330 14 (mask 14) (HT 7) (HT 7) = HT 11 ∧
    pcomp 8330 14 (mask 14) (HWX 2) (pcomp 8330 14 (mask 14) (HWX 2)
      (pcomp 8330 14 (mask 14) (HT 6) (pcomp 8330 14 (mask 14) (HWX 0) (HWX 1)))) = HT 12 ∧
    pcomp 8330 14 (mask 14) (HT 8) (pcomp 8330 14 (mask 14) (HWX 0) (HWX 0)) = HT 13 := by
  have hc := kP
  simp only [bAnd_iff, CFSG.KS.PK.pcompC_eq] at hc
  obtain ⟨h8, h9, h10, h11, h12, h13⟩ := hc
  exact ⟨Nat.eq_of_beq_eq_true h8, Nat.eq_of_beq_eq_true h9, Nat.eq_of_beq_eq_true h10,
    Nat.eq_of_beq_eq_true h11, Nat.eq_of_beq_eq_true h12, Nat.eq_of_beq_eq_true h13⟩

theorem eW8 : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (heTcWs.getD 8 []) = HT 8 := by
  have e : heTcWs.getD 8 [] = wX.getD 0 [] ++ heTcWs.getD 7 [] := rfl
  rw [e, (appK eX0 eR2 cT.2.1).1, eP.1]

theorem wOK8 : wOK 8 = true := wOK_of eW8 (allN_spec kI 0 (by decide))

theorem eW9 : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (heTcWs.getD 9 []) = HT 9 := by
  have e : heTcWs.getD 9 [] = heTcWs.getD 6 [] ++ heTcWs.getD 6 [] := rfl
  rw [e, (appK eR1 eR1 cT.1).1, eP.2.1]

theorem wOK9 : wOK 9 = true := wOK_of eW9 (allN_spec kI 1 (by decide))

theorem eW10 : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (heTcWs.getD 10 []) = HT 10 := by
  have e : heTcWs.getD 10 [] = wX.getD 2 [] ++ heTcWs.getD 7 [] := rfl
  rw [e, (appK eX2 eR2 cT.2.1).1, eP.2.2.1]

theorem wOK10 : wOK 10 = true := wOK_of eW10 (allN_spec kI 2 (by decide))

theorem wOK11 : wOK 11 = true := by
  have e : heTcWs.getD 11 [] = heTcWs.getD 7 [] ++ heTcWs.getD 7 [] := rfl
  refine wOK_of ?_ (allN_spec kI 3 (by decide))
  rw [e, (appK eR2 eR2 cT.2.1).1, eP.2.2.2.1]

theorem wOK12 : wOK 12 = true := by
  have e : heTcWs.getD 12 [] = wX.getD 2 [] ++ (wX.getD 2 [] ++ (heTcWs.getD 6 [] ++
      (wX.getD 0 [] ++ wX.getD 1 []))) := rfl
  refine wOK_of ?_ (allN_spec kI 4 (by decide))
  have h1 := appK eX0 eX1 cT.2.2.2.2.1
  have h2 := appK eR1 h1.1 h1.2
  have h3 := appK eX2 h2.1 h2.2
  rw [e, (appK eX2 h3.1 h3.2).1, eP.2.2.2.2.1]

theorem wOK13 : wOK 13 = true := by
  have e : heTcWs.getD 13 [] = heTcWs.getD 8 [] ++ (wX.getD 0 [] ++ wX.getD 0 []) := rfl
  refine wOK_of ?_ (allN_spec kI 5 (by decide))
  have h1 := appK eX0 eX0 cT.2.2.2.1
  rw [e, (appK eW8 h1.1 h1.2).1, eP.2.2.2.2.2]

theorem wOK14 : wOK 14 = true := by
  quickRfl

end CertificateChecks.KernelTc.He

end

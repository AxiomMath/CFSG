module

public import Certificates.Kernel.LocalComp.Tits8Data
public import Certificates.Kernel.SporSch.Tits.Inv2266
public import Certificates.Kernel.Sporadic.Tits.LocJ
public import CFSG.Certificates.Kernel.LocalCompTits8Sound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Tits8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.ComponentClassification.RankTwoExceptional.TitsSec8
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelMisc
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsInv
open CertificateChecks.KernelLC
open CFSG.KLie.CT (andB orB notB)

@[expose] def wd (i : Nat) : List Int := (titsSec8ZWords ++ titsSec8TWords).getD i []

@[expose] noncomputable def cm (a b : Nat) : Nat :=
  pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) a b)
    (pinvS 1755 11 (mask 11) a)) (pinvS 1755 11 (mask 11) b)

@[expose] noncomputable def okP (x : Nat) : Bool :=
  andB (canonK 1755 11 (mask 11) (1755 * 11) x)
    (andB (canonK 1755 11 (mask 11) (1755 * 11) (pinvS 1755 11 (mask 11) x))
      (permOK 1755 11 (mask 11) (1755 * 11) x (pinvS 1755 11 (mask 11) x)))

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

@[expose] noncomputable def sH (x : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsH.LR TitsH.TRI TitsH.BP 5 0 x
@[expose] noncomputable def sJ (x : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsJ.LR TitsJ.TRI TitsJ.BP 4 0 x
@[expose] noncomputable def sN (x : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0 x
@[expose] noncomputable def sK (x : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsK.LR TitsK.TRI TitsK.BP 5 0 x

@[expose] noncomputable def pc (k : Nat) : Nat :=
  prodCode 1755 11 (mask 11) (1755 * 11) TitsN.LR TitsN.TR k

@[expose] noncomputable def CCL : List Nat := (List.range 8).map Tits8CC

theorem kId : (canonK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) && idK 1755 11 (mask 11)) = true := by
  quickRfl

theorem kW : allN 8 (fun i => andB (wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13
    (wd i) (Tits8W i)) (okP (Tits8W i))) = true := by quickRfl

theorem kU : allN 4 (fun j => andB (Nat.beq (Tits8U j) (cm (Tits8W (2 * j)) (Tits8W (2 * j + 1))))
    (okP (Tits8U j))) = true := by quickRfl

theorem kZT : (Nat.beq (cm (Tits8U 0) (Tits8U 1)) TitsZ && Nat.beq (cm (Tits8U 2) (Tits8U 3)) TitsT) =
    true := by quickRfl

theorem kSH : allN 4 (fun i => sH (Tits8W i)) = true := by quickRfl

theorem kSJ : (sJ (Tits8U 0) && sJ (Tits8U 1)) = true := by quickRfl

theorem kSN : allN 4 (fun i => andB (sN (Tits8W (4 + i)))
    (Nat.beq (pcomp 1755 11 (mask 11) (Tits8W (4 + i)) TitsT)
      (pcomp 1755 11 (mask 11) TitsT (Tits8W (4 + i))))) = true := by quickRfl

theorem kSK : (sK (Tits8U 2) && sK (Tits8U 3)) = true := by quickRfl

theorem kCC : (Nat.beq (maskOf CCL) TitsMN.MC && ascK (tot5 TitsN.LR) CCL 0) = true := by quickRfl

@[expose] noncomputable def cenK (i : Nat) : Bool :=
  strictB (pc (Tits8CC i)) fun x => andB (canonK 1755 11 (mask 11) (1755 * 11) x)
    (orB (Nat.beq x (pidn 1755 11)) (orB (Nat.beq x TitsT)
      (orB (notB (Nat.beq (pcomp 1755 11 (mask 11) x x) (pidn 1755 11)))
        (strictB (Tits8Wit i) fun k => andB (Nat.blt k (tot5 TitsN.LR)) (andB (hasBit TitsMN.M k)
          (strictB (pc k) fun y => andB (canonK 1755 11 (mask 11) (1755 * 11) y)
            (notB (Nat.beq (pcomp 1755 11 (mask 11) x y) (pcomp 1755 11 (mask 11) y x)))))))))

theorem kCen : allN 8 cenK = true := by quickRfl

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem okP_spec {x : Nat} (h : okP x = true) :
    C x ∧ C (pinvS 1755 11 (mask 11) x) ∧
      permOK 1755 11 (mask 11) (1755 * 11) x (pinvS 1755 11 (mask 11) x) = true := by
  simpa only [okP, andB_eq, Bool.and_eq_true] using h

theorem mcomm_eq {a b : Nat} (ha : okP a = true) (hb : okP b = true) :
    mcommA (unpack 1755 11 a) (unpack 1755 11 b) = unpack 1755 11 (cm a b) := by
  obtain ⟨ca, cia, pa⟩ := okP_spec ha
  obtain ⟨cb, cib, pb⟩ := okP_spec hb
  unfold mcommA
  rw [invCand_unpack pa, invCand_unpack pb, compA_unpack ca cb,
    compA_unpack (canonK_pcomp ca cb) cia, compA_unpack (canonK_pcomp (canonK_pcomp ca cb) cia) cib]
  rfl

theorem cm_canon {a b : Nat} (ha : okP a = true) (hb : okP b = true) : C (cm a b) :=
  canonK_pcomp (canonK_pcomp (canonK_pcomp (okP_spec ha).1 (okP_spec hb).1) (okP_spec ha).2.1)
    (okP_spec hb).2.1

theorem w_facts {i : Nat} (hi : i < 8) :
    wA (wd i) = unpack 1755 11 (Tits8W i) ∧ lettersOK 13 (wd i) = true ∧ okP (Tits8W i) = true := by
  have h := allN_spec kW i hi
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨e, l⟩ := wordEqK_sound ⟨bindsD.2.2.2.1, bindsD.2.2.2.2.1⟩ permD h.1
  exact ⟨(wa_def _).trans e, l, h.2⟩

theorem u_facts {j : Nat} (hj : j < 4) :
    Tits8U j = cm (Tits8W (2 * j)) (Tits8W (2 * j + 1)) ∧ okP (Tits8U j) = true := by
  have h := allN_spec kU j hj
  simp only [andB_eq, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, h.2⟩

theorem invOK_of {x : Nat} (h : okP x = true) : invOK (unpack 1755 11 x) = true :=
  isInv_of (okP_spec h).2.2

theorem comm_eq {j : Nat} (hj : j < 2) {L : List (List Int)}
    (h0 : wordAt L 0 = wd (4 * j)) (h1 : wordAt L 1 = wd (4 * j + 1))
    (h2 : wordAt L 2 = wd (4 * j + 2)) (h3 : wordAt L 3 = wd (4 * j + 3)) :
    firstComm L = unpack 1755 11 (Tits8U (2 * j)) ∧ secondComm L = unpack 1755 11 (Tits8U (2 * j + 1)) := by
  have w0 := w_facts (i := 4 * j) (by omega)
  have w1 := w_facts (i := 4 * j + 1) (by omega)
  have w2 := w_facts (i := 4 * j + 2) (by omega)
  have w3 := w_facts (i := 4 * j + 3) (by omega)
  have u0 := u_facts (j := 2 * j) (by omega)
  have u1 := u_facts (j := 2 * j + 1) (by omega)
  have e0 : 2 * (2 * j) = 4 * j := by omega
  have e2 : 2 * (2 * j + 1) = 4 * j + 2 := by omega
  have e3 : 4 * j + 2 + 1 = 4 * j + 3 := by omega
  rw [e0] at u0
  rw [e2, e3] at u1
  unfold firstComm secondComm
  rw [h0, h1, h2, h3, w0.1, w1.1, w2.1, w3.1, mcomm_eq w0.2.2 w1.2.2, mcomm_eq w2.2.2 w3.2.2,
    ← u0.1, ← u1.1]
  exact ⟨rfl, rfl⟩

theorem eqA_cm {a b P : Nat} (ha : okP a = true) (hb : okP b = true) (hP : C P)
    (h : Nat.beq (cm a b) P = true) :
    eqA 1755 (mcommA (unpack 1755 11 a) (unpack 1755 11 b)) (unpack 1755 11 P) = true := by
  rw [mcomm_eq ha hb, eqA_unpack (cm_canon ha hb) hP]
  exact h

theorem zCheck : titsSec8ZCheck = true := by
  have hc := comm_eq (j := 0) (L := titsSec8ZWords) (by omega) rfl rfl rfl rfl
  simp only [Nat.reduceMul, Nat.reduceAdd] at hc
  have u0 := (u_facts (j := 0) (by omega)).2
  have u1 := (u_facts (j := 1) (by omega)).2
  have kz := kZT
  have kj := kSJ
  simp only [Bool.and_eq_true] at kz kj
  have hw : ∀ i < 4, (lettersOK 13 (wd i) && invOK (wA (wd i)) && inH (wA (wd i))) = true := by
    intro i hi
    obtain ⟨e, l, ok⟩ := w_facts (i := i) (by omega)
    rw [l, e, invOK_of ok, Bool.true_and, Bool.true_and]
    exact siftK_sound bindsH permH TitsH.hl rfl (range_of_canonK (okP_spec ok).1)
      (allN_spec kSH i hi)
  have j0 : inJ (unpack 1755 11 (Tits8U 0)) = true :=
    siftK_sound bindsJ permJ TitsJ.hl rfl (range_of_canonK (okP_spec u0).1) kj.1
  have j1 : inJ (unpack 1755 11 (Tits8U 1)) = true :=
    siftK_sound bindsJ permJ TitsJ.hl rfl (range_of_canonK (okP_spec u1).1) kj.2
  have hall : (titsSec8ZWords.all fun w => lettersOK 13 w && invOK (wA w) && inH (wA w)) = true := by
    rw [List.all_eq_true]
    intro w hw'
    have hL : titsSec8ZWords = [wd 0, wd 1, wd 2, wd 3] := rfl
    rw [hL] at hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl
    exacts [hw 0 (by omega), hw 1 (by omega), hw 2 (by omega), hw 3 (by omega)]
  unfold titsSec8ZCheck
  rw [hall, hc.1, hc.2, invOK_of u0, invOK_of u1, j0, j1, z_eq, eqA_cm u0 u1 canonZ kz.1]
  simp only [Bool.and_true]
  rfl

theorem tCheck : titsSec8TCheck = true := by
  have hc := comm_eq (j := 1) (L := titsSec8TWords) (by omega) rfl rfl rfl rfl
  simp only [Nat.reduceMul, Nat.reduceAdd] at hc
  have u2 := (u_facts (j := 2) (by omega)).2
  have u3 := (u_facts (j := 3) (by omega)).2
  have kz := kZT
  have kk := kSK
  simp only [Bool.and_eq_true] at kz kk
  have hw : ∀ i < 4, (lettersOK 13 (wd (4 + i)) && invOK (wA (wd (4 + i))) &&
      inN (wA (wd (4 + i))) && commA (wA (wd (4 + i))) titsTArr) = true := by
    intro i hi
    obtain ⟨e, l, ok⟩ := w_facts (i := 4 + i) (by omega)
    have h := allN_spec kSN i hi
    simp only [andB_eq, Bool.and_eq_true] at h
    have cw := (okP_spec ok).1
    have hn : inN (unpack 1755 11 (Tits8W (4 + i))) = true :=
      siftK_sound bindsN permN TitsN.hl rfl (range_of_canonK cw) h.1
    rw [l, e, invOK_of ok, Bool.true_and, Bool.true_and, hn, Bool.true_and, t_eq]
    unfold commA
    rw [compA_unpack cw cT, compA_unpack cT cw, eqA_unpack (canonK_pcomp cw cT) (canonK_pcomp cT cw)]
    exact h.2
  have k2 : inK (unpack 1755 11 (Tits8U 2)) = true :=
    siftK_sound bindsK permK TitsK.hl rfl (range_of_canonK (okP_spec u2).1) kk.1
  have k3 : inK (unpack 1755 11 (Tits8U 3)) = true :=
    siftK_sound bindsK permK TitsK.hl rfl (range_of_canonK (okP_spec u3).1) kk.2
  have hall : (titsSec8TWords.all fun w => lettersOK 13 w && invOK (wA w) && inN (wA w) &&
      commA (wA w) titsTArr) = true := by
    rw [List.all_eq_true]
    intro w hw'
    have hL : titsSec8TWords = [wd 4, wd 5, wd 6, wd 7] := rfl
    rw [hL] at hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl
    exacts [hw 0 (by omega), hw 1 (by omega), hw 2 (by omega), hw 3 (by omega)]
  unfold titsSec8TCheck
  rw [hall, hc.1, hc.2, invOK_of u2, invOK_of u3, k2, k3, t_eq, eqA_cm u2 u3 cT kz.2]
  simp only [Bool.and_true]
  rfl

theorem ccq_eq : titsCCQ = CCL.map fun k => unpack 1755 11 (pc k) := by
  have k := kCC
  rw [Bool.and_eq_true] at k
  rw [ccq_def]
  exact surv5K_soundCT bindsN permN TitsN.hl agrC k.1 k.2 TitsNcE.all

theorem cnt_mem {k : Nat} (hk : k < tot5 TitsN.LR) (hM : hasBit TitsMN.M k = true) :
    unpack 1755 11 (pc k) ∈ titsCNt :=
  surv5K_memT bindsN permN TitsN.hl agrTN TitsNtE.all hk hM

theorem centreCheck : titsSec8CentreCheck = true := by
  have ki := kId
  rw [Bool.and_eq_true] at ki
  have hid : idA 1755 = unpack 1755 11 (pidn 1755 11) := (idK_sound ki.2).symm
  unfold titsSec8CentreCheck
  rw [ccq_eq, List.all_eq_true]
  intro c hc
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
  rw [CCL] at hk
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
  rw [List.mem_range] at hi
  have h := allN_spec kCen i hi
  unfold cenK at h
  rw [strictB_app] at h
  simp only [andB_eq, orB_eq, notB_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    at h
  simp only [Bool.or_eq_true, Bool.not_eq_true']
  obtain ⟨cx, h⟩ := h
  rw [hid, t_eq, eqA_unpack cx ki.1, eqA_unpack cx cT, compA_unpack cx cx,
    eqA_unpack (canonK_pcomp cx cx) ki.1]
  rcases h with h | h | h | h
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h
  · left
    left
    left
    rw [strictB_app] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hk, hM, h⟩ := h
    rw [strictB_app] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨cy, hne⟩ := h
    have hmem := cnt_mem (Eq.mp Nat.blt_eq hk) hM
    rw [Bool.eq_false_iff]
    intro e
    have hc := List.all_eq_true.1 e _ hmem
    unfold commA at hc
    rw [compA_unpack cx cy, compA_unpack cy cx,
      eqA_unpack (canonK_pcomp cx cy) (canonK_pcomp cy cx)] at hc
    rw [hc] at hne
    exact absurd hne (by decide)

theorem titsSec8Check_true : titsSec8Check = true := by
  simp only [titsSec8Check, zCheck, tCheck, centreCheck, Bool.and_self]

end CertificateChecks.KernelLC.Tits8

end

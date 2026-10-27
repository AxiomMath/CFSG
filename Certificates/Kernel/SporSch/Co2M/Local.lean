module

public import Certificates.Kernel.SporSch.Co2M.Seeds

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2M CFSG.KS.MatRep CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native

@[expose] noncomputable def wP (T : List (ℕ × ℕ)) (w : List ℤ) : ℕ × ℕ := wordP mmK I22 T w

@[expose] noncomputable def cmpP (p q : ℕ × ℕ) : ℕ × ℕ := (mmK q.1 p.1, mmK p.2 q.2)

@[expose] noncomputable def invP (p : ℕ × ℕ) : ℕ × ℕ := (p.2, p.1)

@[expose] noncomputable def powP (p : ℕ × ℕ) (e : ℕ) : ℕ × ℕ :=
  (mpowW mmK I22 p.1 e, mpowI mmK I22 p.2 e)

@[expose] noncomputable def cInitT : List (ℕ × ℕ) := localRec.cInitialWords.map (wP aT)
@[expose] noncomputable def dT : List (ℕ × ℕ) := localRec.dWords.map (wP aT)
@[expose] noncomputable def dStarT : List (ℕ × ℕ) := extP mmK I22 dT localRec.dStrongDerivations
@[expose] noncomputable def rT : List (ℕ × ℕ) := localRec.rWords.map (wP dStarT)
@[expose] noncomputable def z0P : ℕ × ℕ := wP cInitT localRec.cInitialCenterWord
@[expose] noncomputable def tP : ℕ × ℕ := wP dT localRec.dCenterWord
@[expose] noncomputable def zP : ℕ × ℕ := wP rT localRec.zRWord
@[expose] noncomputable def wwP : ℕ × ℕ := wP aT localRec.alignmentIntermediateWord
@[expose] noncomputable def xP : ℕ × ℕ := cmpP (cmpP wwP z0P) (invP wwP)
@[expose] noncomputable def hP : ℕ × ℕ :=
  cmpP (powP (cmpP xP zP) ((oddN2 - 1) / 2)) (powP (cmpP z0P xP) ((oddN1 - 1) / 2))
@[expose] noncomputable def cT : List (ℕ × ℕ) := cInitT.map fun g => cmpP (cmpP hP g) (invP hP)
@[expose] noncomputable def cStarT : List (ℕ × ℕ) := extP mmK I22 cT localRec.cStrongDerivations
@[expose] noncomputable def qT : List (ℕ × ℕ) := localRec.qWords.map (wP cStarT)
@[expose] noncomputable def sT : List (ℕ × ℕ) :=
  qT ++ localRec.sQuotientWords.map (wP cStarT)

theorem rep_cmp {a b : Array ℕ} {p q : ℕ × ℕ} (ha : MatRep.Rep 22 co2PackedVecs a p.1 p.2)
    (hb : MatRep.Rep 22 co2PackedVecs b q.1 q.2) :
    MatRep.Rep 22 co2PackedVecs (compA 2300 a b) (cmpP p q).1 (cmpP p q).2 := by
  have h := rep_compA good ha hb
  rw [V_size] at h
  unfold cmpP
  rw [mmK_eq, mmK_eq]
  exact h

theorem rep_inv {a : Array ℕ} {p : ℕ × ℕ} (ha : MatRep.Rep 22 co2PackedVecs a p.1 p.2) :
    MatRep.Rep 22 co2PackedVecs (invCand 2300 a) (invP p).1 (invP p).2 := by
  have h := rep_invCand good ha
  rwa [V_size] at h

theorem rep_pow {a : Array ℕ} {p : ℕ × ℕ} (ha : MatRep.Rep 22 co2PackedVecs a p.1 p.2) (e : ℕ) :
    MatRep.Rep 22 co2PackedVecs (CFSG.Monster.B.Mathieu.powArr 2300 a e) (powP p e).1 (powP p e).2 := by
  have h := rep_powArr good mmK_eq I22_eq ha e
  rwa [V_size] at h

theorem lens : localRec.cInitialWords.length = 2 ∧ localRec.dWords.length = 2 ∧
    localRec.dStrongDerivations.length = 5 ∧ localRec.rWords.length = 10 ∧
    localRec.cStrongDerivations.length = 7 := by
  decide +kernel

theorem lets : wordsOK 2 localRec.cInitialWords = true ∧ wordsOK 2 localRec.dWords = true ∧
    extOK 2 localRec.dStrongDerivations = true ∧ wordsOK 7 localRec.rWords = true ∧
    lettersOK 2 localRec.cInitialCenterWord = true ∧ lettersOK 2 localRec.dCenterWord = true ∧
    lettersOK 10 localRec.zRWord = true ∧ lettersOK 2 localRec.alignmentIntermediateWord = true ∧
    extOK 2 localRec.cStrongDerivations = true ∧ wordsOK 9 localRec.qWords = true ∧
    wordsOK 9 localRec.sQuotientWords = true := by
  decide +kernel

theorem cInitRep : RepT 22 co2PackedVecs cInitArrs cInitT :=
  repT_words good V_size mmK_eq I22_eq aRep lets.1

theorem dRep : RepT 22 co2PackedVecs dArrs dT :=
  repT_words good V_size mmK_eq I22_eq aRep lets.2.1

theorem dStarRep : RepT 22 co2PackedVecs dStarArrs dStarT :=
  repT_extend good V_size mmK_eq I22_eq _ dRep (by
    have : dT.length = 2 := by rw [dT, List.length_map, lens.2.1]
    rw [this]
    exact lets.2.2.1)

theorem dStar_len : dStarT.length = 7 := by
  have h := dStarRep.1
  rw [← h]
  unfold dStarArrs extendArrs
  have : ∀ (ds : List (List ℤ)) (A : Array (Array ℕ)),
      (ds.foldl (fun acc w => acc.push (wordArr acc w)) A).size = A.size + ds.length := by
    intro ds
    induction ds with
    | nil => intro A; simp
    | cons w ds ih => intro A; rw [List.foldl_cons, ih]; simp; omega
  rw [this, dRep.1, dT, List.length_map, lens.2.1, lens.2.2.1]

theorem rRep : RepT 22 co2PackedVecs rArrs rT :=
  repT_words good V_size mmK_eq I22_eq dStarRep (by rw [dStar_len]; exact lets.2.2.2.1)

theorem z0Rep : MatRep.Rep 22 co2PackedVecs z0Arr z0P.1 z0P.2 :=
  rep_wordArr good V_size mmK_eq I22_eq cInitRep (by
    rw [cInitT, List.length_map, lens.1]; exact lets.2.2.2.2.1)

theorem tRep : MatRep.Rep 22 co2PackedVecs tArr tP.1 tP.2 :=
  rep_wordArr good V_size mmK_eq I22_eq dRep (by
    rw [dT, List.length_map, lens.2.1]; exact lets.2.2.2.2.2.1)

theorem zRep : MatRep.Rep 22 co2PackedVecs zArr zP.1 zP.2 :=
  rep_wordArr good V_size mmK_eq I22_eq rRep (by
    rw [rT, List.length_map, lens.2.2.2.1]; exact lets.2.2.2.2.2.2.1)

theorem wRep : MatRep.Rep 22 co2PackedVecs wArr wwP.1 wwP.2 :=
  rep_wordArr good V_size mmK_eq I22_eq aRep lets.2.2.2.2.2.2.2.1

theorem xRep : MatRep.Rep 22 co2PackedVecs xArr xP.1 xP.2 :=
  rep_cmp (rep_cmp wRep z0Rep) (rep_inv wRep)

theorem hRep : MatRep.Rep 22 co2PackedVecs hArr hP.1 hP.2 :=
  rep_cmp (rep_pow (rep_cmp xRep zRep) _) (rep_pow (rep_cmp z0Rep xRep) _)

theorem cRep : RepT 22 co2PackedVecs cArrs cT :=
  repT_map cInitRep fun _ _ hg => rep_cmp (rep_cmp hRep hg) (rep_inv hRep)

theorem cStarRep : RepT 22 co2PackedVecs cStarArrs cStarT :=
  repT_extend good V_size mmK_eq I22_eq _ cRep (by
    have : cT.length = 2 := by rw [cT, List.length_map, cInitT, List.length_map, lens.1]
    rw [this]
    exact lets.2.2.2.2.2.2.2.2.1)

theorem cStar_len : cStarT.length = 9 := by
  have h := cStarRep.1
  rw [← h]
  unfold cStarArrs extendArrs
  have : ∀ (ds : List (List ℤ)) (A : Array (Array ℕ)),
      (ds.foldl (fun acc w => acc.push (wordArr acc w)) A).size = A.size + ds.length := by
    intro ds
    induction ds with
    | nil => intro A; simp
    | cons w ds ih => intro A; rw [List.foldl_cons, ih]; simp; omega
  rw [this, cRep.1, cT, List.length_map, cInitT, List.length_map, lens.1, lens.2.2.2.2]

theorem qRep : RepT 22 co2PackedVecs qArrs qT :=
  repT_words good V_size mmK_eq I22_eq cStarRep (by rw [cStar_len]; exact lets.2.2.2.2.2.2.2.2.2.1)

theorem sRep : RepT 22 co2PackedVecs sArrs sT :=
  repT_append qRep (repT_words good V_size mmK_eq I22_eq cStarRep (by
    rw [cStar_len]; exact lets.2.2.2.2.2.2.2.2.2.2))

end CertificateChecks.KernelSporSch.Co2M

end

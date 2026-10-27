
module

public import Certificates.Kernel.Sporadic.Fi22.X2069P
public import Certificates.Kernel.Sporadic.Fi22.X2069T
public import Certificates.Kernel.Sporadic.Fi22.X2069S
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.Certificates.Kernel.Spor.CBfsKSound
public import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
import Init.Data.Range.Lemmas
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi22GOT CFSG.Monster.B.Fischer.fi22GraphOuterHex

namespace CertificateChecks.KernelSpor.Fi22X

meta def goM : Array (Array Nat) := #[CFSG.Monster.B.Fischer.fi22GraphOuterArr]

end CertificateChecks.KernelSpor.Fi22X

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22X.GOT CertificateChecks.KernelSpor.Fi22X.goM 12

namespace CertificateChecks.KernelSpor.Fi22X

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.Misc.PairCount
open CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native

@[expose] noncomputable def GO : Nat := GOT 0

@[expose] noncomputable def c (p q : Nat) : Nat := pcomp 3510 12 (mask 12) p q

@[expose] noncomputable def inv (p : Nat) : Nat := pinvS 3510 12 (mask 12) p

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 3510 12 (mask 12) (3510 * 12) p

@[expose] noncomputable def siftP (G : Nat) : Bool :=
  siftK 3510 12 (mask 12) (3510 * 12) (pidn 3510 12) Fi22PC.LR Fi22PC.TRI Fi22PC.BP 6 0 G

@[expose] noncomputable def siftT (G : Nat) : Bool :=
  siftK 3510 12 (mask 12) (3510 * 12) (pidn 3510 12) Fi22TC.LR Fi22TC.TRI Fi22TC.BP 6 0 G

theorem goOK : bAnd(asciiK (Fi22GOT.chars.take (nat_lit 10531)),
    lineK 3 3510 12 GO (Fi22GOT.chars.drop (nat_lit 0))) = true := by quickRfl
theorem cnE : allN 21 (fun L => cn (EX L)) = true := by quickRfl
theorem cnT : allN 13 (fun k => cn (TS k)) = true := by quickRfl
theorem cnG : cn GO = true := by quickRfl
theorem permE0 : permOK 3510 12 (mask 12) (3510 * 12) (EX 0) (inv (EX 0)) = true := by quickRfl
theorem permE1 : permOK 3510 12 (mask 12) (3510 * 12) (EX 1) (inv (EX 1)) = true := by quickRfl
theorem cnQi : cn (inv (EX 0)) = true := by quickRfl
theorem cnVi : cn (inv (EX 1)) = true := by quickRfl
theorem sP0 : siftP (EX 0) = true := by quickRfl
theorem sP1 : bIf(siftP (EX 1), false, true) = true := by quickRfl
theorem sP2 : siftP (c GO (EX 1)) = true := by quickRfl
theorem c4 : allN 9 (fun k => Nat.beq (c (EX (Nat.add 2 k)) (EX 0)) (c (EX 0) (TS k))) = true := by
  quickRfl
theorem c5 : allN 9 (fun k => Nat.beq (EX (Nat.add 11 k)) (EX (Nat.add 2 k))) = true := by quickRfl
theorem c6 : Nat.beq (EX 20) (EX 1) = true := by quickRfl
theorem t7 : siftT (c (inv (EX 0)) (c (EX 1) (c (EX 1) (EX 0)))) = true := by quickRfl
theorem t8 : allN 9 (fun k => siftT (c (inv (EX 0)) (c (EX 1) (c (EX (Nat.add 2 k))
    (c (inv (EX 1)) (EX 0)))))) = true := by quickRfl
theorem d9 : allN 10 (fun k => allN 256 (fun i => bAnd(Nat.blt (pg 9 (mask 9) (R256 k) i) 256,
    Nat.beq (pg 12 (mask 12) DP (pg 9 (mask 9) (R256 k) i))
      (pg 12 (mask 12) (EX (Nat.add 11 k)) (pg 12 (mask 12) DP i))))) = true := by quickRfl
theorem dLt : allN 256 (fun i => Nat.blt (pg 12 (mask 12) DP i) 3510) = true := by quickRfl
theorem dDist : allN 256 (fun i => allN i (fun j =>
    Bool.not (Nat.beq (pg 12 (mask 12) DP j) (pg 12 (mask 12) DP i)))) = true := by quickRfl

theorem hi_of {G : Nat} (h : cn G = true) : Nat.shiftRight G (3510 * 12) = 0 := by
  have h' : bAnd(Nat.beq (Nat.shiftRight G (3510 * 12)) (nat_lit 0),
      allN 3510 (fun i => Nat.blt (pg 12 (mask 12) G i) 3510)) = true := h
  exact Nat.eq_of_beq_eq_true ((bAnd_iff (Nat.beq (Nat.shiftRight G (3510 * 12)) (nat_lit 0))
    (allN 3510 (fun i => Nat.blt (pg 12 (mask 12) G i) 3510))).1 h').1

theorem cn_c {p q : Nat} (hp : cn p = true) (hq : cn q = true) : cn (c p q) = true :=
  canonK_pcomp hp hq

theorem comp_eq {p q : Nat} (hp : cn p = true) (hq : cn q = true) :
    compA 3510 (unpack 3510 12 p) (unpack 3510 12 q) = unpack 3510 12 (c p q) :=
  compA_unpack hp hq

theorem eqA_of {p q : Nat} (hp : cn p = true) (hq : cn q = true) (h : Nat.beq p q = true) :
    eqA 3510 (unpack 3510 12 p) (unpack 3510 12 q) = true := by
  rw [eqA_unpack hp hq]
  exact h

theorem go_eq : fi22GraphOuterArr = unpack 3510 12 GO := by
  obtain ⟨ha, hk⟩ := (bAnd_iff (asciiK (Fi22GOT.chars.take (nat_lit 10531)))
    (lineK 3 3510 12 GO (Fi22GOT.chars.drop (nat_lit 0)))).1 goOK
  have hl := lineK_sound (L := 0) (wd := 3) (n := 3510) ha hk
  unfold fi22GraphOuterArr
  rw [Fi22GOT.eq]
  apply Array.ext
  · simp [CFSG.KS.Raw.unpack]
  · intro i h1 h2
    simp only [CFSG.KS.Raw.unpack, Array.getElem_ofFn]
    have := hl i (by simpa using h1)
    simpa using this

theorem e_cn {L : Nat} (hL : L < 21) : cn (EX L) = true := allN_spec cnE L hL

theorem posArr_get {i : Nat} (hi : i < 256) : fi22ExtPosArr[fi22ExtDArr[i]!]! = i := by
  have hD : ∀ i < 256, fi22ExtDArr[i]! < 3510 := fun i hi => by
    rw [dArr_get hi]
    exact Nat.blt_eq ▸ allN_spec dLt i hi
  have hd : ∀ i < 256, ∀ j < i, fi22ExtDArr[j]! ≠ fi22ExtDArr[i]! := fun i hi j hj e => by
    rw [dArr_get hi, dArr_get (by omega)] at e
    have h := allN_spec (allN_spec dDist i hi) j hj
    rw [e, Nat.beq_refl] at h
    exact absurd h (by decide)
  have heq : fi22ExtPosArr = (List.range' 0 256).foldl (fun p i => p.set! fi22ExtDArr[i]! i)
      (Array.replicate 3510 256) := by
    unfold fi22ExtPosArr
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
  rw [heq]
  exact (CFSG.KS.CB.set_loop hD hd).2 i hi

theorem facts : fi22InP (fi22ExtArr 0) = true ∧ fi22InP (fi22ExtArr 1) = false ∧
    fi22InP (compA 3510 fi22GraphOuterArr (fi22ExtArr 1)) = true ∧
    (∀ k < 9, eqA 3510 (compA 3510 (fi22ExtArr (2 + k)) (fi22ExtArr 0))
      (compA 3510 (fi22ExtArr 0) (fi22OuterStrong3510 4)[k]!) = true) ∧
    (∀ k < 9, eqA 3510 (fi22ExtArr (11 + k)) (fi22ExtArr (2 + k)) = true) ∧
    eqA 3510 (fi22ExtArr 20) (fi22ExtArr 1) = true ∧
    fi22InT (compA 3510 fi22ExtQiArr
      (compA 3510 (fi22ExtArr 1) (compA 3510 (fi22ExtArr 1) (fi22ExtArr 0)))) = true ∧
    (∀ k < 9, fi22InT (compA 3510 fi22ExtQiArr (compA 3510 (fi22ExtArr 1)
      (compA 3510 (fi22ExtArr (2 + k)) (compA 3510 fi22ExtViArr (fi22ExtArr 0))))) = true) ∧
    (∀ k < 10, ∀ i < 256, (fi22ExtArr256 k)[i]! < 256 ∧
      fi22ExtDArr[(fi22ExtArr256 k)[i]!]! = (fi22ExtArr (11 + k))[fi22ExtDArr[i]!]!) ∧
    (∀ i < 256, fi22ExtPosArr[fi22ExtDArr[i]!]! = i) ∧
    rawChainOK 256 (fi22ExtSmallStrong.extract 0 10) fi22ExtSmallStrong #[0, 1, 2, 3, 4, 6]
      (fi22WordsArr 10 18 fi22ExtSmallDerivations) 4 = true ∧
    rawOrbitSizes 256 fi22ExtSmallStrong #[0, 1, 2, 3, 4, 6] = [256, 64, 4, 2, 2, 1] := by
  have e0 := ext_eq (L := 0) (by norm_num)
  have e1 := ext_eq (L := 1) (by norm_num)
  have c0 := e_cn (L := 0) (by norm_num)
  have c1 := e_cn (L := 1) (by norm_num)
  have hQi : fi22ExtQiArr = unpack 3510 12 (inv (EX 0)) := by
    rw [fi22ExtQiArr, e0]
    exact invCand_unpack permE0
  have hVi : fi22ExtViArr = unpack 3510 12 (inv (EX 1)) := by
    rw [fi22ExtViArr, e1]
    exact invCand_unpack permE1
  refine ⟨?_, ?_, ?_, fun k hk => ?_, fun k hk => ?_, ?_, ?_, fun k hk => ?_, fun k hk i hi => ?_,
    fun i hi => posArr_get hi, ?_, ?_⟩
  · rw [fi22InP, siftK_eq bindsP permP Fi22PC.hl e0 (hi_of c0) (range_of_canonK c0)]
    exact sP0
  · rw [fi22InP, siftK_eq bindsP permP Fi22PC.hl e1 (hi_of c1) (range_of_canonK c1)]
    have h := sP1
    change Bool.rec (motive := fun _ => Bool) true false (siftP (EX 1)) = true at h
    change siftP (EX 1) = false
    cases e : siftP (EX 1)
    · rfl
    · rw [e] at h
      exact absurd h (by decide)
  · rw [fi22InP, go_eq, e1, comp_eq cnG c1, siftK_eq bindsP permP Fi22PC.hl rfl (hi_of (cn_c cnG c1))
      (range_of_canonK (cn_c cnG c1))]
    exact sP2
  · rw [ext_eq (by omega), e0, outT_eq (by omega), comp_eq (e_cn (by omega)) c0,
      comp_eq c0 (allN_spec cnT k (by omega))]
    exact eqA_of (cn_c (e_cn (by omega)) c0) (cn_c c0 (allN_spec cnT k (by omega))) (allN_spec c4 k hk)
  · rw [ext_eq (by omega), ext_eq (by omega)]
    exact eqA_of (e_cn (by omega)) (e_cn (by omega)) (allN_spec c5 k hk)
  · rw [ext_eq (by norm_num), e1]
    exact eqA_of (e_cn (by norm_num)) c1 c6
  · rw [fi22InT, fi22TLevels, hQi, e1, e0, comp_eq c1 c0, comp_eq c1 (cn_c c1 c0),
      comp_eq cnQi (cn_c c1 (cn_c c1 c0)),
      siftK_eq bindsT permT Fi22TC.hl rfl (hi_of (cn_c cnQi (cn_c c1 (cn_c c1 c0))))
        (range_of_canonK (cn_c cnQi (cn_c c1 (cn_c c1 c0))))]
    exact t7
  · have ck := e_cn (L := 2 + k) (by omega)
    rw [fi22InT, fi22TLevels, hQi, hVi, e1, e0, ext_eq (by omega), comp_eq cnVi c0,
      comp_eq ck (cn_c cnVi c0), comp_eq c1 (cn_c ck (cn_c cnVi c0)),
      comp_eq cnQi (cn_c c1 (cn_c ck (cn_c cnVi c0))),
      siftK_eq bindsT permT Fi22TC.hl rfl (hi_of (cn_c cnQi (cn_c c1 (cn_c ck (cn_c cnVi c0)))))
        (range_of_canonK (cn_c cnQi (cn_c c1 (cn_c ck (cn_c cnVi c0)))))]
    exact allN_spec t8 k hk
  · have h := allN_spec (allN_spec d9 k hk) i hi
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    have hx : pg 9 (mask 9) (R256 k) i < 256 := Nat.blt_eq ▸ h1
    have hD : fi22ExtDArr[i]! < 3510 := by
      rw [dArr_get hi]
      exact Nat.blt_eq ▸ allN_spec dLt i hi
    rw [ext256_eq (by omega), unpack_get hi, dArr_get hx, ext_eq (by omega), unpack_get hD,
      dArr_get hi]
    exact ⟨hx, Nat.eq_of_beq_eq_true h2⟩
  · have hw : fi22WordsArr 10 18 fi22ExtSmallDerivations =
        CFSG.Sporadic.Schreier.Co3.Native.wordsArr 10 18 fi22ExtSmallDerivations := rfl
    rw [hw]
    exact rawChainK_sound (NS := 32) (CH := 8) bindsS Fi22SC.head Fi22SC.hl (by norm_num) Fi22SC.hs
  · rw [rawOrbitSizesK_sound bindsS permS Fi22SC.hl]
    decide

end CertificateChecks.KernelSpor.Fi22X

end

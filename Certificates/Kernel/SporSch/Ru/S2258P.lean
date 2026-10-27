
module

public import Certificates.Kernel.SporSch.Ru.S2258
public import Certificates.Kernel.SporSch.Ru.R2257P
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuSy

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLines
  CertificateChecks.KernelSporSch.RuP

theorem canon3 {j : Nat} (hj : j < 7) : canonK 1920 11 (mask 11) (1920 * 11) (SFp j) = true ∧
    canonK 1920 11 (mask 11) (1920 * 11) (SFI j) = true ∧
    canonK 1920 11 (mask 11) (1920 * 11) (RFp j) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec canS j hj)
  exact ⟨h1, (bAnd_iff _ _).1 h2⟩

theorem sfp_eq {j : Nat} (hj : j < 7) : ruSF j = unpack 1920 11 (SFp j) := sf_eq hj

theorem rf_eq {i : Nat} (hi : i < 7) : ruRF i = unpack 1920 11 (RFp i) := by
  have h1 : (ruLines1920.getD 4 (0, 0)).1 = 34 := rfl
  have h2 : (ruLines1920.getD 4 (0, 0)).2 = 7 := rfl
  rw [ruRF, RuR.field_get (f := 4) (by omega)]
  exact row1920 (by omega)

theorem sfi_eq {j : Nat} (hj : j < 7) : invCand 1920 (ruSF j) = unpack 1920 11 (SFI j) := by
  rw [sfp_eq hj]
  exact (invEqK_sound (perm1920 (7 + j) (by omega))).1

theorem sift_of {g : Array Nat} {G : Nat} (hg : g = unpack 1920 11 G) (h : siftR G = true) :
    ruSift 1920 (ruField1920 4) ruRBase g = true := by
  unfold siftR at h
  rw [strictB_eq'] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  exact siftK_soundR RuR.bindsR RuR.permR RuRS.hl hg (Nat.eq_of_beq_eq_true h1) h3 h4

theorem conj_g {i j : Nat} (hi : i < 5) (hj : j < 4) :
    compA 1920 (compA 1920 (ruSF j) (ruRF i)) (invCand 1920 (ruSF j)) =
      unpack 1920 11 (pcomp 1920 11 (mask 11) (pcomp 1920 11 (mask 11) (SFp j) (RFp i)) (SFI j)) := by
  obtain ⟨cs, ci, _⟩ := canon3 (j := j) (by omega)
  obtain ⟨_, _, cr⟩ := canon3 (j := i) (by omega)
  rw [sfi_eq (by omega), sfp_eq (by omega), rf_eq (by omega), compA_unpack cs cr,
    compA_unpack (canonK_pcomp cs cr) ci]

theorem comm_g {i j : Nat} (hi : i < 4) (hj : j < 4) :
    ruCommA 1920 (ruSF i) (ruSF j) = unpack 1920 11 (pcomp 1920 11 (mask 11)
      (pcomp 1920 11 (mask 11) (pcomp 1920 11 (mask 11) (SFp i) (SFp j)) (SFI i)) (SFI j)) := by
  obtain ⟨c1, c1i, _⟩ := canon3 (j := i) (by omega)
  obtain ⟨c2, c2i, _⟩ := canon3 (j := j) (by omega)
  rw [ruCommA, sfi_eq (by omega), sfi_eq (by omega), sfp_eq (by omega), sfp_eq (by omega),
    compA_unpack c1 c2, compA_unpack (canonK_pcomp c1 c2) c1i,
    compA_unpack (canonK_pcomp (canonK_pcomp c1 c2) c1i) c2i]

theorem k_split {k : Nat} : Nat.div k 4 = k / 4 ∧ Nat.mod k 4 = k % 4 := ⟨rfl, rfl⟩

theorem conj_sift {i j : Nat} (hi : i < 5) (hj : j < 4) : ruSift 1920 (ruField1920 4) ruRBase
    (compA 1920 (compA 1920 (ruSF j) (ruRF i)) (invCand 1920 (ruSF j))) = true := by
  have h := CJ.all (4 * i + j) (by change 4 * i + j < 20; omega)
  unfold conjOK at h
  rw [strictB_eq', strictB_eq'] at h
  have e1 : Nat.div (4 * i + j) 4 = i := by change (4 * i + j) / 4 = i; omega
  have e2 : Nat.mod (4 * i + j) 4 = j := by change (4 * i + j) % 4 = j; omega
  rw [e1, e2] at h
  exact sift_of (conj_g hi hj) h

theorem comm_sift {i j : Nat} (hi : i < 4) (hj : j < 4) :
    ruSift 1920 (ruField1920 4) ruRBase (ruCommA 1920 (ruSF i) (ruSF j)) = true := by
  have h := CM.all (4 * i + j) (by change 4 * i + j < 16; omega)
  unfold commOK at h
  rw [strictB_eq', strictB_eq'] at h
  have e1 : Nat.div (4 * i + j) 4 = i := by change (4 * i + j) / 4 = i; omega
  have e2 : Nat.mod (4 * i + j) 4 = j := by change (4 * i + j) % 4 = j; omega
  rw [e1, e2] at h
  exact sift_of (comm_g hi hj) h

theorem sq_sift {i : Nat} (hi : i < 4) :
    ruSift 1920 (ruField1920 4) ruRBase (compA 1920 (ruSF i) (ruSF i)) = true := by
  obtain ⟨c, _, _⟩ := canon3 (j := i) (by omega)
  have h := SQ.all i (by change i < 4; exact hi)
  refine sift_of ?_ h
  rw [sfp_eq (by omega), compA_unpack c c]

theorem pS_eq {G : Nat} (hG : canonK 1920 11 (mask 11) (1920 * 11) G = true) :
    pS G = (fun g => !(ruCommutesS g) || eqA 1920 g (idA 1920) || eqA 1920 g ruZF)
      (unpack 1920 11 G) := by
  have hc : allN 4 (fun j => Nat.beq (pcomp 1920 11 (mask 11) G (SFp j))
      (pcomp 1920 11 (mask 11) (SFp j) G)) = ruCommutesS (unpack 1920 11 G) := by
    have hj : ∀ j < 4, Nat.beq (pcomp 1920 11 (mask 11) G (SFp j))
        (pcomp 1920 11 (mask 11) (SFp j) G) = eqA 1920 (compA 1920 (unpack 1920 11 G) (ruSF j))
          (compA 1920 (ruSF j) (unpack 1920 11 G)) := by
      intro j hj
      obtain ⟨cs, _, _⟩ := canon3 (j := j) (by omega)
      rw [sfp_eq (by omega), compA_unpack hG cs, compA_unpack cs hG,
        canon_eqA (canonK_pcomp hG cs) (canonK_pcomp cs hG)]
    apply Bool.eq_iff_iff.2
    rw [ruCommutesS, allLt_iff]
    constructor
    · intro h j hj'
      rw [← hj j hj']
      exact allN_spec h j hj'
    · intro h
      exact allN_of_forall fun j hj' => (hj j hj').trans (h j hj')
  have hz : CFSG.KS.Prim.canonK 1920 11 (mask 11) (1920 * 11) RuF.ZF = true := cZF
  rw [pS, hc]
  beta_reduce
  rw [idA_eq, RuF.zf_eq, canon_eqA hG cId, canon_eqA hG hz]
  cases ruCommutesS (unpack 1920 11 G) <;> cases Nat.beq G (pidn 1920 11) <;> rfl

theorem cPtsS_lt : ∀ x ∈ cPtsS, x < 1920 := by
  unfold cPtsS
  decide

theorem cmS_of_comm {T0 T1 : Nat}
    (h : Nat.beq (pcomp 1920 11 (mask 11) (pcomp 1920 11 (mask 11) T0 T1) (SFp 0))
      (pcomp 1920 11 (mask 11) (SFp 0) (pcomp 1920 11 (mask 11) T0 T1)) = true) :
    ∀ l : List Nat, (∀ x ∈ l, x < 1920) → cmS T0 T1 (SFp 0) l = true
  | [], _ => rfl
  | x :: l, hl => by
    have hx := hl x List.mem_cons_self
    have hy : pg 11 (mask 11) (SFp 0) x < 1920 :=
      Nat.blt_eq.mp (allN_spec (range_of_canonK (canon3 (j := 0) (by omega)).1) x hx)
    have e : pg 11 (mask 11) (pcomp 1920 11 (mask 11) (pcomp 1920 11 (mask 11) T0 T1) (SFp 0)) x =
        pg 11 (mask 11) (pcomp 1920 11 (mask 11) (SFp 0) (pcomp 1920 11 (mask 11) T0 T1)) x := by
      rw [Nat.eq_of_beq_eq_true h]
    rw [CFSG.KS.PF.pg_pcomp (by norm_num) hx, CFSG.KS.PF.pg_pcomp (by norm_num) hx,
      CFSG.KS.PF.pg_pcomp (by norm_num) hx, CFSG.KS.PF.pg_pcomp (by norm_num) hy] at e
    have e2 : g2S T0 T1 (pg 11 (mask 11) (SFp 0) x) = pg 11 (mask 11) (SFp 0) (g2S T0 T1 x) := e
    change bAnd(Nat.beq (g2S T0 T1 (pg 11 (mask 11) (SFp 0) x))
      (pg 11 (mask 11) (SFp 0) (g2S T0 T1 x)), cmS T0 T1 (SFp 0) l) = true
    rw [e2, Nat.beq_refl, cmS_of_comm h l fun y hy => hl y (List.mem_cons_of_mem _ hy)]

theorem pS_of_F {T0 T1 : Nat} (h : pSF T0 T1 = true) :
    pS (pcomp 1920 11 (mask 11) T0 T1) = true := by
  unfold pSF at h
  cases hs : cmS T0 T1 (SFp 0) cPtsS
  · unfold pS
    cases hc : allN 4 (fun j => Nat.beq (pcomp 1920 11 (mask 11) (pcomp 1920 11 (mask 11) T0 T1)
        (SFp j)) (pcomp 1920 11 (mask 11) (SFp j) (pcomp 1920 11 (mask 11) T0 T1)))
    · rfl
    · rw [cmS_of_comm (allN_spec hc 0 (by omega)) cPtsS cPtsS_lt] at hs
      exact absurd hs (by decide)
  · rw [hs] at h
    exact h

theorem rowS_of_F {a : Nat} (h : rowSF a = true) : rowS a = true := by
  unfold rowSF at h
  unfold rowS row2K
  simp only [CFSG.KS.PackFld.strictB_eqP] at h ⊢
  exact CFSG.KS.PackFld.allN_of_forall fun b hb => pS_of_F (allN_spec h b hb)

theorem facts : (∀ j < 4, isInvA 1920 (ruSF j) (invCand 1920 (ruSF j)) = true) ∧
    (∀ i < 5, ∀ j < 4, ruSift 1920 (ruField1920 4) ruRBase
      (compA 1920 (compA 1920 (ruSF j) (ruRF i)) (invCand 1920 (ruSF j))) = true) ∧
    (∀ i < 4, ∀ j < 4, ruSift 1920 (ruField1920 4) ruRBase
      (ruCommA 1920 (ruSF i) (ruSF j)) = true) ∧
    (∀ i < 4, ruSift 1920 (ruField1920 4) ruRBase (compA 1920 (ruSF i) (ruSF i)) = true) ∧
    ruSift 1920 (ruField1920 4) ruRBase (ruSF 1) = true ∧
    all2 1920 (rawLevels 1920 (ruField1920 1) (ruBaseArr 1920 ruSBase)) (fun g =>
      !(ruCommutesS g) || eqA 1920 g (idA 1920) || eqA 1920 g ruZF) = true := by
  refine ⟨fun j hj => ?_, fun i hi j hj => conj_sift hi hj, fun i hi j hj => comm_sift hi hj,
    fun i hi => sq_sift hi, sift_of (sfp_eq (by omega)) s1OK, ?_⟩
  · rw [sfp_eq (by omega)]
    exact isInv_of rfl (perm1920 (7 + j) (by omega))
  · exact all2_of_rows (p := fun g => !(ruCommutesS g) || eqA 1920 g (idA 1920) || eqA 1920 g ruZF)
      (pK := pS) (LR := RuSS1920.LR) (TR := RuSS1920.TR) RuR.bindsS RuR.permS RuSS1920.hl
      (Nat.le_refl 2)
      (fun G hG => pS_eq hG) fun a ha => rowS_of_F <| RS.all a (by
        have e := Nat.eq_of_beq_eq_true cntS
        change a < 1024
        omega)

end CertificateChecks.KernelSporSch.RuSy

end

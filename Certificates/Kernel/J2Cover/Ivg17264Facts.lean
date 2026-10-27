module

public import Certificates.Kernel.J2Cover.Ivg17264
public import Certificates.Kernel.J2Cover.KFact17260Facts
public import CFSG.Certificates.Kernel.BfsPinAlg

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover.KF17260

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum CFSG.KC.Child3 CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover (inP commA arrTable autStrong)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact

theorem foldl_eval {G : Array (Array Nat)} {S : Nat → Nat}
    (hS : ∀ j < 2, G[j]! = unpack 315 9 (S j) ∧ CnN 315 9 (S j)) :
    ∀ (wd : List Nat) (acc : Nat), CnN 315 9 acc → (∀ j ∈ wd, j < 2) →
      wd.foldl (fun a j => compA 315 a G[j]!) (unpack 315 9 acc) =
          unpack 315 9 (wfoldK 315 9 (mask 9) S wd acc) ∧
        CnN 315 9 (wfoldK 315 9 (mask 9) S wd acc)
  | [], acc, ha, _ => ⟨rfl, ha⟩
  | l :: rest, acc, ha, h => by
    obtain ⟨h1, h2⟩ := hS l (h l List.mem_cons_self)
    rw [List.foldl_cons, h1, compA_unpackN ha h2, wfoldK_cons]
    exact foldl_eval hS rest _ (canon_pcN ha h2) fun l' hl' => h l' (List.mem_cons_of_mem l hl')

theorem ivgY_eq {i : Nat} (hi : i < 3) :
    ivgY i = unpack 315 9 (yK i) ∧ CnN 315 9 (yK i) ∧
      ivgY2 i = unpack 315 9 (y2K i) ∧ CnN 315 9 (y2K i) := by
  have h := allN_spec ch17264ivg i hi
  unfold ivgKc at h
  simp only [bAnd_iff] at h
  obtain ⟨bX, bK, eX, eK, cR, cKI, -⟩ := h
  obtain ⟨-, -, iX, cX, cXI, -⟩ := elt_of (arrBind_sound bX) eX
  obtain ⟨-, -, iK, cK', -, -⟩ := elt_of (arrBind_sound bK) eK
  have c1 := canon_pcN cX cR
  have c2 := canon_pcN cR c1
  have cY : CnN 315 9 (yK i) := canon_pcN cXI c2
  have hY : ivgY i = unpack 315 9 (yK i) := by
    unfold ivgY
    rw [iX, arrBind_sound bX, binds.2.1 i hi, compA_unpackN cX cR, compA_unpackN cR c1,
      compA_unpackN cXI c2]
    rfl
  have c3 := canon_pcN cY cKI
  refine ⟨hY, cY, ?_, canon_pcN cK' c3⟩
  unfold ivgY2
  rw [hY, iK, arrBind_sound bK, compA_unpackN cY cKI, compA_unpackN cK' c3]
  rfl

theorem binds_aut : autStrong[0]! = unpack 315 9 (PA.S 0) ∧ autStrong[1]! = unpack 315 9 (PA.S 1) :=
  ⟨CertificateChecks.KernelJ2Cover.binds.2.2.2.2.1 0 (by omega),
    CertificateChecks.KernelJ2Cover.binds.2.2.2.2.1 1 (by omega)⟩

theorem ivg : ivgCheck = true := by
  have hb := ch17264base
  simp only [bAnd_iff] at hb
  obtain ⟨hn, cid, c0, c1⟩ := hb
  unfold ivgCheck
  rw [List.all_eq_true]
  intro i hi
  have hi3 : i < 3 := List.mem_range.1 hi
  have h := allN_spec ch17264ivg i hi3
  unfold ivgKc at h
  simp only [bAnd_iff] at h
  obtain ⟨bX, bK, eX, eK, -, -, hs, ho, wa, wb, ea, eb⟩ := h
  obtain ⟨x1, x2, -⟩ := elt_of (arrBind_sound bX) eX
  obtain ⟨k1, k2, -⟩ := elt_of (arrBind_sound bK) eK
  obtain ⟨hY, cY, hY2, cY2⟩ := ivgY_eq hi3
  unfold sP at hs
  simp only [bAnd_iff] at hs
  have hm : 0 < ivgOrd[i]! := by interval_cases i <;> decide
  have hS : ∀ j < 2, (#[ivgY i, ivgY2 i])[j]! = unpack 315 9 (letK i j) ∧ CnN 315 9 (letK i j) := by
    intro j hj
    interval_cases j
    · exact ⟨hY, cY⟩
    · exact ⟨hY2, cY2⟩
  have hw : ∀ {wd : List Nat}, wd.all (· < 2) = true → ∀ j ∈ wd, j < 2 := fun hw j hj => by
    have := List.all_eq_true.1 hw j hj
    simpa using this
  have hev : ∀ {wd : List Nat} {P : Nat}, wd.all (· < 2) = true → CnN 315 9 P →
      Nat.beq (wfoldK 315 9 (mask 9) (letK i) wd (pidn 315 9)) P = true →
      eqA 315 (ivgEval #[ivgY i, ivgY2 i] wd) (unpack 315 9 P) = true := by
    intro wd P hwd hP he
    obtain ⟨e1, e2⟩ := foldl_eval hS wd (pidn 315 9) cid (hw hwd)
    unfold ivgEval
    rw [idA_eq hn, e1, eqA_unpackN e2 hP]
    exact he
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨x1, x2⟩, k1⟩, k2⟩, ?_⟩, ?_⟩, wa⟩, wb⟩, ?_⟩, ?_⟩
  · rw [hY]
    exact inP_of rfl hs.1 (range_of_canonK cY) hs.2
  · rw [hY, ordTest_of hm cY]
    exact ho
  · rw [binds_aut.1]
    exact hev wa c0 ea
  · rw [binds_aut.2]
    exact hev wb c1 eb

end CertificateChecks.KernelJ2Cover.KF17260

end

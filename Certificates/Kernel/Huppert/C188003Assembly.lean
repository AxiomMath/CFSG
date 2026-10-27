module

public import Certificates.Kernel.Huppert.C188003
public import CFSG.Certificates.Kernel.F4TNonRoot
import all CFSG.Fischer.F4
import all CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge

public section

set_option maxRecDepth 100000

namespace CFSG.KD.C188003

open CFSG.Fischer CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisN CFSG.KC.F4T
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Elem

theorem c188003_omega : ∀ k : Fin 6, ∀ v : Fin 3 → F4,
    v ∈ Omega k ↔ ∃ d ∈ omega.getD k.val [], vecT d = v := by
  decide +kernel

theorem c188003_pts : ∀ k : Fin 6, ∀ v ∈ omega.getD k.val [], (∀ x ∈ v, x < 4) ∧ vecT v ≠ 0 := by
  decide +kernel

theorem c188003_dist : ∀ k : Fin 6, ∀ i < 6, ∀ j < 6, i ≠ j → ∀ c : F4,
    vecT ((omega.getD k.val []).getD i []) ≠ c • vecT ((omega.getD k.val []).getD j []) := by
  decide +kernel

theorem c188003_frame_det : ∀ k : Fin 6,
    (Matrix.of fun r (i : Fin 3) => vecT ((omega.getD k.val []).getD i []) r).det ≠ 0 := by
  intro k
  rw [Matrix.det_fin_three]
  revert k
  decide +kernel

theorem c188003_frame : ∀ k : Fin 6, ∃ a : Fin 3 → F4, (∀ i, a i ≠ 0) ∧
    ∀ r : Fin 3, ∑ i : Fin 3, vecT ((omega.getD k.val []).getD i []) r * a i =
      vecT ((omega.getD k.val []).getD 3 []) r := by
  simp only [Fin.sum_univ_three]
  decide +kernel

theorem c188003_frame' (k : Fin 6) : ∃ a : Fin 3 → F4, (∀ i, a i ≠ 0) ∧
    Matrix.mulVec (Matrix.of fun r (i : Fin 3) => vecT ((omega.getD k.val []).getD i []) r) a =
      vecT ((omega.getD k.val []).getD 3 []) := by
  obtain ⟨a, ha, he⟩ := c188003_frame k
  exact ⟨a, ha, funext fun r => by rw [← he r]; rfl⟩

theorem c188003_head : ∀ k : Fin 6,
    (t4Reps.getD k.val []).head? = some [1, 0, 0, 0, 1, 0, 0, 0, 1] := by
  decide +kernel

theorem c188003_t4_lens : ∀ k : Fin 6, ((t4Reps.getD k.val []).tail.length ≤ 56 ∧
    (t4Words.getD k.val []).length ≤ 56) := by
  decide +kernel

theorem t4WordsOK_of_two {Om : List (List Nat)} {r : List Nat} {L : List (List Nat)}
    {W : List (List (List Nat))} (hL : L.length ≤ 56) (hW : W.length ≤ 56)
    (h0 : t4WordsOK Om r (chunkT 28 0 L) (chunkT 28 0 W) = true)
    (h1 : t4WordsOK Om r (chunkT 28 1 L) (chunkT 28 1 W) = true) : t4WordsOK Om r L W = true := by
  have h := t4WordsOK_append h0 h1
  simp only [chunkT, Nat.mul_zero, Nat.mul_one, List.drop_zero] at h
  rwa [List.take_of_length_le (l := L.drop 28) (by simp; omega),
    List.take_of_length_le (l := W.drop 28) (by simp; omega), List.take_append_drop,
    List.take_append_drop] at h

theorem c188003_t4w (k : Fin 6) :
    t4WordsOK (omega.getD k.val []) (t4R.getD k.val []) (t4Reps.getD k.val []).tail
      (t4Words.getD k.val []) = true := by
  obtain ⟨hL, hW⟩ := c188003_t4_lens k
  have h0 : t4wAt k.val 0 = true := by
    fin_cases k
    · exact c188003_t4w00
    · exact c188003_t4w10
    · exact c188003_t4w20
    · exact c188003_t4w30
    · exact c188003_t4w40
    · exact c188003_t4w50
  have h1 : t4wAt k.val 1 = true := by
    fin_cases k
    · exact c188003_t4w01
    · exact c188003_t4w11
    · exact c188003_t4w21
    · exact c188003_t4w31
    · exact c188003_t4w41
    · exact c188003_t4w51
  exact t4WordsOK_of_two hL hW h0 h1

theorem c188003_close (k : Fin 6) :
    closeOK (omega.getD k.val []) (t4Reps.getD k.val []) (t4Masks.getD k.val []) = true := by
  fin_cases k
  · exact c188003_close0
  · exact c188003_close1
  · exact c188003_close2
  · exact c188003_close3
  · exact c188003_close4
  · exact c188003_close5

theorem c188003_T4 (i : Fin 6) (Y : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)) :
    P i < Y → Y ≤ SLsub → Y = SLsub :=
  T4_of_data i (c188003_omega i) (c188003_pts i) (c188003_close i) (c188003_head i)
    (c188003_t4w i) Y

theorem c188003_wits : witOK rowCodes invsT wits = true := by
  have hlen := c188003_wit_len
  simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at hlen
  refine witOK_of_chunks rowCodes 30 11 invsT wits (by rw [hlen.1, hlen.2]) (by omega)
    fun k hk => ?_
  interval_cases k
  · exact c188003_wit0
  · exact c188003_wit1
  · exact c188003_wit2
  · exact c188003_wit3
  · exact c188003_wit4
  · exact c188003_wit5
  · exact c188003_wit6
  · exact c188003_wit7
  · exact c188003_wit8
  · exact c188003_wit9
  · exact c188003_wit10

theorem c188003_invs_OK : ∀ A ∈ invsT, ∀ x ∈ [A.a00, A.a01, A.a02, A.a10, A.a11, A.a12, A.a20,
    A.a21, A.a22], x < 4 := by
  decide +kernel

theorem c188003_rows (i : Nat) (hi : i < 72) :
    t3RowOK (rowCodes.getD i []) (rowW1.getD i []) (rowWO.getD i []) (rowWO2.getD i []) = true := by
  have hlen := c188003_rows_len
  simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at hlen
  refine t3Rows_of_chunks ⟨hlen.1.1.1, hlen.1.1.2, hlen.1.2, hlen.2⟩ (fun k hk => ?_) i hi
  interval_cases k
  · exact c188003_rows0
  · exact c188003_rows1
  · exact c188003_rows2

theorem c188003_nonroots {code : List Nat} (hc : code ∈ rowCodes)
    (hr : isRootT (matN code) = false) : ∃ k < 6, ∃ ws,
      nonRootOK (omega.getD k []) ((gks.getD k []).getD 0 []) ((gks.getD k []).getD 1 []) code ws =
        true := by
  have h := c188003_nonroot
  simp only [nonRootsOK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨⟨hl1, hl2⟩, hall⟩ := h
  obtain ⟨p, hp⟩ := fst_mem_zip (l₂ := rowIdx.zip rowG) (by simp [hl1, hl2]) hc
  have := hall _ hp
  simp only [hr, Bool.false_or, Bool.and_eq_true, Nat.blt_eq] at this
  exact ⟨p.1, this.1, p.2, this.2⟩

theorem c188003_chains (k : Nat) (hk : k < 6) :
    chainOK (omega.getD k []) ((gks.getD k []).getD 0 []) ((gks.getD k []).getD 1 [])
      (chainW.getD k []) = true := by
  have h := c188003_chain
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, hall⟩ := h
  have hk1 : k < omega.length := by rw [h1]; exact hk
  have hk2 : k < gks.length := by rw [h2]; exact hk
  have hk3 : k < chainW.length := by rw [h3]; exact hk
  have hp : (omega[k], (gks[k], chainW[k])) ∈ omega.zip (gks.zip chainW) :=
    List.mem_iff_getElem.2 ⟨k, by simp [List.length_zip, hk1, hk2, hk3],
      by simp only [List.getElem_zip]; rfl⟩
  have := hall _ hp
  rwa [List.getD_eq_getElem _ _ hk1, List.getD_eq_getElem _ _ hk2,
    List.getD_eq_getElem _ _ hk3]

theorem c188003_T3 (t x w z : Matrix.GeneralLinearGroup (Fin 3) F4) (μ : F4)
    (hμ : μ = 1 ∨ μ = F4.ω ∨ μ = om2) (ht : Good3 (t : Matrix (Fin 3) (Fin 3) F4))
    (hx : (x : Matrix (Fin 3) (Fin 3) F4) = Xd) (hw : (w : Matrix (Fin 3) (Fin 3) F4) = Wm μ)
    (hz : (z : Matrix (Fin 3) (Fin 3) F4) = Zs) :
    (∀ g ∈ SLsub, g ∈ Subgroup.closure ({x, w, z, t} : Set (Matrix.GeneralLinearGroup (Fin 3) F4))) ∨
      (μ = 1 ∧ ∃ i : Fin 6,
        Subgroup.closure ({x, w, z, t} : Set (Matrix.GeneralLinearGroup (Fin 3) F4)) = P i) := by
  obtain ⟨h1, h2⟩ := good3_inv ht
  obtain ⟨A, hA, hAt⟩ := invsT_complete _ h1 h2
  have hAOK : OK A := OK_of_lt (c188003_invs_OK A hA)
  obtain ⟨code, hc, hcA⟩ := witOK_sound c188003_wits
    (fun B hB => OK_of_lt (c188003_invs_OK B hB)) A hA (by rw [hAt]; exact ht)
  subst hcA
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hc
  have hlen := c188003_rows_len
  simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at hlen
  have hn72 : n < 72 := by rw [← hlen.1.1.1]; exact hn
  have hrow := c188003_rows n hn72
  rw [List.getD_eq_getElem _ _ hn] at hrow
  obtain ⟨hcode, hwo, hwo2, hw1⟩ := t3RowOK_spec hrow
  set H := Subgroup.closure ({x, w, z, t} : Set (Matrix.GeneralLinearGroup (Fin 3) F4)) with hH
  have hxH : x ∈ H := Subgroup.subset_closure (by simp)
  have hwH : w ∈ H := Subgroup.subset_closure (by simp)
  have hzH : z ∈ H := Subgroup.subset_closure (by simp)
  have htH : t ∈ H := Subgroup.subset_closure (by simp)
  have hX : InM H Xd := ⟨x, hxH, hx⟩
  rcases hμ with rfl | rfl | rfl
  · cases hroot : isRootT (matN rowCodes[n])
    · obtain ⟨k, hk, ws, hnr⟩ := c188003_nonroots hc hroot
      refine Or.inr ⟨rfl, ⟨k, hk⟩, ?_⟩
      exact closure_eq_P_of_data ⟨k, hk⟩ (c188003_omega ⟨k, hk⟩) (c188003_pts ⟨k, hk⟩)
        (c188003_dist ⟨k, hk⟩) (isUnit_iff_ne_zero.2 (c188003_frame_det ⟨k, hk⟩))
        (c188003_frame' ⟨k, hk⟩) (c188003_chains k hk) hnr hx hw hz hAt
    · have hw' : (w : Matrix (Fin 3) (Fin 3) F4) = Wm (f4 1) := by rw [hw, f4_one]
      exact Or.inl (SL_of_w6OK (gensT3_in (by decide) hAOK hxH hx hwH hw' hzH hz htH hAt) hX
        (hw1 hroot))
  · have hw' : (w : Matrix (Fin 3) (Fin 3) F4) = Wm (f4 2) := hw
    exact Or.inl (SL_of_w6OK (gensT3_in (by decide) hAOK hxH hx hwH hw' hzH hz htH hAt) hX hwo)
  · have hw' : (w : Matrix (Fin 3) (Fin 3) F4) = Wm (f4 3) := by rw [hw, om2_eq]; rfl
    exact Or.inl (SL_of_w6OK (gensT3_in (by decide) hAOK hxH hx hwH hw' hzH hz htH hAt) hX hwo2)

end CFSG.KD.C188003

end

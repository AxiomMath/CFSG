module

public import Certificates.Kernel.LocalComp.FendelWit
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.FendelDataInputs
meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.FendelDataInputs
meta import CFSG.Sporadic.Schreier.Co3Arrays
import CFSG.GH74.M12.HypCore
import CFSG.GH74.M12.HypCoreInputs
import Certificates.Data.CFSGNative.Co3Schreier.Basic
import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLC.C12T CFSG.Sporadic.Schreier.Co3.co3Perm12Text
#ks_hexlines CertificateChecks.KernelLC.C12T CFSG.Sporadic.Schreier.Co3.co3Perm12Text 1 12 5

#ks_perm CertificateChecks.KernelLC.Fendel.CP 9 CFSG.EvenSmallLie.SympSix.fendelCArr
#ks_perm CertificateChecks.KernelLC.Fendel.KP 9 CFSG.EvenSmallLie.SympSix.fendelKArr
#ks_perm CertificateChecks.KernelLC.Fendel.YP 9 CFSG.EvenSmallLie.SympSix.fendelYArr
#ks_perm CertificateChecks.KernelLC.Fendel.YHP 9 CFSG.EvenSmallLie.SympSix.fendelYHArr
#ks_perm CertificateChecks.KernelLC.Fendel.Y1P 9 CFSG.EvenSmallLie.SympSix.fendelY'Arr
#ks_perm CertificateChecks.KernelLC.Fendel.Y1HP 9 CFSG.EvenSmallLie.SympSix.fendelY'HArr
#ks_perm CertificateChecks.KernelLC.Fendel.Y1ZHP 9 CFSG.EvenSmallLie.SympSix.fendelY'ZHArr
#ks_perm CertificateChecks.KernelLC.Fendel.G1P 9 CFSG.EvenSmallLie.SympSix.fendelK2Arr

namespace CertificateChecks.KernelLC.Fendel

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel CertificateChecks.KernelSpor
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.Schreier.Co3.Native CFSG.EvenSmallLie.SympSix CFSG.GH74.M12.Hyp

@[expose] noncomputable def eltOK (i0 i1 i2 i3 P : Nat) : Bool :=
  bAnd(prod4OK Co3M.LR Co3M.TR i0 i1 i2 i3, Nat.beq (prod4 Co3M.LR Co3M.TR i0 i1 i2 i3) P)

theorem elt_eq {i0 i1 i2 i3 P : Nat} (h : eltOK i0 i1 i2 i3 P = true) :
    fendelMArr i0 i1 i2 i3 = unpack 276 9 P := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  unfold fendelMArr
  rw [prod4_eq trM h1, Nat.eq_of_beq_eq_true h2]

theorem kc : eltOK 238 82 12 2 CP = true := by quickRfl
theorem kk : eltOK 54 54 13 1 KP = true := by quickRfl
theorem ky : eltOK 75 24 16 0 YP = true := by quickRfl
theorem kyh : eltOK 176 6 0 0 YHP = true := by quickRfl
theorem ky1 : eltOK 0 122 8 1 Y1P = true := by quickRfl
theorem ky1h : eltOK 115 2 8 0 Y1HP = true := by quickRfl
theorem ky1zh : eltOK 41 119 18 2 Y1ZHP = true := by quickRfl

@[expose] noncomputable def GB : Nat := prod4 Co3M.LR Co3M.TR 0 40 9 2
@[expose] noncomputable def GHB : Nat := prod4 Co3M.LR Co3M.TR 90 95 25 1
@[expose] noncomputable def GHD : Nat := prod4 Co3M.LR Co3M.TR 11 101 7 1

theorem kg1 : eltOK 0 40 9 2 GB = true := by quickRfl
theorem kg3 : eltOK 235 52 24 0 G1P = true := by quickRfl
theorem kgh1 : eltOK 90 95 25 1 GHB = true := by quickRfl
theorem kgh3 : eltOK 11 101 7 1 GHD = true := by quickRfl

theorem c_eq : fendelCArr = unpack 276 9 CP := elt_eq kc
theorem k_eq : fendelKArr = unpack 276 9 KP := elt_eq kk
theorem y_eq : fendelYArr = unpack 276 9 YP := elt_eq ky
theorem yh_eq : fendelYHArr = unpack 276 9 YHP := elt_eq kyh
theorem y1_eq : fendelY'Arr = unpack 276 9 Y1P := elt_eq ky1
theorem y1h_eq : fendelY'HArr = unpack 276 9 Y1HP := elt_eq ky1h
theorem y1zh_eq : fendelY'ZHArr = unpack 276 9 Y1ZHP := elt_eq ky1zh
theorem k2_eq : fendelK2Arr = unpack 276 9 G1P := elt_eq kg3

@[expose] noncomputable def GP (i : Nat) : Nat :=
  match i with
  | 0 => Y1P | 1 => GB | 2 => YP | _ => G1P

@[expose] noncomputable def GHP (i : Nat) : Nat :=
  match i with
  | 0 => Y1HP | 1 => GHB | 2 => YHP | _ => GHD

theorem gp0 : GP 0 = Y1P := rfl

theorem g_eq (i : Nat) (hi : i < 4) : fendelGArr i = unpack 276 9 (GP i) := by
  interval_cases i
  · exact y1_eq
  · exact elt_eq kg1
  · exact y_eq
  · exact elt_eq kg3

theorem gh_eq (i : Nat) (hi : i < 4) : fendelGHArr i = unpack 276 9 (GHP i) := by
  interval_cases i
  · exact y1h_eq
  · exact elt_eq kgh1
  · exact yh_eq
  · exact elt_eq kgh3

@[expose] noncomputable def memOK (P : Nat) : Bool :=
  bAnd(invEqK 276 9 (mask 9) (276 * 9) P (pinvS 276 9 (mask 9) P),
    bAnd(Co3Text.hiOK P, Co3M.sift P))

theorem mem_sound {P : Nat} (h : memOK P) :
    isInvA 276 (unpack 276 9 P) (invCand 276 (unpack 276 9 P)) = true ∧
      siftA 276 co3MLevels co3MBaseArr 0 (unpack 276 9 P) = true := by
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  obtain ⟨e1, e2⟩ := invEqK_sound h1
  exact ⟨by rw [e1]; exact e2, data.sift _ (Nat.eq_of_beq_eq_true h2) (range_of_permOK h1) h3⟩

theorem ma : memOK AP = true := by quickRfl
theorem mc : memOK CP = true := by quickRfl
theorem mk : memOK KP = true := by quickRfl
theorem my : memOK YP = true := by quickRfl
theorem myh : memOK YHP = true := by quickRfl
theorem my1 : memOK Y1P = true := by quickRfl
theorem my1h : memOK Y1HP = true := by quickRfl
theorem my1zh : memOK Y1ZHP = true := by quickRfl
theorem mg1 : memOK GB = true := by quickRfl
theorem mg3 : memOK G1P = true := by quickRfl
theorem mgh1 : memOK GHB = true := by quickRfl
theorem mgh3 : memOK GHD = true := by quickRfl

theorem elts : ∀ x ∈ fendelMElts, isInvA 276 x (invCand 276 x) = true ∧
    siftA 276 co3MLevels co3MBaseArr 0 x = true := by
  intro x hx
  simp only [fendelMElts, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · rw [a_eq]; exact mem_sound ma
  · rw [c_eq]; exact mem_sound mc
  · rw [k_eq]; exact mem_sound mk
  · rw [y_eq]; exact mem_sound my
  · rw [yh_eq]; exact mem_sound myh
  · rw [y1_eq]; exact mem_sound my1
  · rw [y1h_eq]; exact mem_sound my1h
  · rw [y1zh_eq]; exact mem_sound my1zh
  · rw [g_eq 0 (by omega)]; exact mem_sound my1
  · rw [g_eq 1 (by omega)]; exact mem_sound mg1
  · rw [g_eq 2 (by omega)]; exact mem_sound my
  · rw [g_eq 3 (by omega)]; exact mem_sound mg3
  · rw [gh_eq 0 (by omega)]; exact mem_sound my1h
  · rw [gh_eq 1 (by omega)]; exact mem_sound mgh1
  · rw [gh_eq 2 (by omega)]; exact mem_sound myh
  · rw [gh_eq 3 (by omega)]; exact mem_sound mgh3
  · rw [k2_eq]; exact mem_sound mg3

theorem eq_of_beq {p q : Nat} (h : Nat.beq p q = true) :
    eqA 276 (unpack 276 9 p) (unpack 276 9 q) = true :=
  eqK_sound (n := 276) (w := 9) h

theorem a_sq : sqIdK 276 9 (mask 9) (276 * 9) (pidn 276 9) AP = true := by quickRfl
theorem a_ne : neIdK 276 9 (mask 9) (276 * 9) (pidn 276 9) AP = true := by quickRfl
theorem t_ne : neK 276 9 (mask 9) (276 * 9) Co3Tt Co3Z = true := by quickRfl

theorem c1 : prodOK CP Co3Tt (pc CP Co3Tt) = true := by quickRfl
theorem c2 : prodOK Co3Z Co3Tt (pc Co3Z Co3Tt) = true := by quickRfl
theorem c3 : prodOK (pc Co3Z Co3Tt) CP (pc (pc Co3Z Co3Tt) CP) = true := by quickRfl
theorem c4 : Nat.beq (pc CP Co3Tt) (pc (pc Co3Z Co3Tt) CP) = true := by quickRfl

theorem k1 : commK 276 9 (mask 9) (276 * 9) KP Co3Tt = true := by quickRfl
theorem k2 : prodOK KP KP Co3Z = true := by quickRfl

@[expose] noncomputable def conjOK (H X : Nat) : Bool :=
  bAnd(prodOK H X (pc H X), bAnd(prodOK AP H (pc AP H), Nat.beq (pc H X) (pc AP H)))

theorem conj_sound {H X : Nat} (h : conjOK H X = true) :
    eqA 276 (compA 276 (unpack 276 9 H) (unpack 276 9 X))
      (compA 276 fendelAArr (unpack 276 9 H)) = true := by
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  rw [a_eq, prodOK_eq h1, prodOK_eq h2]
  exact eq_of_beq h3

theorem y1 : commK 276 9 (mask 9) (276 * 9) YP Co3Tt = true := by quickRfl
theorem y2 : conjOK YHP YP = true := by quickRfl
theorem z1 : commK 276 9 (mask 9) (276 * 9) Y1P Co3Tt = true := by quickRfl
theorem z2 : conjOK Y1HP Y1P = true := by quickRfl
theorem z3 : prodOK Co3Z Y1P (pc Co3Z Y1P) = true := by quickRfl
theorem z4 : conjOK Y1ZHP (pc Co3Z Y1P) = true := by quickRfl

theorem gc : allN 4 (fun i => bAnd(commK 276 9 (mask 9) (276 * 9) (GP i) Co3Tt,
    conjOK (GHP i) (GP i))) = true := by quickRfl

theorem q1 : commK 276 9 (mask 9) (276 * 9) G1P Co3Tt = true := by quickRfl
theorem q2 : prodOK Y1P G1P (pc Y1P G1P) = true := by quickRfl
theorem q3 : invEqK 276 9 (mask 9) (276 * 9) Y1P (pinvS 276 9 (mask 9) Y1P) = true := by quickRfl
theorem q4 : invEqK 276 9 (mask 9) (276 * 9) G1P (pinvS 276 9 (mask 9) G1P) = true := by quickRfl
theorem q5 : prodOK (pc Y1P G1P) (pinvS 276 9 (mask 9) Y1P)
    (pc (pc Y1P G1P) (pinvS 276 9 (mask 9) Y1P)) = true := by quickRfl
theorem q6 : prodOK (pc (pc Y1P G1P) (pinvS 276 9 (mask 9) Y1P)) (pinvS 276 9 (mask 9) G1P)
    Co3Z = true := by quickRfl

@[expose] noncomputable def C12 : Nat := C12T.L 13

theorem c12_eq : co3C12Arr = unpack 12 5 C12 := by
  have h := CFSG.KS.Text.hexBind_sound C12T.all 13 (by decide)
  rw [← C12T.eq, Nat.zero_add] at h
  have hsz : (co3Field12 1).size = 1 := by
    unfold co3Field12
    rw [Array.size_ofFn]
    rfl
  unfold co3C12Arr
  rw [getElem!_pos (co3Field12 1) 0 (by omega)]
  have e : (co3Field12 1)[0]'(by omega) = co3Arr12 ((co3Lines12.getD 1 (0, 0)).1 + 0) := by
    unfold co3Field12
    exact Array.getElem_ofFn ..
  rw [e]
  exact h

theorem kc12 : invEqK 12 5 (mask 5) (12 * 5) C12 (pinvS 12 5 (mask 5) C12) = true := by quickRfl

@[expose] noncomputable def ktblK (X : Nat) : List Nat :=
  tmul (tmul (wordT fendelW) (fendelTbl (compA 12 (compA 12 (unpack 12 5 C12)
    (restrictA co3ItArr (unpack 276 9 X))) (unpack 12 5 (pinvS 12 5 (mask 5) C12)))))
    (tinv (wordT fendelW))

theorem ktbl_eq (X : Nat) : fendelKTbl (unpack 276 9 X) = ktblK X := by
  unfold fendelKTbl fendelK1 renameA ktblK
  rw [c12_eq, (invEqK_sound kc12).1]

theorem tz : ktblK Co3Z = JT := by decide +kernel
theorem ty : ktblK YP ∈ QT ∧ ktblK YP ≠ JT := by decide +kernel
theorem tg : fendelGWords.map (fun u => u.foldr (fun i t => tmul (ktblK (GP (i - 1))) t) tid) =
    gensT := by decide +kernel
theorem tw : ∀ u ∈ fendelGWords, ∀ i ∈ u, 1 ≤ i ∧ i ≤ 4 := by decide +kernel
theorem tb : ∀ t ∈ BT, (∀ u ∈ BT, tmul t u = tmul u t) → t = tid ∨ t = JT := by decide +kernel

theorem gword (u : List Nat) (hu : ∀ i ∈ u, 1 ≤ i ∧ i ≤ 4) :
    fendelGWordTbl u = u.foldr (fun i t => tmul (ktblK (GP (i - 1))) t) tid := by
  induction u with
  | nil =>
    unfold fendelGWordTbl
    rw [List.foldr_nil, List.foldr_nil]
  | cons i u ih =>
    have hi := hu i (List.mem_cons_self ..)
    unfold fendelGWordTbl at ih ⊢
    rw [List.foldr_cons, List.foldr_cons, ih fun j hj => hu j (List.mem_cons_of_mem _ hj),
      g_eq (i - 1) (by omega), ktbl_eq]

theorem size_of_map {A : Array Level} {L : List Nat}
    (h : A.toList.map (fun l => l.pts.size) = L) (i : Nat) (hi : i < L.length) :
    (A[i]!).pts.size = L[i]! := by
  subst h
  have hi' : i < A.size := by simpa using hi
  rw [getElem!_pos A i hi']
  simp [hi']

theorem facts : (∀ x : Fin 128 × Fin 4 × Fin 2, fendelWitOK x.1 x.2.1 x.2.2 = true)
    ∧ ((co3TLevels[0]!).pts.size = 128 ∧ (co3TLevels[1]!).pts.size = 4 ∧
       (co3TLevels[2]!).pts.size = 2)
    ∧ (∀ x ∈ fendelMElts, isInvA 276 x (invCand 276 x) = true ∧
       siftA 276 co3MLevels co3MBaseArr 0 x = true)
    ∧ (eqA 276 (compA 276 fendelAArr fendelAArr) (idA 276) = true ∧
       eqA 276 fendelAArr (idA 276) = false ∧ eqA 276 co3TtArr co3ZArr = false)
    ∧ (eqA 276 (compA 276 fendelCArr co3TtArr) (compA 276 (compA 276 co3ZArr co3TtArr) fendelCArr)
       = true)
    ∧ (commutesA 276 fendelKArr co3TtArr = true ∧
       eqA 276 (compA 276 fendelKArr fendelKArr) co3ZArr = true)
    ∧ (fendelKTbl co3ZArr = JT)
    ∧ (commutesA 276 fendelYArr co3TtArr = true ∧
       eqA 276 (compA 276 fendelYHArr fendelYArr) (compA 276 fendelAArr fendelYHArr) = true ∧
       fendelKTbl fendelYArr ∈ QT ∧ fendelKTbl fendelYArr ≠ JT)
    ∧ (commutesA 276 fendelY'Arr co3TtArr = true ∧
       eqA 276 (compA 276 fendelY'HArr fendelY'Arr) (compA 276 fendelAArr fendelY'HArr) = true ∧
       eqA 276 (compA 276 fendelY'ZHArr (compA 276 co3ZArr fendelY'Arr))
         (compA 276 fendelAArr fendelY'ZHArr) = true)
    ∧ (∀ i < 4, commutesA 276 (fendelGArr i) co3TtArr = true ∧
       eqA 276 (compA 276 (fendelGHArr i) (fendelGArr i)) (compA 276 fendelAArr (fendelGHArr i))
         = true)
    ∧ (fendelGWords.map fendelGWordTbl = gensT ∧
       ∀ u ∈ fendelGWords, ∀ i ∈ u, 1 ≤ i ∧ i ≤ 4)
    ∧ (commutesA 276 fendelK2Arr co3TtArr = true ∧
       eqA 276 (compA 276 (compA 276 (compA 276 (fendelGArr 0) fendelK2Arr)
         (invCand 276 (fendelGArr 0))) (invCand 276 fendelK2Arr)) co3ZArr = true)
    ∧ (∀ t ∈ BT, (∀ u ∈ BT, tmul t u = tmul u t) → t = tid ∨ t = JT) := by
  have hT : rawOrbitSizes 276 co3TArrs co3TBaseArr = [128, 4, 2] := by
    rw [rawOrbitSizesK_sound Co3T.binds Co3T.perm Co3T.hl]
    decide
  unfold rawOrbitSizes at hT
  refine ⟨witOK_all, ⟨size_of_map hT 0 (by decide), size_of_map hT 1 (by decide),
    size_of_map hT 2 (by decide)⟩, elts, ⟨?_, ?_, ?_⟩,
    ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, fun i hi => ?_, ⟨?_, tw⟩, ⟨?_, ?_⟩, tb⟩
  · rw [a_eq]
    exact sqIdK_sound a_sq
  · rw [a_eq]
    exact neIdK_sound a_ne
  · rw [Co3Single.tt_eq, Co3Single.z_eq]
    exact neK_sound t_ne
  · rw [c_eq, Co3Single.tt_eq, Co3Single.z_eq, prodOK_eq c1, prodOK_eq c2, prodOK_eq c3]
    exact eq_of_beq c4
  · rw [k_eq, Co3Single.tt_eq]
    exact commK_sound k1
  · rw [k_eq, Co3Single.z_eq, prodOK_eq k2]
    exact eq_of_beq (Nat.beq_refl _)
  · rw [Co3Single.z_eq, ktbl_eq]
    exact tz
  · rw [y_eq, Co3Single.tt_eq]
    exact commK_sound y1
  · rw [y_eq, yh_eq]
    exact conj_sound y2
  · rw [y_eq, ktbl_eq]
    exact ty.1
  · rw [y_eq, ktbl_eq]
    exact ty.2
  · rw [y1_eq, Co3Single.tt_eq]
    exact commK_sound z1
  · rw [y1_eq, y1h_eq]
    exact conj_sound z2
  · rw [y1_eq, y1zh_eq, Co3Single.z_eq, prodOK_eq z3]
    exact conj_sound z4
  · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec gc i hi)
    rw [g_eq i hi, gh_eq i hi, Co3Single.tt_eq]
    exact ⟨commK_sound h1, conj_sound h2⟩
  · rw [List.map_congr_left fun u hu => gword u (tw u hu)]
    exact tg
  · rw [k2_eq, Co3Single.tt_eq]
    exact commK_sound q1
  · rw [g_eq 0 (by omega), gp0, k2_eq, Co3Single.z_eq]
    rw [prodOK_eq q2, (invEqK_sound q3).1, (invEqK_sound q4).1, prodOK_eq q5, prodOK_eq q6]
    exact eq_of_beq (Nat.beq_refl _)

end CertificateChecks.KernelLC.Fendel

end

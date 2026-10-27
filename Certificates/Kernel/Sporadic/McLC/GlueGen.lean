module

public import Certificates.Kernel.Sporadic.McLC.Glue
public import CFSG.Certificates.Kernel.SporSch.SetReplayProof
public import Certificates.Kernel.Sporadic.McLC.OrbZ

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLC

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.SmallOddCore CFSG.ClassicalInvolution
open CFSG.KS.SporSch CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Co3.Native CFSG.KS.Raw

theorem rep_inv_of {T : Table} {g : Equiv.Perm (Fin 275)} (h : Rep 275 T g) :
    Rep 275 (invT 275 T) g⁻¹ := by
  have hT : ∀ x < 275, ap T x = actN g x := fun x hx => by rw [h x hx, idx_eq]
  exact rep_of_actN (CFSG.KS.VO.invT_get (f := actN g) (g := actN g⁻¹) (by norm_num)
    fun x hx => ⟨hT x hx, actN_lt _ hx, by rw [← actN_mul, inv_mul_cancel, actN_one]⟩).2

@[expose] noncomputable def FG (p : List Nat × List (List Nat)) : List Table :=
  wordTbl 275 McLData.kgens p.1 :: p.2.map fun cw =>
    conjT 275 (wordTbl 275 McLData.kgens cw) (invT 275 (wordTbl 275 McLData.kgens cw))
      (wordTbl 275 McLData.kgens p.1)

theorem repGens_eq : McLData.repGens = McLData.repData.map FG := rfl

@[expose] noncomputable def gam (j i : Nat) : Equiv.Perm (Fin 275) :=
  if i = 0 then rho j else
    wp qK ((repD j).2.getD (i - 1) []) * rho j * (wp qK ((repD j).2.getD (i - 1) []))⁻¹

theorem rep_FG {j i : Nat} (hj : j < 21) (hi : i < (repD j).2.length + 1) :
    Rep 275 ((FG (repD j)).getD i (idT 275)) (gam j i) := by
  have hR := rep_word_kgens (repData_letters j hj).1
  rcases i with _ | s
  · unfold gam
    rw [if_pos rfl]
    exact hR
  · have hs : s < (repD j).2.length := by omega
    unfold gam
    rw [if_neg (Nat.succ_ne_zero s), Nat.add_sub_cancel]
    have hw : ∀ l ∈ (repD j).2.getD s [], l = 1 ∨ l = 2 :=
      (repData_letters j hj).2 _ (by rw [List.getD_eq_getElem _ _ hs]; exact List.getElem_mem hs)
    have hC := rep_word_kgens hw
    have e : (FG (repD j)).getD (s + 1) (idT 275) =
        conjT 275 (wordTbl 275 McLData.kgens ((repD j).2.getD s []))
          (invT 275 (wordTbl 275 McLData.kgens ((repD j).2.getD s [])))
          (wordTbl 275 McLData.kgens (repD j).1) := by
      unfold FG
      rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by simpa using hs), List.getElem_map,
        List.getD_eq_getElem _ _ hs]
    rw [e]
    exact Rep.compT (Rep.compT hC hR) (rep_inv_of hC)

theorem gsOK_spec {j : Nat} (hj : j < 21) : McLC.GL j = Nat.succ (repD j).2.length ∧
    (∀ x < 275, pk (GT j 0) x = pk (RP j) x) ∧
    ∀ i < (repD j).2.length, ∀ x < 275,
      pk (GT j (Nat.succ i)) (List.foldr GK x ((repD j).2.getD i [])) =
        List.foldr GK (pk (RP j) x) ((repD j).2.getD i []) := by
  have h := allN_spec gsOK_ok j hj
  unfold gsOK at h
  simp only [strictB_eq, bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, fun x hx => Nat.eq_of_beq_eq_true (allN_spec h2 x hx),
    fun i hi x hx => Nat.eq_of_beq_eq_true (allN_spec (allN_spec h3 i hi) x hx)⟩

theorem GT_spec {j i : Nat} (hj : j < 21) (hi : i < McLC.GL j) {y : Nat} (hy : y < 275) :
    pk (GT j i) y = actN (gam j i) y := by
  obtain ⟨hL, h0, hs⟩ := gsOK_spec hj
  rcases i with _ | s
  · rw [h0 y hy, RP_spec hj hy]
    unfold gam
    rw [if_pos rfl]
  · have hs' : s < (repD j).2.length := by omega
    have hx := actN_lt (wp qK ((repD j).2.getD s []))⁻¹ hy
    have e := hs s hs' _ hx
    have f1 : List.foldr GK (actN (wp qK ((repD j).2.getD s []))⁻¹ y) ((repD j).2.getD s []) =
        actN (wp qK ((repD j).2.getD s [])) (actN (wp qK ((repD j).2.getD s []))⁻¹ y) :=
      foldr_wp (fun c _ z hz => GK_eq c hz) hx
    rw [f1, ← actN_mul, mul_inv_cancel, actN_one, RP_spec hj hx,
      foldr_wp (fun c _ z hz => GK_eq c hz) (actN_lt (rho j) hx)] at e
    rw [e]
    unfold gam
    rw [if_neg (Nat.succ_ne_zero s), Nat.add_sub_cancel, actN_mul, actN_mul]

theorem vOK_spec {j : Nat} (hj : j < 21) {e : Nat} (he : e < 2) :
    (∀ i ∈ vword (2 * j + e), i < McLC.GL j) ∧
      ∀ x < 275, LJ (2 * e) x = List.foldr (fun i y => pk (GT j i) y) x (vword (2 * j + e)) := by
  have h0 := allN_spec vOK_ok j hj
  unfold vOK at h0
  have h := allN_spec h0 e he
  simp only [strictB_eq, bAnd_iff] at h
  refine ⟨fun i hi => ?_, fun x hx => Nat.eq_of_beq_eq_true (allN_spec h.2 x hx)⟩
  have h1 := List.all_eq_true.1 h.1 i hi
  rwa [Nat.blt_eq] at h1

theorem gam_mem {j i : Nat} (hj : j < 21) (hi : i < McLC.GL j) : gam j i ∈ genOf 275 (FG (repD j)) := by
  have hL := (gsOK_spec hj).1
  have hlen : i < (FG (repD j)).length := by
    unfold FG
    rw [List.length_cons, List.length_map]
    omega
  rw [← tp_eq (rep_FG hj (by omega))]
  apply tp_mem_genOf
  rw [List.getD_eq_getElem _ _ hlen]
  exact List.getElem_mem hlen

theorem sg_gen {j e : Nat} (hj : j < 21) (he : e < 2) : sg (2 * e) ∈ genOf 275 (FG (repD j)) := by
  have hv := vOK_spec hj he
  have eq : sg (2 * e) = wp (gam j) (vword (2 * j + e)) := perm_ext fun x hx => by
    rw [actN_sg (by omega) hx, hv.2 x hx]
    exact foldr_wp (fun c hc y hy => GT_spec hj (hv.1 c hc) hy) hx
  rw [eq]
  exact wp_mem fun c hc => gam_mem hj (hv.1 c hc)

theorem repD_eq {j : Nat} (hj : j < McLData.repData.length) : repD j = McLData.repData[j] := by
  unfold repD
  rw [List.getD_eq_getElem]

theorem gen_K : ∀ gs ∈ McLData.repGens, genOf 275 McLData.kgens ≤ genOf 275 gs := by
  intro gs hgs
  rw [repGens_eq] at hgs
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hgs
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
  have hj' : j < 21 := by rwa [repData_len] at hj
  rw [← repD_eq hj, genOf_kgens, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  obtain h | h := hg
  · rw [h]
    exact sg_gen hj' (e := 0) (by norm_num)
  · rw [h]
    exact sg_gen hj' (e := 1) (by norm_num)

theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b := by
  by_cases e : a = b
  · subst e
    rw [Nat.beq_refl]
    exact beq_self_eq_true a
  · have h : Nat.beq a b = false := by
      cases h : Nat.beq a b
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) e
    rw [h]
    exact beq_false_of_ne e

theorem Ta_size : McLData.Ta.size = 275 := by
  unfold McLData.Ta
  rw [McLK.orb_eq.1]
  simp [CFSG.KS.VO3.v3Rec]

theorem Tb_size : McLData.Tb.size = 275 := by
  unfold McLData.Tb
  rw [McLK.orb_eq.1]
  simp [CFSG.KS.VO3.v3Rec]

theorem arr_ext {a b : Array Nat} (ha : a.size = 275) (hb : b.size = 275)
    (e : ∀ x < 275, a[x]! = b[x]!) : a = b :=
  Array.ext (by rw [ha, hb]) fun i h1 h2 => by
    have := e i (by rw [ha] at h1; exact h1)
    rwa [getElem!_pos a i h1, getElem!_pos b i h2] at this

theorem unpack_get {P x : Nat} (hx : x < 275) : (unpack 275 9 P)[x]! = pg 9 (mask 9) P x := by
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem gensK : McLProof.abArr.size = 2 ∧
    ∀ k < 2, McLProof.abArr[k]! = unpack 275 9 (McLCOZ.G k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  have hu : (unpack 275 9 (McLCOZ.G k)).size = 275 := by simp [unpack]
  interval_cases k
  · change Native.natArr McLData.Ta = _
    refine arr_ext (by simp [Native.natArr,Ta_size]) hu fun x hx => ?_
    rw [natArr_getElem!, ap_Ta hx, unpack_get hx]
    exact (Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec gensZ x hx)).1).symm
  · change Native.natArr McLData.Tb = _
    refine arr_ext (by simp [Native.natArr,Tb_size]) hu fun x hx => ?_
    rw [natArr_getElem!, ap_Tb hx, unpack_get hx]
    exact (Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec gensZ x hx)).2).symm

theorem fixZ_eq : McLProof.fixZ = fixL := by
  unfold McLProof.fixZ fixedList fixL
  refine List.filter_congr fun p hp => ?_
  have hp' := List.mem_range.1 hp
  change ((Native.natArr McLData.Ta)[p]! == p) = Nat.beq (r32 McLK.AL p) p
  rw [natArr_getElem!, ap_Ta hp', beq_nat]

theorem replayK : SetReplayOK 275 9 35 2 22275 22275 McLCOZ.nS 16 McLCOZ.nB 64 64 McLCOZ.G
    McLCOZ.GI (rowGet McLCOZ.XT 343) (rowGet McLCOZ.WT 40) (rowGet McLCOZ.ST 20)
    (rowGet McLCOZ.SIT 20) McLCOZ.C McLProof.fixZ := by
  obtain ⟨c0, cN⟩ := by simpa only [bAnd_iff] using cntZ
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, le_refl _, by decide, by decide,
    by norm_num, by norm_num, fun k hk => allN_spec permZ k hk, ?_, McLCOZ.helt, McLCOZ.hsrt,
    Nat.eq_of_beq_eq_true c0, Nat.eq_of_beq_eq_true cN, McLCOZ.hrun⟩
  rw [fixZ_eq]
  exact startZ

theorem orbit_K : translatesOK McLProof.abArr McLProof.fixZ McLProof.orbZ.1 McLProof.orbZ.2.1
      McLProof.orbZ.2.2 = true ∧ keysSortedOK McLProof.orbZ.1 = true ∧
      McLProof.orbZ.1.size = 22275 := by
  unfold McLProof.orbZ
  exact SRP.setReplay_proved gensK replayK

end CertificateChecks.KernelSpor.McLC

end

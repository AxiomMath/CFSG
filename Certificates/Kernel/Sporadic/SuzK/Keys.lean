module

public import Certificates.Kernel.Sporadic.SuzK.Matrix
public import CFSG.F3.ConjBFSWSuz
import Certificates.Kernel.Sporadic.SuzK.E0
import Certificates.Kernel.Sporadic.SuzK.E1
import Certificates.Kernel.Sporadic.SuzK.E2
import Certificates.Kernel.Sporadic.SuzK.E3
import Certificates.Kernel.Sporadic.SuzK.E4
import Certificates.Kernel.Sporadic.SuzK.E5
import Certificates.Kernel.Sporadic.SuzK.E6
import Certificates.Kernel.Sporadic.SuzK.E7
import Certificates.Kernel.Sporadic.SuzK.E8
import Certificates.Kernel.Sporadic.SuzK.E9
import Certificates.Kernel.Sporadic.SuzK.E10
import Certificates.Kernel.Sporadic.SuzK.E11
import Certificates.Kernel.Sporadic.SuzK.E12
import Certificates.Kernel.Sporadic.SuzK.KeyChecks
public import Certificates.Kernel.Sporadic.SuzK.Misc
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Spor.ConjIndexSound
public import Certificates.Kernel.Sporadic.SuzK.Orb

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.SuzK.edgeAll CertificateChecks.KernelSpor.SuzK.edgeSl 1430
#kon_join CertificateChecks.KernelSpor.SuzK.sortAll CertificateChecks.KernelSpor.SuzK.sortSl 65

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.F3.Native CFSG.KS CFSG.KS.F3L CFSG.KS.Mat3 CFSG.KS.PEnum CFSG.KC.Enum CFSG.KC.Ord
  CFSG.Sporadic.Suz.Native CFSG.Sporadic.Th.Native CFSG.KS.Raw.Orb

theorem r32_lt (F : Nat → Nat) (i : Nat) : r32 F i < 4294967296 := by
  unfold r32 CFSG.KS.Row.rg
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem tabList_length (F : Nat → Nat) : ∀ c j, (tabList F j c).length = c
  | 0, _ => rfl
  | c + 1, j => by simp [tabList, tabList_length F c]

theorem tabList_getElem (F : Nat → Nat) : ∀ c j i (h : i < (tabList F j c).length),
    (tabList F j c)[i] = UInt32.ofNat (r32 F (j + i))
  | 0, _, i, h => by simp [tabList] at h
  | c + 1, j, 0, _ => by simp [tabList]
  | c + 1, j, i + 1, h => by
    simp only [tabList, List.getElem_cons_succ]
    rw [tabList_getElem F c (j + 1) i]
    congr 2
    omega

theorem tabOf_size (F : Nat → Nat) : (tabOf F).size = 22880 := by
  unfold tabOf
  rw [List.size_toArray]
  exact tabList_length F 22880 0

theorem ap_tabOf (F : Nat → Nat) {x : Nat} (hx : x < 22880) : ap (tabOf F) x = r32 F x := by
  have hs : x < (tabOf F).size := by rw [tabOf_size]; exact hx
  unfold ap
  rw [getElem!_pos _ x hs]
  have e : (tabOf F)[x]'hs = UInt32.ofNat (r32 F (0 + x)) :=
    tabList_getElem F 22880 0 x (by rw [tabList_length]; exact hx)
  rw [e, Nat.zero_add, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (r32_lt F x)

theorem orbLit_keys : orbLit.keys = keysLit := by
  unfold orbLit
  dsimp only

theorem keysLit_size : keysLit.size = 22880 := by
  unfold keysLit
  exact Array.size_ofFn

theorem keys_size : orbLit.keys.size = 22880 := by
  rw [orbLit_keys, keysLit_size]

theorem keys_get {k : Nat} (hk : k < 22880) : orbLit.keys[k]! = keyW k := by
  rw [orbLit_keys, getElem!_pos _ k (by rw [keysLit_size]; exact hk)]
  unfold keysLit
  rw [Array.getElem_ofFn]

theorem bfs' : CFSG.KC.F3Bfs.bfsOrderOK (r32 AL) (r32 BE) (r32 PA) (r32 LB) 22880 = true := bfs_ok

theorem al_lt {k : Nat} (hk : k < 22880) : r32 AL k < 22880 :=
  Nat.lt_of_lt_of_le (BfsSpec.cnt_step bfs' hk).2.1 (BfsSpec.cnt_le bfs' hk).2

theorem be_lt {k : Nat} (hk : k < 22880) : r32 BE k < 22880 :=
  Nat.lt_of_lt_of_le (BfsSpec.cnt_step bfs' hk).2.2 (BfsSpec.cnt_le bfs' hk).2

theorem dep_pt {k : Nat} (hk : k < 22880) :
    r32 DP k < 1000 ∧ (k ≠ 0 → r32 DP k = r32 DP (r32 PA k) + 1) := by
  have h := dep_ok
  unfold depK at h
  rw [Raw.Orb.bAnd_eq,Bool.and_eq_true] at h
  have h2 := allN_iff.1 h.2 k hk
  rw [strictB_eq, Raw.Orb.bAnd_eq,Bool.and_eq_true, Raw.Orb.bIf_eq] at h2
  refine ⟨by simpa [Nat.blt_eq] using h2.1, fun hk0 => ?_⟩
  have h3 := h2.2
  have hb : k.beq 0 = false := by
    cases e : k.beq 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hk0
  rw [hb, if_neg Bool.false_ne_true] at h3
  exact Nat.eq_of_beq_eq_true h3

@[expose] noncomputable def img (g k : Nat) : Nat := if g = 0 then r32 AL k else r32 BE k

theorem edge_facts {g k : Nat} (hg : g < 2) (hk : k < 22880) :
    VLD (kx k) = true ∧ MUL (x3 g) (kx k) = MUL (kx (img g k)) (x3 g) := by
  have hs : 715 * g + k / 32 < 1430 := by omega
  have h := edgeAll (715 * g + k / 32) hs
  unfold edgeSl at h
  have e1 : Nat.div (715 * g + k / 32) 715 = g := by
    change (715 * g + k / 32) / 715 = g
    omega
  have e2 : Nat.mul (Nat.mod (715 * g + k / 32) 715) 32 = k / 32 * 32 := by
    change (715 * g + k / 32) % 715 * 32 = k / 32 * 32
    congr 1
    omega
  rw [strictB_eq, strictB_eq, e1, e2] at h
  have h' := allN_iff.1 h (k % 32) (Nat.mod_lt _ (by norm_num))
  have e3 : Nat.add (k / 32 * 32) (k % 32) = k := by
    change k / 32 * 32 + k % 32 = k
    omega
  rw [strictB_eq, e3, Raw.Orb.bIf_eq, if_pos (Nat.blt_eq.mpr hk)] at h'
  unfold edge at h'
  rw [strictB_eq, strictB_eq, strictB_eq, Raw.Orb.bAnd_eq,Bool.and_eq_true] at h'
  obtain ⟨h1, h2⟩ := h'
  refine ⟨h1, ?_⟩
  have hi : Bool.rec (motive := fun _ => Nat) (r32 BE k) (r32 AL k) (Nat.beq g 0) = img g k := by
    unfold img
    rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
    · rfl
    · rfl
  rw [hi] at h2
  exact Nat.eq_of_beq_eq_true h2

theorem LO_eq : LO = 2 ^ 4096 - 1 := pow_sub_one_eq 4096

theorem canon_kx {k : Nat} (hk : k < 22880) : Canon3 4096 (kx k) :=
  (valid3_iff LO_eq).1 (edge_facts (g := 0) (by norm_num) hk).1

theorem canon_x3 {g : Nat} (hg : g < 2) : Canon3 4096 (x3 g) := by
  have h := vld_ok
  rw [Raw.Orb.bAnd_eq,Bool.and_eq_true] at h
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · exact (valid3_iff LO_eq).1 h.1
  · exact (valid3_iff LO_eq).1 h.2

noncomputable abbrev KM (k : Nat) : Matrix (Fin 64) (Fin 64) (ZMod 3) := toMat 64 (unlane 64 (laneK k))

theorem mul_mat3 {X Y : Nat} (hX : Canon3 4096 X) (hY : Canon3 4096 Y) :
    mat3 64 4096 (MUL X Y) = mat3 64 4096 X * mat3 64 4096 Y :=
  (mul3s_sound consts_ok hX hY).2

theorem ML_x3 {g : Nat} (hg : g < 2) : mat3 64 4096 (x3 g) = ML g := by
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · exact mat3_x3 canons.1
  · exact mat3_x3 canons.2.1

theorem img_lt {g k : Nat} (hg : g < 2) (hk : k < 22880) : img g k < 22880 := by
  unfold img
  split_ifs
  · exact al_lt hk
  · exact be_lt hk

theorem edge_mat {g k : Nat} (hg : g < 2) (hk : k < 22880) : ML g * KM k = KM (img g k) * ML g := by
  have h := congrArg (mat3 64 4096) (edge_facts hg hk).2
  rw [mul_mat3 (canon_x3 hg) (canon_kx hk), mul_mat3 (canon_kx (img_lt hg hk)) (canon_x3 hg),
    ML_x3 hg, mat3_kx, mat3_kx] at h
  exact h

theorem conjA_mat {k : Nat} (hk : k < 22880) : ML 0 * KM k * ML 0 = KM (r32 AL k) := by
  have h := edge_mat (g := 0) (by norm_num) hk
  have e : img 0 k = r32 AL k := rfl
  rw [e] at h
  rw [h, mul_assoc, A_sq, mul_one]

theorem conjB_mat {k : Nat} (hk : k < 22880) : ML 1 * KM k * ML 2 = KM (r32 BE k) := by
  have h := edge_mat (g := 1) (by norm_num) hk
  have e : img 1 k = r32 BE k := rfl
  rw [e] at h
  rw [h, mul_assoc, B_B2, mul_one]

theorem sort_facts {i : Nat} (hi : i < 22880) : r32 SO i < 22880 ∧ r32 SOI i < 22880 ∧
    r32 SO (r32 SOI i) = i ∧ (i + 1 < 22880 → kx (r32 SO i) < kx (r32 SO (i + 1))) := by
  have hs : i / 352 < 65 := by omega
  have h := sortAll (i / 352) hs
  unfold sortSl at h
  rw [strictB_eq] at h
  have h' := allN_iff.1 h (i % 352) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (i / 352) 352) (i % 352) = i := by
    change i / 352 * 352 + i % 352 = i
    omega
  rw [e] at h'
  unfold sortAt at h'
  rw [strictB_eq, strictB_eq, Raw.Orb.bAnd_eq,Raw.Orb.bAnd_eq,Raw.Orb.bAnd_eq,Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, Nat.beq_eq] at h'
  obtain ⟨h1, h2, h3, h4⟩ := h'
  refine ⟨h1, h2, h3, fun hi1 => ?_⟩
  rw [Raw.Orb.bIf_eq, if_pos (Nat.blt_eq.mpr hi1), Nat.blt_eq] at h4
  exact h4

theorem sort_mono {a b : Nat} (hab : a < b) (hb : b < 22880) : kx (r32 SO a) < kx (r32 SO b) := by
  induction b with
  | zero => omega
  | succ b ih =>
    have h := (sort_facts (i := b) (by omega)).2.2.2 hb
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hab | rfl
    · exact lt_trans (ih hab (by omega)) h
    · exact h

theorem kx_inj {j k : Nat} (hj : j < 22880) (hk : k < 22880) (h : kx j = kx k) : j = k := by
  obtain ⟨-, hj1, hj2, -⟩ := sort_facts hj
  obtain ⟨-, hk1, hk2, -⟩ := sort_facts hk
  by_contra hne
  have hne' : r32 SOI j ≠ r32 SOI k := fun e => hne (by rw [← hj2, ← hk2, e])
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · have := sort_mono hlt hk1
    rw [hj2, hk2, h] at this
    exact lt_irrefl _ this
  · have := sort_mono hlt hj1
    rw [hj2, hk2, h] at this
    exact lt_irrefl _ this

theorem KM_inj {j k : Nat} (hj : j < 22880) (hk : k < 22880) (h : KM j = KM k) : j = k := by
  change toMat 64 (unlane 64 (laneK j)) = toMat 64 (unlane 64 (laneK k)) at h
  rw [← mat3_kx, ← mat3_kx] at h
  exact kx_inj hj hk (mat3_inj (by norm_num) (canon_kx hj) (canon_kx hk) h)

theorem alpha_inv {k : Nat} (hk : k < 22880) : r32 AL (r32 AL k) = k := by
  apply KM_inj (al_lt (al_lt hk)) hk
  rw [← conjA_mat (al_lt hk), ← conjA_mat hk]
  calc ML 0 * (ML 0 * KM k * ML 0) * ML 0 = (ML 0 * ML 0) * KM k * (ML 0 * ML 0) := by
        simp only [mul_assoc]
    _ = KM k := by rw [A_sq, one_mul, mul_one]

theorem beta_ord {k : Nat} (hk : k < 22880) : r32 BE (r32 BE (r32 BE k)) = k := by
  have h1 := be_lt hk
  have h2 := be_lt h1
  apply KM_inj (be_lt h2) hk
  have e1 : ML 1 * ML 1 * ML 1 = 1 := by rw [mul_assoc, ← B2_eq, B_B2]
  have e2 : ML 2 * ML 2 * ML 2 = 1 := by
    calc ML 2 * ML 2 * ML 2 = ML 2 * (ML 1 * ML 1) * ML 2 := by rw [← B2_eq]
      _ = (ML 2 * ML 1) * (ML 1 * ML 2) := by simp only [mul_assoc]
      _ = 1 := by rw [B2_B, B_B2, one_mul]
  rw [← conjB_mat h2, ← conjB_mat h1, ← conjB_mat hk]
  calc ML 1 * (ML 1 * (ML 1 * KM k * ML 2) * ML 2) * ML 2 =
      (ML 1 * ML 1 * ML 1) * KM k * (ML 2 * ML 2 * ML 2) := by simp only [mul_assoc]
    _ = KM k := by rw [e1, e2, one_mul, mul_one]

theorem laneK_canon {k : Nat} (hk : k < 22880) : (laneK k).wf = true := by
  rw [laneK_eq]
  apply V.wf_of_bits
  intro t
  change ((kx k &&& (2 ^ 4096 - 1)).testBit t && (kx k >>> 4096).testBit t) = false
  rw [lo_bit, Nat.testBit_shiftRight]
  cases h : (kx k).testBit t
  · simp
  · rw [(canon_kx hk).2 t h]
    simp

theorem rowsWF_laneK {k : Nat} (hk : k < 22880) : RowsWF (unlane 64 (laneK k)) :=
  RowsWF.of_canonM (canonM_unlane 64 (laneK_canon hk))

theorem toVM_keyW (k : Nat) : toVM (keyW k) = unlane 64 (laneK k) := toVM_ofV_unlane _

theorem conj_lanes {G Gi : V} (hG : Canon G) (hGi : Canon Gi) {X K : V} (hX : RowsWF (unlane 64 X))
    (hK : K.wf = true)
    (h : toMat 64 (unlane 64 G) * toMat 64 (unlane 64 X) * toMat 64 (unlane 64 Gi) =
      toMat 64 (unlane 64 K)) :
    conjM 64 (unlane 64 G) (unlane 64 Gi) (unlane 64 X) = unlane 64 K := by
  have hGw := RowsWF.of_canonM (canonM_unlane 64 hG.wf)
  have hGiw := RowsWF.of_canonM (canonM_unlane 64 hGi.wf)
  have hs : (mul 64 (unlane 64 G) (unlane 64 X)).size = 64 := by
    unfold mul
    rw [Array.size_map, unlane_size]
  apply eq_of_canonM (canonM_mul hs (RowsWF.mul _ 64 hGw hX) (canonM_unlane 64 hGi.wf))
    (canonM_unlane 64 hK)
  rw [toMat_mul hs (RowsWF.mul _ 64 hGw hX) hGiw, toMat_mul (unlane_size' _) hGw hX, h]

theorem hA_key {k : Nat} (hk : k < 22880) : conjW 64 (wA ()) (wA ()) (keyW k) = keyW (r32 AL k) := by
  apply toVM_inj
  rw [toVM_conjW, toVM_wA, toVM_keyW, toVM_keyW]
  exact conj_lanes canons.1 canons.1 (rowsWF_laneK hk) (laneK_canon (al_lt hk)) (conjA_mat hk)

theorem hB_key {k : Nat} (hk : k < 22880) : conjW 64 (wB ()) (wBi ()) (keyW k) = keyW (r32 BE k) := by
  apply toVM_inj
  rw [toVM_conjW, toVM_wB, toVM_wBi, toVM_keyW, toVM_keyW]
  exact conj_lanes canons.2.1 canons.2.2.1 (rowsWF_laneK hk) (laneK_canon (be_lt hk)) (conjB_mat hk)

theorem keyW_inj {j k : Nat} (hj : j < 22880) (hk : k < 22880) (h : keyW j = keyW k) : j = k := by
  apply KM_inj hj hk
  have := congrArg (fun X => toMat 64 (toVM X)) h
  simp only [toVM_keyW] at this
  exact this

theorem root_key : keyW 0 = wRoot () := by
  have h := root_ok
  unfold rootK at h
  have e : kx 0 = x3 8 := Nat.eq_of_beq_eq_true h
  have hl : laneK 0 = ln 8 := by
    rw [laneK_eq, e, ← x3_lane canons.2.2.2.2.2.2.2.2.1]
  rw [wRoot_eq]
  unfold keyW
  rw [hl]

theorem orbitData_eq : orbitData () = orbLit := by
  have hs := keys_size
  have hal : ∀ k < orbLit.keys.size, ap orbLit.alpha k = r32 AL k :=
    fun k hk => ap_tabOf AL (by omega)
  have hbe : ∀ k < orbLit.keys.size, ap orbLit.beta k = r32 BE k :=
    fun k hk => ap_tabOf BE (by omega)
  unfold orbitData
  refine BfsSpec.conjBFSW_eq_of (fp := r32 PA) (fl := r32 LB) (dep := r32 DP) (by rw [hs]; decide)
    (by rw [keys_get (by norm_num), root_key]) (by rw [hs]; exact tabOf_size AL)
    (by rw [hs]; exact tabOf_size BE) (by rw [hs]; exact tabOf_size PA)
    (by rw [hs]; exact tabOf_size LB) hal hbe
    (fun k hk => ap_tabOf PA (by omega)) (fun k hk => ap_tabOf LB (by omega))
    (by rw [hs]; exact bfs') (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_)
    (fun i hi j hj e => ?_) (fun k hk => (dep_pt (by omega)).1)
    (fun k hk0 hk => (dep_pt (by omega)).2 (by omega))
  · rw [hal k hk, keys_get (by omega), keys_get (al_lt (by omega))]
    exact hA_key (by omega)
  · rw [hbe k hk, keys_get (by omega), keys_get (be_lt (by omega))]
    exact hB_key (by omega)
  · rw [hal k hk, hal (r32 AL k) (by rw [hs]; exact al_lt (by omega))]
    exact alpha_inv (by omega)
  · have h1 := be_lt (k := k) (by omega)
    have h2 := be_lt h1
    rw [hbe k hk, hbe (r32 BE k) (by rw [hs]; exact h1),
      hbe (r32 BE (r32 BE k)) (by rw [hs]; exact h2)]
    exact beta_ord (by omega)
  · rw [keys_get (by omega), keys_get (by omega)] at e
    exact keyW_inj (by omega) (by omega) e

end CertificateChecks.KernelSpor.SuzK

end

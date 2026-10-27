module

public import CFSG.Certificates.Kernel.U6FlagSound
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2FlagCert
public import Certificates.Data.Kernel.U6.FlagPack
import CFSG.Certificates.Kernel.U6LinProved
import CFSG.Certificates.Kernel.U6FlagProved
public import CFSG.Certificates.Kernel.U6LinSound
public import Certificates.Data.Kernel.U6.FlagK

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6F2 CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (unpackN packN unpackBlk packBlks linBits)
open CFSG.EvenSmallLie.UnitarySix.YamadaN2 (t2Bits aBits2 n0Bits2 n1Bits2 cMask2 dBlock2 dFb2
  dCols2 dTarget2 candBlock dCheck2W dEcols2 dQcols2 s2CheckW s2Qcols s2Fb s2Block s2Target
  s2Sol s2Farkas tytBits tauBits vBits yProd bitList lamZ linE emb2m par640 eProdBits)

@[expose] noncomputable def dBlock2K (v k : ℕ) : ℕ :=
  nIf(Nat.blt k 4,
    Nat.xor (mulF 8 (mulF 8 (packM 8 t2Bits) (fget v k 64)) (packM 8 t2Bits)) (fget v k 64),
    Nat.xor (Nat.xor (mulF 8 (mulF 8 (packM 8 (n0Bits2 ((k - 4) / 4))) (fget v ((k - 4) % 4) 64))
        (packM 8 (n1Bits2 ((k - 4) / 4))))
      (msumK 4 (cMask2 ((k - 4) / 4) ((k - 4) % 4)) fun m => fget v m 64))
      (msumK 4 (Nat.mod (Nat.shiftRight
          (fget (fget v 4 64) (2 * ((k - 4) / 4) + (k - 4) % 4 / 2) 8) (4 * ((k - 4) % 4 % 2))) 16)
        fun m => packM 8 (aBits2 m)))

@[expose] noncomputable def dFb2K (v : ℕ) : ℕ :=
  orN 20 fun k => Nat.shiftLeft (dBlock2K v k) (Nat.mul k 64)

set_option maxHeartbeats 1000000 in
theorem dFb2_eq (v : ℕ) : dFb2 v = dFb2K v := by
  rw [dFb2, packBlks_eq, packN_eq_proved]
  refine orN_congr fun k hk => ?_
  congr 1
  interval_cases k <;>
    simp only [dBlock2, CFSG.EvenSmallLie.UnitarySix.YamadaN2.lamMaskOf, unpackBlk_eq,
      Nat.reduceLT, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
      ite_true, ite_false, packM_bxor_proved, packM_bmul_proved, packM_unpackN_proved,
      packM_msum2_proved, getD_unpackN_proved] <;>
    rfl

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem dCheck2W_true : dCheck2W = true := by
  rw [dCheck2W, Bool.and_eq_true]
  constructor
  · refine certCheckWith_of_idRowsK_proved (F := (List.range (5 * 64)).map fun l => dFb2K (2 ^ l))
      (B := dCols2.toList) (fun l hl => by rw [getLD_map_range _ _ hl, dFb2_eq]) rfl
      (by decide +kernel) (by decide +kernel) ?_
    decide +kernel
  · simp only [dFb2_eq]
    decide +kernel

@[expose] noncomputable def e2K (v m : ℕ) : ℕ :=
  emb2K (Nat.mod (Nat.shiftRight v (Nat.mul 32 m)) (2 ^ 32))

@[expose] noncomputable def linEK (PL : List (List ℕ)) (j m v : ℕ) : ℕ :=
  (List.range (bitList (cMask2 j m)).length).foldl (fun acc i => Nat.xor acc
      (mulF 18 (e2K v ((bitList (cMask2 j m)).getD i 0)) (getLD 0 (getLD [] PL (4 * j + m)) i)))
    (mulF 18 (mulF 18 (getLD 0 vP j) (e2K v m)) (getLD 0 vP j))

@[expose] noncomputable def s2BlockK (TY : List ℕ) (PL : List (List ℕ)) (v k : ℕ) : ℕ :=
  nIf(Nat.blt k 4,
    blk2K (Nat.xor (mulF 18 (e2K v k) (getLD 0 TY k)) (mulF 18 (mulF 18 tauP (e2K v k)) tauP)),
    blk2K (linEK PL ((k - 4) / 4) ((k - 4) % 4) v))

@[expose] noncomputable def s2FbK (z v : ℕ) : ℕ :=
  orN 20 fun k => Nat.shiftLeft
    (Nat.mod (s2BlockK (getLD [] tytP z) (getLD [] plP z) v k) (2 ^ 32)) (Nat.mul k 32)

theorem tauP_spec : packM 18 tauBits = tauP := by decide +kernel

theorem vP_spec : ∀ j < 4, packM 18 (vBits j) = getLD 0 vP j := by decide +kernel

theorem tytP_spec : ∀ z < 4, ∀ k < 4, packM 18 (tytBits z k) = getLD 0 (getLD [] tytP z) k := by
  decide +kernel

@[expose] def plOK (z : ℕ) : Prop :=
  ∀ j < 4, ∀ m < 4, ∀ i < (bitList (cMask2 j m)).length,
    packM 18 (CFSG.EvenSmallLie.UnitarySix.YamadaPar.bmul 18 18
        (yProd z ((bitList (cMask2 j m)).drop (i + 1))) (eProdBits (lamZ z j m))) =
      getLD 0 (getLD [] (getLD [] plP z) (4 * j + m)) i

theorem plP_0 : plOK 0 := by unfold plOK; decide +kernel
theorem plP_1 : plOK 1 := by unfold plOK; decide +kernel
theorem plP_2 : plOK 2 := by unfold plOK; decide +kernel
theorem plP_3 : plOK 3 := by unfold plOK; decide +kernel

theorem plP_spec {z : ℕ} (hz : z < 4) : plOK z := by
  interval_cases z
  exacts [plP_0, plP_1, plP_2, plP_3]

theorem packM_emb2m (v m : ℕ) : packM 18 (emb2m v m) = e2K v m := packM_emb2_proved _

theorem linE_eq {z : ℕ} (hz : z < 4) (v : ℕ) {j m : ℕ} (hj : j < 4) (hm : m < 4) :
    packM 18 (linE z j m v) = linEK (getLD [] plP z) j m v := by
  simp only [linE]
  rw [packM_foldl_bxor_proved, packM_bmul_proved, packM_bmul_proved, packM_emb2m, vP_spec j hj]
  unfold linEK
  exact foldl_congr_range _ fun a i hi => by
    rw [packM_bmul_proved, packM_emb2m, plP_spec hz j hj m hm i hi]

theorem s2Block_eq {z : ℕ} (hz : z < 4) (v : ℕ) {k : ℕ} (hk : k < 20) :
    s2Block z v k = s2BlockK (getLD [] tytP z) (getLD [] plP z) v k := by
  by_cases h4 : k < 4
  · have hb : Nat.blt k 4 = true := Nat.blt_eq.mpr h4
    rw [s2Block, ite_eq_left_of_eq_true _ _ (eq_true h4), blk2Bits_eq_proved]
    simp only [packM_bxor_proved, packM_bmul_proved, packM_emb2m]
    rw [tytP_spec z hz k h4, tauP_spec]
    unfold s2BlockK
    rw [hb]
  · have hb : Nat.blt k 4 = false := Bool.eq_false_iff.mpr fun h => h4 (Nat.blt_eq.mp h)
    rw [s2Block, ite_eq_right_of_eq_false _ _ (eq_false h4), blk2Bits_eq_proved,
      linE_eq hz v (by omega) (Nat.mod_lt _ (by norm_num))]
    unfold s2BlockK
    rw [hb]

theorem s2Fb_eq {z : ℕ} (hz : z < 4) (v : ℕ) : s2Fb z v = s2FbK z v := by
  rw [s2Fb, cat20_eq_proved, s2FbK]
  exact orN_congr fun k hk => by rw [s2Block_eq hz v hk]

theorem s2Inj {z : ℕ} (hz : z < 2) (hp : (s2Qcols z).size = 640)
    (h : idRowsK 128 ((List.range 128).map fun l => s2FbK z (2 ^ l)) (List.replicate 128 0) []
      (s2Qcols z).toList = true) :
    CFSG.EvenSmallLie.UnitarySix.YamadaPar.injCheckWith 128 640 (linBits 128 640 (s2Fb z))
      (s2Qcols z) = true :=
  injCheckWith_of_idRowsK_proved (fun l hl => by rw [getLD_map_range _ _ hl, s2Fb_eq (by omega)])
    hp h

set_option maxHeartbeats 0 in
theorem s2CheckW_true : s2CheckW = true := by
  have i0 := s2Inj (z := 0) (by norm_num) (by decide +kernel) (by decide +kernel)
  have i1 := s2Inj (z := 1) (by norm_num) (by decide +kernel) (by decide +kernel)
  have t0 : (s2Fb 0 (s2Sol 0) == s2Target 0) = true := by
    rw [s2Fb_eq (by norm_num)]
    decide +kernel
  have t1 : (s2Fb 1 (s2Sol 1) == s2Target 1) = true := by
    rw [s2Fb_eq (by norm_num)]
    decide +kernel
  have f2 : ((List.range 128).all fun j => !par640 (s2Farkas 2 &&& s2Fb 2 (2 ^ j))) = true := by
    simp only [s2Fb_eq (by norm_num : (2 : ℕ) < 4), par640_eq_proved]
    decide +kernel
  have f3 : ((List.range 128).all fun j => !par640 (s2Farkas 3 &&& s2Fb 3 (2 ^ j))) = true := by
    simp only [s2Fb_eq (by norm_num : (3 : ℕ) < 4), par640_eq_proved]
    decide +kernel
  have p2 : par640 (s2Farkas 2 &&& s2Target 2) = true := by
    rw [par640_eq_proved]
    decide +kernel
  have p3 : par640 (s2Farkas 3 &&& s2Target 3) = true := by
    rw [par640_eq_proved]
    decide +kernel
  rw [s2CheckW]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨fun z hz => ?_, fun h hh => ?_⟩
  · interval_cases z
    · exact ⟨i0, t0⟩
    · exact ⟨i1, t1⟩
  · interval_cases h
    · exact ⟨fun j hj => List.all_eq_true.mp f2 j (List.mem_range.mpr hj), p2⟩
    · exact ⟨fun j hj => List.all_eq_true.mp f3 j (List.mem_range.mpr hj), p3⟩

end CertificateChecks.KernelU6

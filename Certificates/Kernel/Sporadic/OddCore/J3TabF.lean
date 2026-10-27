module

public import Certificates.Kernel.Sporadic.OddCore.J3TabE
public import Certificates.Kernel.Sporadic.OddCore.J3TabP
public import Certificates.Kernel.Sporadic.OddCore.J3HypSylF
public import CFSG.Certificates.Kernel.Spor.ClassOneH
public import CFSG.Certificates.Kernel.J2CoverSnd.Packed
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinEJ3Check

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3Tab

open CFSG.EvenSporadicStandard.HypOne.J3 CFSG.EvenSporadicStandard.Fin76b.J3
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CertificateChecks.KernelSpor.J3HypSyl

theorem blt_iff {a b : Nat} : Nat.blt a b = true ↔ a < b := by
  rw [Nat.blt_eq]

theorem allIn_iff {n : Nat} {p : Nat → Bool} :
    CFSG.Sporadic.Th.Native.allIn 0 n p = true ↔ ∀ k < n, p k = true := by
  unfold CFSG.Sporadic.Th.Native.allIn
  rw [Nat.sub_zero]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.all_succ, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h1 k hk
      · simpa using h2
    · intro h
      exact ⟨fun k hk => h k (by omega), by simpa using h n (by omega)⟩

theorem rec_spec {a : Nat} (ha : a < 128) : mK a 0 = a ∧ ∀ c < 127, mK a (c + 1) < 128 ∧
    mK a (c + 1) = r32 J3HS.POS (mK a (parOf J3HS.PL (c + 1)) * 3 + labOf J3HS.PL (c + 1)) := by
  have h := (bAnd_iff _ _).1 (allN_spec rec_ok a ha)
  refine ⟨Nat.eq_of_beq_eq_true h.1, fun c hc => ?_⟩
  have h2 := (bAnd_iff _ _).1 (allN_spec h.2 c hc)
  exact ⟨blt_iff.1 h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem t_spec : tI < 128 ∧ J3HS.T tI = J3CentP 9 ∧ J3HS.T 0 = pidn 6156 13 := by
  have h := t_ok
  simp only [bAnd_iff] at h
  exact ⟨blt_iff.1 h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem step_eq {i j : Nat} (hi : i < 128) (hj : j < 3) :
    stepK 6156 13 (mask 13) true J3HS.G J3HS.GI j (J3HS.T i) =
      pcomp 6156 13 (mask 13) (J3HS.T i) (J3HS.GI j) := by
  unfold stepK
  rw [(gen hj).2.2]
  exact congrArg (fun x => pcomp 6156 13 (mask 13) x (J3HS.GI j))
    (CFSG.KC.J2Cover.Snd.pcomp_id' (hT hi)).2

theorem mul_spec {a : Nat} (ha : a < 128) : ∀ b < 128, mK a b < 128 ∧
    pcomp 6156 13 (mask 13) (J3HS.T a) (J3HS.T b) = J3HS.T (mK a b) := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb
    obtain ⟨h0, hs⟩ := rec_spec ha
    rcases b with _ | c
    · rw [h0, t_spec.2.2]
      exact ⟨ha, (CFSG.KC.J2Cover.Snd.pcomp_id' (hT ha)).1⟩
    · have hpe := penumPt_specH (s_pe (c + 1) (by rw [hcnt]; exact hb))
      obtain ⟨hlt, hlab, hTb, -⟩ := hpe.2.1 (Nat.succ_ne_zero c)
      obtain ⟨ih1, ih2⟩ := ih _ hlt (by omega)
      have hpos := (penumPt_specH (s_pe _ (by rw [hcnt]; exact ih1))).2.2.1 _ hlab
      obtain ⟨hrc, hre⟩ := hs c (by omega)
      refine ⟨hrc, ?_⟩
      have e1 : pcomp 6156 13 (mask 13) (J3HS.T a) (J3HS.T (c + 1)) =
          pcomp 6156 13 (mask 13) (J3HS.T (mK a (parOf J3HS.PL (c + 1))))
            (J3HS.GI (labOf J3HS.PL (c + 1))) := by
        rw [hTb, step_eq (by omega) hlab,
          ← CFSG.KC.J2Cover.Snd.pcomp_assoc' (hT ha) (hT (by omega)) (gen hlab).1, ih2]
      have e2 : J3HS.T (mK a (c + 1)) =
          pcomp 6156 13 (mask 13) (J3HS.T (mK a (parOf J3HS.PL (c + 1))))
            (J3HS.GI (labOf J3HS.PL (c + 1))) := by
        rw [← step_eq ih1 hlab, ← hpos.2.1]
        exact congrArg J3HS.T hre
      exact e1.trans e2.symm

theorem syl_size : sylList.size = 128 := by
  rw [syl_eq]
  simp

theorem syl_get {i : Nat} (hi : i < 128) : sylList[i]! = fE i := by
  rw [syl_eq, getElem!_pos _ i (by simpa using hi)]
  simp

theorem syl_hk : hkeysDistinct 6156 sylList.toList = true := by
  have h := (mulH_sound base.1 (fun j hj => (gen hj).2.2) s_tabs base.2.2.2.2.2.2 s_pe s_hs).2.2
  unfold sylList
  rw [closure_eq]
  exact h

theorem hkey_inj_of {n : ℕ} {L : Array Table} (hk : hkeysDistinct n L.toList = true) :
    ∀ a < L.size, ∀ b < L.size, hkey n L[a]! = hkey n L[b]! → a = b := by
  have hsorted := (CFSG.Sporadic.Schreier.pairwise_of_strictlyIncreasing hk).imp
    (fun hab => Nat.ne_of_lt hab)
  have hkeys : (L.toList.map fun T => (hkey n T).toNat).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.1 hsorted
  intro a ha b hb e
  have e' : (L.toList.map fun T => (hkey n T).toNat)[a]'(by simpa using ha) =
      (L.toList.map fun T => (hkey n T).toNat)[b]'(by simpa using hb) := by
    simp only [List.getElem_map, Array.getElem_toList]
    rw [← getElem!_pos L a ha, ← getElem!_pos L b hb, e]
  exact (List.Nodup.getElem_inj_iff hkeys).1 e'

theorem idx_get {k : Nat} (hk : k < 128) : sylIdx (fE k) = k := by
  rw [← syl_get hk]
  unfold sylIdx sylIndex
  rw [CFSG.KS.ClassOneH.hashIndex_get (hkey_inj_of syl_hk) (by rw [syl_size]; exact hk)]
  rfl

theorem mF_of {a b : Nat} (ha : a < 128) (hb : b < 128) : mF a b = mK a b := by
  unfold mF
  rw [(blt_iff.2 ha : Nat.blt a 128 = true), (blt_iff.2 hb : Nat.blt b 128 = true)]

theorem prod_eq {a b : Nat} (ha : a < 128) (hb : b < 128) :
    compT 6156 sylList[a]! sylList[b]! = fE (mK a b) := by
  rw [syl_get ha, syl_get hb]
  unfold fE
  rw [compT_unpack (hT ha) (hT hb), (mul_spec ha b hb).2]

theorem mulJ3_eq : mulJ3 = mF := by
  funext a b
  unfold mulJ3 mulTabJ3
  by_cases ha : a < 128
  · rw [getElem!_pos _ a (by simpa using ha), Array.getElem_ofFn]
    by_cases hb : b < 128
    · rw [getElem!_pos _ b (by simpa using hb), Array.getElem_ofFn, mF_of ha hb, prod_eq ha hb,
        idx_get (mul_spec ha b hb).1]
    · rw [getElem!_neg _ b (by simpa using hb)]
      unfold mF
      rw [(blt_iff.2 ha : Nat.blt a 128 = true),
        (Bool.eq_false_iff.2 fun h => hb (blt_iff.1 h) : Nat.blt b 128 = false)]
      rfl
  · rw [getElem!_neg _ a (by simpa using ha)]
    unfold mF
    rw [(Bool.eq_false_iff.2 fun h => ha (blt_iff.1 h) : Nat.blt a 128 = false)]
    rfl

theorem tIdx_eq : tIdxJ3 = tI := by
  unfold tIdxJ3
  rw [J3HypSyl.t0_eq, ← t_spec.2.1]
  exact idx_get t_spec.1

theorem facts24595 : j3E_check = true := by
  unfold j3E_check tableOK
  rw [mulJ3_eq, tIdx_eq]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨e_ok, ?_⟩, t_spec.1⟩, ?_⟩, ?_⟩
  · rw [allIn_iff]
    intro a ha
    rw [allIn_iff]
    intro b hb
    obtain ⟨h1, -⟩ := mul_spec ha b hb
    rw [Bool.and_eq_true, decide_eq_true_eq, mF_of ha hb, prod_eq ha hb, syl_get h1]
    exact ⟨h1, tblEq_self (hT h1)⟩
  · rw [syl_get t_spec.1, J3HypSyl.t0_eq, ← t_spec.2.1]
    exact tblEq_self (hT t_spec.1)
  · rw [syl_get (by norm_num), hid, ← t_spec.2.2]
    exact tblEq_self (hT (by norm_num))

theorem facts24607 : j3PinCheck = true := by
  unfold j3PinCheck
  rw [mulJ3_eq, tIdx_eq]
  exact pin_ok

end CertificateChecks.KernelSpor.J3Tab

end

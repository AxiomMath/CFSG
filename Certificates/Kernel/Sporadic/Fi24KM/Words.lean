module

public import Certificates.Kernel.Sporadic.Fi24Br.Img
public import Certificates.Kernel.Sporadic.Fi24KM.Light
import Certificates.Kernel.Sporadic.Fi24KM.S0
import Certificates.Kernel.Sporadic.Fi24KM.S1
import Certificates.Kernel.Sporadic.Fi24KM.S2
import Certificates.Kernel.Sporadic.Fi24KM.R
import CFSG.Certificates.Kernel.Common.ForallChunks
public import Certificates.Kernel.Sporadic.Fi24KM.Prog

public section

set_option maxRecDepth 400000

namespace CFSG.KD.KMFi24

#kc_forall_chunks S.all (fun k => sC k = true) 29 CFSG.KD.KMFi24.sC 1
#kc_forall_chunks R.all (fun j => rC j = true) 3 CFSG.KD.KMFi24.rC 1
#kc_forall_chunks M.all (fun j => mC j = true) 8 CFSG.KD.KMFi24.mC 1

end CFSG.KD.KMFi24

namespace CertificateChecks.KernelSpor.Fi24KM

open CFSG.KC.Ord CFSG.KC.WP CFSG.KS.Ord CFSG.KS.Mat3 CertificateChecks.KernelHomG
  CertificateChecks.KernelWP CertificateChecks.KernelSpor.Fi24Rels
  CFSG.HardMathSupport.Dickson.I271.TabMThreeA
open CFSG.KD.BrFi24 (RB MUL ONE)

theorem hS : ∀ k < 29,
    progOK RB 11 CFSG.KD.KMFi24.RS MUL ONE (CFSG.KD.KMFi24.PS k) (CFSG.KD.KMFi24.RS k) = true :=
  CFSG.KD.KMFi24.S.all

theorem goodS : ∀ k < 29, Good (Canon3 609961) (mat3 781 609961) RB 11 (CFSG.KD.KMFi24.RS k)
    (CFSG.KD.KMFi24.WC k) :=
  states_good hs hroot hinv CFSG.KD.KMFi24.statesL hS

theorem hR : ∀ j < 3,
    progOK RB 11 CFSG.KD.KMFi24.RS MUL ONE (CFSG.KD.KMFi24.QR j) ONE = true :=
  CFSG.KD.KMFi24.R.all

theorem relsOne : ∀ v ∈ kmRels (), (v.map fun l => mat3 781 609961 (letM RB 11 l)).prod = 1 :=
  rels_of_cover hs hroot hinv CFSG.KD.KMFi24.relsB
    (relProgs_one hs hroot hinv goodS CFSG.KD.KMFi24.relsL hR) CFSG.KD.KMFi24.relsW

theorem hM : ∀ j < 8, notB (Nat.beq (progTop RB (nat_lit 11) CFSG.KD.KMFi24.RS MUL ONE
    (CFSG.KD.KMFi24.QM j)) ONE) = true :=
  CFSG.KD.KMFi24.M.all

theorem coverAll_spec {rels : List (List (Nat × Bool))} {WC PR : Nat → List Nat} {nR : Nat}
    {cv : Nat → Nat} : ∀ n, coverAll rels WC PR nR cv n = true →
      ∀ r < n, coverOK rels WC PR nR r (cv r) = true
  | 0, _, r, hr => absurd hr (Nat.not_lt_zero r)
  | n + 1, h, r, hr => by
    unfold coverAll at h
    rw [Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
    · exact coverAll_spec n h.1 r hr
    · exact h.2

theorem movesNe : ∀ v ∈ kmMoves (), (v.map fun l => mat3 781 609961 (letM RB 11 l)).prod ≠ 1 := by
  intro v hv
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hv
  have hr8 : r < 8 := by
    have := Nat.le_of_ble_eq_true CFSG.KD.KMFi24.movesLen
    omega
  have hc := coverAll_spec _ CFSG.KD.KMFi24.movesW r hr
  unfold coverOK at hc
  rw [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨-, hw⟩ := hc
  have e1 : CFSG.KD.KMFi24.cvI r / 1048576 = 0 := by
    unfold CFSG.KD.KMFi24.cvI
    omega
  have e2 : CFSG.KD.KMFi24.cvI r / 1024 % 1024 = 0 := by
    unfold CFSG.KD.KMFi24.cvI
    omega
  have e3 : CFSG.KD.KMFi24.cvI r % 1024 = r := by
    unfold CFSG.KD.KMFi24.cvI
    omega
  rw [e1, e2, e3, List.getD_eq_getElem _ _ hr] at hw
  have hrot : ∀ w : List Nat, rotC w 0 = w := fun w => by simp [rotC]
  rw [hrot] at hw
  change _ = progWord CFSG.KD.KMFi24.WC (CFSG.KD.KMFi24.QM r) at hw
  rw [CertificateChecks.KernelWPX.prod_eq_wordMat, hw]
  intro h1
  obtain ⟨hl, hrf⟩ := relProgsOK_spec 8 CFSG.KD.KMFi24.movesL r hr8
  obtain ⟨hq, hmt⟩ := top_sound hs hroot hinv (RS := CFSG.KD.KMFi24.RS) (WC := CFSG.KD.KMFi24.WC) hl
    (fun ins hi h1' => goodS _ (refs_of 29 _ hrf ins hi h1'))
  have hX := mat3_inj (by norm_num) hq hs.one_q (hmt.trans (h1.trans hs.one_mt.symm))
  have hm := hM r hr8
  rw [hX, Nat.beq_refl] at hm
  exact Bool.false_ne_true hm

theorem km_words : ∀ x : Nat → GL (Fin 781) (ZMod 3),
    (∀ k < 11, (x k : Matrix (Fin 781) (Fin 781) (ZMod 3)) = CFSG.KD.Fi24Img.img k) →
    (∀ v ∈ kmRels (), CFSG.Sporadic.Bridge.wordProd x v = 1) ∧
      ∀ v ∈ kmMoves (), CFSG.Sporadic.Bridge.wordProd x v ≠ 1 := by
  intro x hx
  have hx' : ∀ g < 11, (x g).val = mat3 781 609961 (RB (g + 1)) := fun g hg =>
    (hx g hg).trans (CertificateChecks.KernelSpor.Fi24Img.img_eq g hg)
  refine ⟨fun v hv => ?_, fun v hv h => ?_⟩
  · apply Units.ext
    rw [CertificateChecks.KernelWPX.val_wordProd hs hroot hinv hx'
      (relsBounded_spec CFSG.KD.KMFi24.relsB v hv), Units.val_one, relsOne v hv]
  · apply movesNe v hv
    rw [← CertificateChecks.KernelWPX.val_wordProd hs hroot hinv hx'
      (relsBounded_spec CFSG.KD.KMFi24.movesB v hv), h, Units.val_one]

end CertificateChecks.KernelSpor.Fi24KM

end

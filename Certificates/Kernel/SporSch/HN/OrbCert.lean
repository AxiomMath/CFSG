module

public import Certificates.Kernel.SporSch.HN.OrbX
public import Certificates.Kernel.SporSch.HN.OrbCertK
public import Certificates.Kernel.SporSch.HN.BindS
public import Certificates.Kernel.SporSch.HN.BindV
public import Certificates.Kernel.SporSch.HN.BindA
public import Certificates.Kernel.SporSch.HN.BindP
public import CFSG.Certificates.Kernel.SporSch.HNXCertSound
public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Cert
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

namespace CertificateChecks.KernelSporSch.HNXCert

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS.SporSch CFSG.KD.LgHNX CFSG.KD.OrdHN
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.HNXOrb
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native

theorem hns_checks : HNXChecks hnsData TX HNX.CNT HNX.SGT MS CM3 M GA GB (RW 1) (RW 2) V0C
    HNSA.chars HNSB.chars (HNXRoot.c0 ++ HNXRoot.c1) :=
  ⟨rfl, rfl, HNSA.eq, HNSB.eq, rootDigits_eq, CFSG.KD.LgHNX.consts, seedA_ok', seedB_ok', bindA,
    bindB, hcore', sum_ok, hsort', link_ok, rec0_root, root_ok⟩

private theorem allBlk_iff {b len : Nat} {f : Nat → Bool} :
    allBlk b f len = true ↔ ∀ l < len, f (b + l) = true := by
  induction len with
  | zero => exact ⟨fun _ l hl => absurd hl (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ len ih =>
    show Bool.rec false (allBlk b f len) (f (Nat.add b len)) = true ↔ _
    constructor
    · intro h l hl
      cases hf : f (Nat.add b len) <;> rw [hf] at h
      · exact absurd h Bool.false_ne_true
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
        · exact ih.1 h l hl
        · exact hf
    · intro h
      have h1 : f (Nat.add b len) = true := h len (Nat.lt_succ_self _)
      rw [h1]
      exact ih.2 fun l hl => h l (Nat.lt_succ_of_lt hl)

private theorem allN_blocks {f : Nat → Bool} : ∀ q : Nat,
    Nat.rec (motive := fun _ => Bool) true
      (fun h ih => Bool.rec false ih (allBlk (Nat.shiftLeft h 6) f 64)) q = true ↔
      ∀ i < 64 * q, f i = true
  | 0 => ⟨fun _ i hi => absurd hi (by omega), fun _ => rfl⟩
  | q + 1 => by
    show Bool.rec false _ (allBlk (Nat.shiftLeft q 6) f 64) = true ↔ _
    have hs : Nat.shiftLeft q 6 = 64 * q := by
      change q <<< 6 = 64 * q
      rw [Nat.shiftLeft_eq]; omega
    constructor
    · intro h i hi
      cases hb : allBlk (Nat.shiftLeft q 6) f 64 <;> rw [hb] at h
      · exact absurd h Bool.false_ne_true
      · by_cases hiq : i < 64 * q
        · exact (allN_blocks q).1 h i hiq
        · have := (allBlk_iff.1 hb) (i - 64 * q) (by omega)
          rwa [hs, show 64 * q + (i - 64 * q) = i by omega] at this
    · intro h
      have hb : allBlk (Nat.shiftLeft q 6) f 64 = true :=
        allBlk_iff.2 fun l hl => h _ (by rw [hs]; omega)
      rw [hb]
      exact (allN_blocks q).2 fun i hi => h i (by omega)

private theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  have hq : Nat.shiftRight n 6 = n / 64 := by
    change n >>> 6 = n / 64
    rw [Nat.shiftRight_eq_div_pow]
  have hr : Nat.land n 63 = n % 64 := Nat.and_two_pow_sub_one_eq_mod n 6
  have hs : Nat.shiftLeft (n / 64) 6 = 64 * (n / 64) := by
    change (n / 64) <<< 6 = 64 * (n / 64)
    rw [Nat.shiftLeft_eq]; omega
  show Bool.rec false _ (allBlk (Nat.shiftLeft (Nat.shiftRight n 6) 6) f (Nat.land n 63)) = true ↔ _
  rw [hq, hr, hs]
  constructor
  · intro h i hi
    cases hb : allBlk (64 * (n / 64)) f (n % 64) <;> rw [hb] at h
    · exact absurd h Bool.false_ne_true
    · by_cases hiq : i < 64 * (n / 64)
      · exact (allN_blocks (f := f) (n / 64)).1 h i hiq
      · have := (allBlk_iff.1 hb) (i - 64 * (n / 64)) (by omega)
        rwa [show 64 * (n / 64) + (i - 64 * (n / 64)) = i by omega] at this
  · intro h
    have hb : allBlk (64 * (n / 64)) f (n % 64) = true :=
      allBlk_iff.2 fun l hl => h _ (by omega)
    rw [hb]
    exact (allN_blocks (n / 64)).2 fun i hi => h i (by omega)

theorem cnt_ok : allN 17813 (fun b => Nat.blt (HNX.CNT b) 1048576) = true := by quickRfl

theorem cnt_lt : ∀ b < 17813, HNX.CNT b < 1048576 := fun b hb =>
  Nat.le_of_ble_eq_true ((allN_iff.1 cnt_ok) b hb)

theorem hns_bind : hnxBindK TX (hnsOrbitData ()) = true :=
  hnxBindK_of HNXBind.bindS HNXBind.bindV HNXBind.bindA HNXBind.bindB HNXBind.bindP HNXBind.bindL

theorem hns_orbit : hnsData.orbit () = (hnsOrbitData ()).toOrbit := hnsData_orbit

theorem hns_orbitCert : orbitCertChecks (hnsData.orbit ()) = true :=
  orbitCert_sound_of_cnt hns_checks cnt_lt hns_orbit hns_bind ⟨rfl, rfl⟩ validA validB oneId ordA
    ordB rfl checkPts_lt basis_ok

end CertificateChecks.KernelSporSch.HNXCert

end

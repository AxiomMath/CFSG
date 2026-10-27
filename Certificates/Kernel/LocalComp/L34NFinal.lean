module

public import Certificates.Kernel.LocalComp.L34NChk
public import Certificates.Kernel.LocalComp.L34NChk0
public import Certificates.Kernel.LocalComp.L34NChk1
public import Certificates.Kernel.LocalComp.L34NChk2
public import Certificates.Kernel.LocalComp.L34NChk3
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Certificates.Kernel.L34NormSound
public import Certificates.Data.CFSGNative.PSL3Four.L34Cent
public import Certificates.Data.L34OuterGen
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.L34KSnd.Tab

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelLC.L34N.l34nAll CertificateChecks.KernelLC.L34N.l34n 180

namespace CertificateChecks.KernelLC.L34N

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Norm
open CertificateChecks.KernelLC.L34Cert CFSG.PSL3Four.Native
open CFSG.KC.HeAutK (cntR)
open CFSG.KLie.CT (andB)

@[expose] noncomputable def nfix (X : Tab) : Nat := cntR (fun p => X[p]! == p) 0 42

theorem listed : Listed (code (pidn 42 6)) J 0 241920 0 7755 := by
  have h := slices_listed (f := code (pidn 42 6)) (J := J) (L := 1344) (C := C) 180
    fun s hs => by
      have h1 := l34nAll s hs
      unfold l34n at h1
      rwa [strictB_eq] at h1
  obtain ⟨h0, h1⟩ := andT kEnds
  rw [Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1] at h
  exact h

theorem code_eq (e k : Nat) :
    code e k = normCode 42 6 9 AP (K 0) (K 1) (K 2) 1 27 e (L34R.T k) := rfl

theorem code_lt {k : Nat} (hk : k < 241920) : code (pidn 42 6) k < 32 := by
  by_cases h : code (pidn 42 6) k = 0
  · omega
  · exact (listed.mem k (Nat.zero_le _) hk h).1

theorem listed_iff {B : Nat → Bool} (hB : B 0 = false) {i : Nat} (hi : i < 241920) :
    B (code (pidn 42 6) i) = true ↔ ∃ q < 7755, J q / 32 = i ∧ B (J q % 32) = true := by
  constructor
  · intro h
    have hne : code (pidn 42 6) i ≠ 0 := fun e => by rw [e, hB] at h; exact Bool.noConfusion h
    obtain ⟨h32, q, -, hq, hJ⟩ := listed.mem i (Nat.zero_le _) hi hne
    refine ⟨q, hq, by omega, ?_⟩
    rwa [show J q % 32 = code (pidn 42 6) i by omega]
  · rintro ⟨q, hq, hqi, h⟩
    obtain ⟨k, -, hk, -, h32, hJ⟩ := listed.get q (Nat.zero_le _) hq
    have hki : k = i := by omega
    subst hki
    rwa [show J q % 32 = code (pidn 42 6) k by omega] at h

theorem canonT {i : Nat} (hi : i < 241920) : canonK 42 6 (mask 6) (42 * 6) (L34R.T i) = true :=
  pinR.canon i hi

theorem canonK' {j : Nat} (hj : j < 12) : canonK 42 6 (mask 6) (42 * 6) (K j) = true :=
  CFSG.KS.Raw.Orb.allN_iff.1 kCanonK j hj

theorem K_tabs : unpack 42 6 (K 0) = a₀T ∧ unpack 42 6 (K 1) = b₀T ∧
    unpack 42 6 (K 2) = Certificates.L34OuterGen.t3aT ∧
    ∀ j < 9, unpack 42 6 (AP j) = (e9T ())[j]! := by
  decide +kernel

theorem canonAP {j : Nat} (hj : j < 9) : canonK 42 6 (mask 6) (42 * 6) (AP j) = true :=
  canonK' (j := 3 + j) (by omega)

theorem normA_iff {i : Nat} (hi : i < 241920) :
    ((∃ j < 9, comp 42 (unpack 42 6 (L34R.T i)) a₀T =
        comp 42 (e9T ())[j]! (unpack 42 6 (L34R.T i))) ∧
      (∃ j < 9, comp 42 (unpack 42 6 (L34R.T i)) b₀T =
        comp 42 (e9T ())[j]! (unpack 42 6 (L34R.T i)))) ↔
      ∃ q < 7755, J q / 32 = i ∧ J q % 2 = 1 := by
  have h := listed_iff (B := fun v => Nat.beq (v % 2) 1) rfl hi
  simp only [Nat.beq_eq] at h
  have e : ∀ q, J q % 32 % 2 = J q % 2 := fun q => by omega
  simp only [e] at h
  rw [← h, code_eq, (normCode_bits ..).1, bv_eq_one, CFSG.KC.L34KSnd.andB_iff,
    inPts_iff (canonT hi) (canonK' (j := 0) (by decide)) (fun j hj => canonAP hj),
    inPts_iff (canonT hi) (canonK' (j := 1) (by decide)) (fun j hj => canonAP hj), K_tabs.1,
    K_tabs.2.1]
  refine and_congr (exists_congr fun j => and_congr_right fun hj => ?_)
    (exists_congr fun j => and_congr_right fun hj => ?_) <;> rw [K_tabs.2.2.2 j hj]

theorem centZ_iff {i : Nat} (hi : i < 241920) :
    comp 42 (unpack 42 6 (L34R.T i)) Certificates.L34OuterGen.t3aT =
        comp 42 Certificates.L34OuterGen.t3aT (unpack 42 6 (L34R.T i)) ↔
      ∃ q < 7755, J q / 32 = i ∧ J q / 2 % 2 = 1 := by
  have h := listed_iff (B := fun v => Nat.beq (v / 2 % 2) 1) rfl hi
  simp only [Nat.beq_eq] at h
  have e : ∀ q, J q % 32 / 2 % 2 = J q / 2 % 2 := fun q => by omega
  simp only [e] at h
  rw [← h, code_eq, (normCode_bits ..).2.1, bv_eq_one,
    CFSG.KC.L34KSnd.commPt_iff (canonT hi) (canonK' (j := 2) (by decide)),
    K_tabs.2.2.1]

theorem stabT_iff {i : Nat} (hi : i < 241920) :
    (((unpack 42 6 (L34R.T i))[1]! = 1 ∨ (unpack 42 6 (L34R.T i))[1]! = 27) ∧
      ((unpack 42 6 (L34R.T i))[27]! = 1 ∨ (unpack 42 6 (L34R.T i))[27]! = 27)) ↔
      ∃ q < 7755, J q / 32 = i ∧ J q / 4 % 2 = 1 := by
  have h := listed_iff (B := fun v => Nat.beq (v / 4 % 2) 1) rfl hi
  simp only [Nat.beq_eq] at h
  have e : ∀ q, J q % 32 / 4 % 2 = J q / 4 % 2 := fun q => by omega
  simp only [e] at h
  rw [← h, code_eq, (normCode_bits ..).2.2.1, bv_eq_one, pairPt_iff (n := 42) (by decide) (by decide)]

theorem o3_iff {i : Nat} (hi : i < 241920) :
    o3Pt 42 6 (pidn 42 6) (L34R.T i) = true ↔ unpack 42 6 (L34R.T i) ≠ idTab 42 ∧
      comp 42 (unpack 42 6 (L34R.T i))
        (comp 42 (unpack 42 6 (L34R.T i)) (unpack 42 6 (L34R.T i))) = idTab 42 :=
  o3Pt_iff (canonT hi)

theorem nfix_of_order3 {i : Nat} (hi : i < 241920) (h1 : unpack 42 6 (L34R.T i) ≠ idTab 42)
    (h3 : comp 42 (unpack 42 6 (L34R.T i))
      (comp 42 (unpack 42 6 (L34R.T i)) (unpack 42 6 (L34R.T i))) = idTab 42) :
    nfix (unpack 42 6 (L34R.T i)) = 0 ∨ nfix (unpack 42 6 (L34R.T i)) = 6 ∨
      nfix (unpack 42 6 (L34R.T i)) = 12 := by
  have ho := (o3_iff hi).2 ⟨h1, h3⟩
  have hc := code_lt hi
  have hb : code (pidn 42 6) i / 8 = o3Cat 42 6 (pidn 42 6) (L34R.T i) := by
    rw [code_eq]
    exact (normCode_bits ..).2.2.2
  have hs := o3Cat_spec 42 6 (pidn 42 6) (L34R.T i)
  have hcat : o3Cat 42 6 (pidn 42 6) (L34R.T i) < 4 := by omega
  unfold nfix
  rw [← nfixK_eq]
  have h0 : o3Cat 42 6 (pidn 42 6) (L34R.T i) ≠ 0 := fun e => by
    rw [hs.1.1 e] at ho
    exact Bool.noConfusion ho
  rcases (by omega : o3Cat 42 6 (pidn 42 6) (L34R.T i) = 1 ∨
      o3Cat 42 6 (pidn 42 6) (L34R.T i) = 2 ∨ o3Cat 42 6 (pidn 42 6) (L34R.T i) = 3) with
    e | e | e
  · exact Or.inl (hs.2.1.1 e).2
  · exact Or.inr (Or.inl (hs.2.2.1.1 e).2)
  · exact Or.inr (Or.inr (hs.2.2.2.1 e).2)

theorem order3_iff {i c : Nat} (hi : i < 241920) (hc : c < 3) :
    (unpack 42 6 (L34R.T i) ≠ idTab 42 ∧
      comp 42 (unpack 42 6 (L34R.T i))
        (comp 42 (unpack 42 6 (L34R.T i)) (unpack 42 6 (L34R.T i))) = idTab 42 ∧
      nfix (unpack 42 6 (L34R.T i)) = 6 * c) ↔
      ∃ q < 7755, J q / 32 = i ∧ J q % 32 / 8 = c + 1 := by
  have h := listed_iff (B := fun v => Nat.beq (v / 8) (c + 1)) (by
    change Nat.beq 0 (c + 1) = false
    exact beq_false (by omega)) hi
  simp only [Nat.beq_eq] at h
  rw [← h, code_eq, (normCode_bits ..).2.2.2, ← and_assoc, ← o3_iff hi]
  unfold nfix
  rw [← nfixK_eq]
  have hs := o3Cat_spec 42 6 (pidn 42 6) (L34R.T i)
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  · exact hs.2.1.symm
  · exact hs.2.2.1.symm
  · exact hs.2.2.2.symm

theorem count_eq {B : Nat → Bool} (hB : B 0 = false) :
    cntR (fun k => B (code (pidn 42 6) k)) 0 241920 = cntR (fun q => B (J q % 32)) 0 7755 :=
  listed.cnt B hB

end CertificateChecks.KernelLC.L34N

end

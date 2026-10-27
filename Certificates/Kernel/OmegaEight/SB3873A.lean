
module

public import Certificates.Kernel.OmegaEight.SB3873
public import Certificates.Kernel.OmegaEight.SB3872K
public import Certificates.Kernel.OmegaEight.FHom
public import Certificates.Kernel.OmegaEight.ExtChi

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.ExtChi CertificateChecks.KernelO8.FHom

@[expose] def t1KillC (k m z : ℕ) (n5 : Bool) : Bool :=
  groupKillC (t1Mul (sFTab k m) z) (t1Inv (sFTab k m) z) t1Gens 131072 8 n5 (chiB 10)
    (chiS 131072) sMarked (t1Cls k m z)

@[expose] noncomputable def MK (k m z : ℕ) : ℕ → ℕ → ℕ := extMul 65536 mulK (FK k m) z

@[expose] noncomputable def IK (k m z : ℕ) : ℕ → ℕ := extInv 65536 mulK invK (FK k m) z

@[expose] noncomputable def conjOK (k m z a n : ℕ) : Bool :=
  (List.range' a n).all fun y => mulK z y == mulK (FK k m (FK k m y)) z

@[expose] noncomputable def chiWOK (k m : ℕ) : Bool :=
  (List.range 128).all fun e => decide (WK k m e < 65536) && (chiS 65536)[WK k m e]! == e.testBit 1

@[expose] noncomputable def chiLOK (k : ℕ) : Bool :=
  (List.range 512).all fun a => decide (LK k a < 65536) && !(chiS 65536)[LK k a]!

theorem mulK_lt (c d : ℕ) : mulK c d < 65536 := sMul_eqK ▸ sMul_lt c d

noncomputable abbrev ΦK : CodeIso SModel 65536 mulK := sMul_eqK ▸ SModel.codeIso

theorem mulK_zero : mulK 0 0 = 0 := sMul_eqK ▸ sMul_zero_zero

theorem invOK_K : invOK mulK invK 65536 = true := kill_inv

theorem genK : Gen mulK sGens 65536 := sMul_eqK ▸ sGen

theorem chi_homK : ∀ a < 65536, ∀ c < 65536,
    (chiS 65536)[mulK a c]! = ((chiS 65536)[a]! ^^ (chiS 65536)[c]!) := fun _ ha _ hc =>
  chi_mul ΦK mulK_zero invOK_K sGens_lt genK kill_chi ha hc

theorem t1KillC_of {k m z : ℕ} {n5 : Bool} (hw : wOK k m = true) (hl : lOK k = true)
    (hconj : conjOK k m z 0 65536 = true) (hz : z < 65536) (hzχ : (chiS 65536)[z]! = false)
    (hcw : chiWOK k m = true) (hcl : chiLOK k = true)
    (hcls : kClassOK (MK k m z) (IK k m z) t1Gens 131072 (t1Cls k m z) = true)
    (hts : ∀ p ∈ sMarked, killAtC (MK k m z) (IK k m z) t1Gens 131072 (kInv (MK k m z) 131072)
      (kOrd4 (MK k m z) 131072) (kRepsC (t1Cls k m z) 8) 8 (chiS 131072) n5 p.1 p.2 = true) :
    t1KillC k m z n5 = true := by
  have hF : (fun c => (sFTab k m)[c]!) = FK k m := sFTab_eq hw hl
  have hFlt : ∀ a < 65536, FK k m a < 65536 := fun a _ => mulK_lt _ _
  have hconj' : ∀ y < 65536, mulK z y = mulK (FK k m (FK k m y)) z := by
    intro y hy
    unfold conjOK at hconj
    rw [List.all_eq_true] at hconj
    exact beq_iff_eq.1 (hconj y (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩))
  have hinv1 : invOK (MK k m z) (IK k m z) 131072 = true :=
    invOK_ext_of_conj ΦK invOK_K hFlt hz hconj'
  have hcw' : ∀ e < 128, WK k m e < 65536 ∧ (chiS 65536)[WK k m e]! = e.testBit 1 := by
    unfold chiWOK at hcw
    rw [List.all_eq_true] at hcw
    intro e he
    have := hcw e (List.mem_range.2 he)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this
  have hcl' : ∀ a < 512, LK k a < 65536 ∧ (chiS 65536)[LK k a]! = false := by
    unfold chiLOK at hcl
    rw [List.all_eq_true] at hcl
    intro a ha
    have := hcl a (List.mem_range.2 ha)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
    exact this
  have hchi1 : chiOK (MK k m z) t1Gens 131072 (chiB 10) (chiS 131072) = true := by
    refine chiOK_ext (chiS 65536) (chiS 131072) (chiS_size _) (fun c hc => ?_)
      (fun a c _ _ => mulK_lt a c) (fun a c ha hc => chi_homK a ha c hc)
      (by rw [chiS_get]; decide +kernel) (fun j hj => ?_)
      (fun d hd => ⟨mulK_lt _ _, ?_⟩) ⟨hz, hzχ⟩ (by decide)
    · rw [chiS_get, chiS_get, Nat.mod_mod_of_dvd _ (by norm_num : 65536 ∣ 65536)]
      simp only [Nat.mod_lt _ (by norm_num : 0 < 65536), decide_true, Bool.true_and,
        show c < 131072 from hc, decide_true]
    · have hj' : j < 9 := hj
      rw [chiS_get]
      interval_cases j <;> decide +kernel
    · obtain ⟨he, ha⟩ := nf_lt hd
      rw [FK, chi_homK _ (hcw' _ he).1 _ (hcl' _ ha).1, (hcw' _ he).2, (hcl' _ ha).2,
        Bool.xor_false, chiS_get, Nat.mod_eq_of_lt hd]
      simp [hd]
  unfold t1KillC groupKillC t1Mul t1Inv
  rw [hF, sMul_eqK, sInv_eqK]
  simp only [Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨hinv1, hcls⟩, hchi1⟩, hts⟩

end CertificateChecks.KernelO8.SB3873

end

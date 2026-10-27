module

public import Certificates.Kernel.TwoHSLe4.NormS
public import Certificates.Kernel.TwoHSLe4.NormPB
public import Certificates.Kernel.TwoHSLe4.NormQB
public import Certificates.Kernel.TwoHSLe4.NormQSound
public import Certificates.Kernel.TwoHSLe4.S9Glue

public section

namespace CertificateChecks.KernelTwoHSLe4.Norm

open CFSG.EvenSporadicStandard.TwoHS

theorem SL_eq : SL = shatR := (S9.shatR_eq).symm

theorem compatS_eq (b : R4) : compatS b = compatR b := by
  unfold compatS compatR
  rw [SL_eq]

theorem normB2S_eq (b : R4) : normB2S b = NormB2 b := by
  unfold normB2S NormB2 shat2R
  rw [SL_eq]

theorem nCaseS_eq (T : List (R4 × List R4)) (a : R4) : nCaseS T a = nCaseB T a := by
  unfold nCaseS nCaseB norm2B
  rw [SL_eq]

theorem candR_eq : candR = candData.map S9.rl := by
  simp [candR, candList, Function.comp_def, S9.toR4_matOfList]

theorem candK_eq : NormP.candK = candR := by
  rw [candR_eq]
  exact eq_of_beq NormP.candK_ok

theorem lifts_all : ∀ b ∈ svL, liftsOK b = true := by
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
  have hi' : i < 32 := List.mem_range.1 hi
  interval_cases i
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb0
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb1
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb2
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb3
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb4
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb5
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb6
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb7
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb8
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb9
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb10
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb11
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb12
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb13
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb14
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb15
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb16
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb17
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb18
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb19
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb20
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb21
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb22
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb23
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb24
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb25
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb26
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb27
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb28
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb29
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb30
  · exact NormP.liftsOK_of_chkN candK_eq NormP.nb31

theorem mem_nvL {b : R4} (hb : b.wf2) (hn : NormB2 b = true) : b ∈ nvL :=
  NormP.mem_nvL_of_chkAN NormP.na hb (by rw [normB2S_eq]; exact hn)

theorem normComplete : NormComplete := by
  intro A ⟨A', hAA', hA'A⟩ hN1 hN2
  have hwa : (toR4 A).wf := wf_toR4 A
  have hinv : rmul (toR4 A) (toR4 A') = R4.one := by
    apply ofR4_inj (wf_rmul _ _) wf_one
    rw [ofR4_rmul, ofR4_toR4, ofR4_toR4, hAA', ofR4_one]
  have hn1 := norm1R_of_norm1 hN1
  have hn2 := norm2R_of_norm2 hN2
  have hn1' := norm1R_of_norm1 (norm1_inv hAA' hA'A hN2)
  have hn2' := norm2R_of_norm2 (norm2_inv hAA' hA'A hN1)
  have hbn : (toR4 A).mod2 ∈ nvL := mem_nvL (mod2_wf2 _) (normB2_of_norm hn1 hn2)
  have hbn' : (toR4 A').mod2 ∈ nvL := mem_nvL (mod2_wf2 _) (normB2_of_norm hn1' hn2')
  have hb : (toR4 A).mod2 ∈ svL := by
    have h := List.all_eq_true.1 sv_ok _ hbn
    have hany : (nvL.any fun b' => (rmul (toR4 A).mod2 b').mod2 == R4.one) = true := by
      rw [List.any_eq_true]
      refine ⟨(toR4 A').mod2, hbn', ?_⟩
      rw [beq_iff_eq, ← mod2_rmul, hinv, mod2_one]
    rw [hany] at h
    simpa using h
  have hl := lifts_all _ hb
  unfold liftsOK at hl
  have key := List.all_eq_true.1 hl _ (mem_bitsN (hi_wf2 hwa))
  rw [nCaseS_eq, compatS_eq, lift2_mod2_hi] at key
  refine concl_of_raw ?_
  rcases nCaseB_sound key with h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd ⟨norm1T_of_norm1R hn1, hn2⟩ h1
  · exact Or.inr h1

end CertificateChecks.KernelTwoHSLe4.Norm

end

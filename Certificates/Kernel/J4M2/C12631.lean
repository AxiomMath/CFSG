module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77BridgeData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77BridgeData
public import Certificates.Kernel.J4M2.C12631Checks
public import Certificates.Kernel.J4M2.C12607
public import Certificates.Kernel.J4M2.C4200
public import CFSG.Certificates.Kernel.J4Q.VOrbBFS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Br

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.KS.SporSch.J4E CFSG.Sporadic.J4Schreier
  CFSG.Sporadic.J4.Native CertificateChecks.KernelSporSch.J4E7 CertificateChecks.KernelJ4Gam
  CFSG.AGLEmbeddingD2.Wilson.NormalizerAction CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77

theorem v2N_eq_toNat (a : V2) : v2N a = a.toNat := by
  unfold v2N V2.toNat
  rw [Nat.lor_eq, Nat.shiftLeft_eq', Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt (UInt64.toNat_lt a.lo) a.hi.toNat,
    Nat.shiftLeft_eq]
  omega

theorem toNat_enc {M : Array V2} (hM : WfA M) :
    WfN (M.map V2.toNat) ∧ encN (M.map V2.toNat) = encR M := by
  have hw : ∀ i (hi : i < M.size), M[i].wf = true := Array.all_eq_true.1 hM.2
  refine ⟨⟨by rw [Array.size_map, hM.1], fun i hi => ?_⟩, ?_⟩
  · have hi' : i < M.size := by rw [hM.1]; exact hi
    rw [CertificateChecks.KernelJ4M2.get!_map _ _ hi', getElem!_pos M i hi', ← v2N_eq_toNat]
    exact v2N_lt112 (hw i hi')
  · unfold encN encR
    refine CertificateChecks.KernelJ4M2.foldr_congr_mem _ _ fun i hi x => ?_
    have hi' : i < M.size := by rw [hM.1]; exact List.mem_range.1 hi
    have e1 : (M.map V2.toNat).getD i 0 = M[i].toNat := by
      simp [Array.getD_eq_getD_getElem?, hi']
    have e2 : M.getD i V2.zero = M[i] := by simp [Array.getD_eq_getD_getElem?, hi']
    rw [e1, e2, v2N_eq_toNat]

theorem natToV2_enc {X : Array Nat} (hX : WfN X) :
    WfA (X.map CFSG.Quasithin.J4M2.natToV2) ∧ encR (X.map CFSG.Quasithin.J4M2.natToV2) = encN X := by
  have hlt : ∀ i (hi : i < X.size), X[i] < 2 ^ 112 := fun i hi => by
    have h := hX.2 i (by rw [← hX.1]; exact hi)
    rwa [getElem!_pos X i hi] at h
  refine ⟨⟨by rw [Array.size_map, hX.1], ?_⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    rw [Array.getElem_map]
    have hi' : i < X.size := by simpa using hi
    exact wf_of_lt (by rw [CertificateChecks.KernelJ4M2.v2N_natToV2 (hlt i hi')]; exact hlt i hi')
  · unfold encN encR
    refine CertificateChecks.KernelJ4M2.foldr_congr_mem _ _ fun i hi x => ?_
    have hi' : i < X.size := by rw [hX.1]; exact List.mem_range.1 hi
    have e1 : (X.map CFSG.Quasithin.J4M2.natToV2).getD i V2.zero =
        CFSG.Quasithin.J4M2.natToV2 X[i] := by
      simp [Array.getD_eq_getD_getElem?, hi']
    have e2 : X.getD i 0 = X[i] := by simp [Array.getD_eq_getD_getElem?, hi']
    rw [e1, e2, CertificateChecks.KernelJ4M2.v2N_natToV2 (hlt i hi')]

theorem hz : WfN zRowsN ∧ encN zRowsN = ZM :=
  ⟨(toNat_enc CertificateChecks.KernelJ4M2.zM_enc.1).1,
    (toNat_enc CertificateChecks.KernelJ4M2.zM_enc.1).2.trans CertificateChecks.KernelJ4M2.zM_enc.2⟩

theorem eZ : Z0 = ZM := Nat.eq_of_beq_eq_true z0_chk

theorem zR_eq : zRowsN = gamZ0 :=
  enc_inj hz.1 (wfN_of rows.1) (hz.2.trans eZ.symm)

theorem gam_eq : gamP = gamGP := by
  unfold gamP gamGP zPN gamZ0P
  rw [zR_eq]
  rfl

theorem pCA : PairOK cAP GA.1 GA.2 := by
  have h := pCj pC1
  rw [eqP_eq ca_chk] at h
  have e : cAP = gamConjP gamC1P := by
    unfold cAP gamConjP
    rw [gam_eq]
    rfl
  rw [e]
  exact h

theorem pCB : PairOK cBP GB.1 GB.2 := by
  have h := pCj hH2
  rw [eqP_eq cb_chk] at h
  have e : cBP = gamConjP H2n := by
    unfold cBP gamConjP
    rw [gam_eq]
  rw [e]
  exact h

theorem pCZ : PairOK cZP GZ.1 GZ.2 := by
  have h := pCj hQZ
  rw [eqP_eq cz_chk] at h
  have e : cZP = gamConjP QZn := by
    unfold cZP gamConjP
    rw [gam_eq]
  rw [e]
  exact h

theorem actOK_of {X π : Array Nat} {g : Nat} (hX : WfN X ∧ encN X = g)
    (h : actAll g (fun i => π.getD i 0) = true) : actOK X π = true := by
  have hA := natToV2_enc hX.1
  unfold actOK
  rw [List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  have h1 := List.all_eq_true.1 h i hi
  unfold actK at h1
  obtain ⟨hlt, heq⟩ := andB_iff.1 h1
  have hl : π.getD i 0 < 77 := lt_of_blt hlt
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hl, ?_⟩
  have f := CertificateChecks.KernelJ4M2.frApply_enc ⟨hA.1, hA.2.trans hX.2⟩ hl
  apply CFSG.KC.J4Q.VOrbBFS.v2N_inj
  rw [f.1, (CertificateChecks.KernelJ4M2.vecs_wf hi').2]
  exact Nat.eq_of_beq_eq_true heq

theorem commOK_of {X : Array Nat} {g : Nat} (hX : WfN X ∧ encN X = g)
    (h : Nat.beq (mulJ c rm g ZM) (mulJ c rm ZM g) = true) : commOK X = true := by
  rw [← hX.2, ← hz.2] at h
  exact eq_sound hK hX.1 hz.1 hz.1 hX.1 h

theorem bridgeCheck_ok : bridgeCheck = true := by
  have h1 : (CFSG.Quasithin.J4M2.zM.size == 112) = true := by
    rw [CertificateChecks.KernelJ4M2.zM_enc.1.1]
    rfl
  have hzz := zz_chk
  rw [eZ, ← hz.2] at hzz
  unfold bridgeCheck
  rw [h1, eq_one_sound hK hz.1 hz.1 hzz, actOK_of pCA.1 ac_a, actOK_of pCB.1 ac_b,
    actOK_of pCZ.1 ac_z, commOK_of pCA.1 cm_a, commOK_of pCB.1 cm_b, commOK_of pCZ.1 cm_z]
  rfl

open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77 in
theorem c12631 : bridgeCheck = true := bridgeCheck_ok

end CertificateChecks.KernelJ4Br

end

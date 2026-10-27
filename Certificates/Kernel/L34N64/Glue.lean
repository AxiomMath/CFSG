module

public import Certificates.Kernel.L34M64.Glue
public import Certificates.Kernel.L34N64.Check

public section

namespace CertificateChecks.KernelL34N64

open CFSG.Fischer Matrix CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H13.Ch9.L34N
  CFSG.Quasithin.H13.Ch9.L34M CFSG.Quasithin.H.Mathieu CFSG.KC.L34N64 CFSG.KC.L34M64
  CFSG.KD.L34M64 CertificateChecks.KernelL34M64

theorem st64_eq :
    st64 = stack4 64 (X12.getD 1 []) (X12.getD 2 []) (X23.getD 1 []) (X23.getD 2 []) := by
  funext w
  rw [st64, tabX12_eq, tabX23_eq]

theorem ker64_eq : ker64 = kerL := by
  rw [ker64, st64_eq]
  exact eq_of_beq ch7252ker

theorem entC_lt (A : Matrix (Fin 8) (Fin 8) F4) (p : ℕ) : entC A p < 4 := by
  unfold entC
  split
  · exact (A _ _).code.isLt
  · norm_num

theorem rep_pw0 : RepP pw0 (adM w0 w0) := by
  intro i j
  have hk : 8 * i.val + j.val < 64 := by omega
  have e : (⟨8 * i.val + j.val, hk⟩ : Fin 64) = pos8 i j := rfl
  rw [pw0, ln_pk64 (entC_lt _), entC, dif_pos hk, e, row8_pos8, col8_pos8]

theorem adGL_w0GL : adGL w0GL = adM w0 w0 := by
  rw [adGL, coe_w0GL, coe_w0GL_inv]

theorem w0img : actM w0C64 512 = actP pw0 512 := by
  rw [w0C64, colsN64_eq (rep8_codes8 _), actM_matOf (xorLin_actH8 _) 64 512 (by norm_num),
    adGL_w0GL, actP_eq rep_pw0]

theorem orb64_eq : orb64 = orbL := by
  rw [orb64, tabU64_eqD, w0img]
  exact eq_of_beq ch7252orb

theorem echComb_eq : echComb orbL = echL := eq_of_beq ch7252ech

theorem chkN64_eq : chkN64 = chkNL ker64 orb64 (echComb orb64) st64 (tabX12_64.getD 1 [])
    (tabX12_64.getD 2 []) (tabX23_64.getD 1 []) (tabX23_64.getD 2 []) := rfl

theorem chkN64_true : chkN64 = true := by
  rw [chkN64_eq, ker64_eq, orb64_eq, echComb_eq, st64_eq, tabX12_eq, tabX23_eq]
  exact ch7252rest

end CertificateChecks.KernelL34N64
